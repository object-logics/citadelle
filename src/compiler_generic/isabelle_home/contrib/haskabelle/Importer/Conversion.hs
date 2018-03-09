{-| Author: Tobias C. Rittweiler, TU Muenchen

Internal importer main interfaces.
-}

module Importer.Conversion (importFiles, importProject) where

import Importer.Library

import qualified Data.Char as Char
import qualified Data.Data as D
import qualified Data.Generics.Aliases as G
import qualified Data.List as List
import Text.PrettyPrint (render)
import qualified Text.Printf as Printf

import System.FilePath
import System.Directory
import System.IO

import Importer.Adapt (Adaption (..), AdaptionTable, readAdapt, preludeFile)
import Importer.Configuration
import Importer.Convert
import Importer.Printer (pprint)

import qualified Importer.Ident_Env as Ident_Env (GlobalE)
import qualified Importer.Isa as Isa (Module (..), ThyName (..))
import qualified Importer.Hsx as Hsx


importProject :: Config -> FilePath -> IO ()
importProject config adaptDir = do
  adapt <- readAdapt adaptDir
  runConversion config (convertFiles adapt)

importFiles :: FilePath -> [FilePath] -> Maybe FilePath -> Bool -> IO ()
importFiles adaptDir files out exportCode
  = importProject (defaultConfig files out defaultCustomisations exportCode) adaptDir

convertFiles :: Adaption -> Conversion ()
convertFiles adapt = do

  inFiles <- getInputFilesRecursively
  outDir <- getOutputDir
  exportCode <- getExportCode
  custs <- getCustomisations
  
  exists <- liftIO $ mapM doesDirectoryExist outDir
  when (case exists of Just False -> True ; _ -> False) $ liftIO $ maybe (return ()) createDirectory outDir

  units <- parseHskFiles (filter Hsx.isHaskellSourceFile inFiles)
  let (adaptTable : _, convertedUnits) = map_split (convertHskUnit custs exportCode adapt) units

  liftIO $ maybe (return ()) (\outDir -> copyFile (preludeFile adapt) (combine outDir (takeFileName (preludeFile adapt)))) outDir
  sequence_ (map (writeIsaUnit adaptTable (reservedKeywords adapt)) convertedUnits)
  liftIO $ case outDir of Nothing -> putStrLn $ gshow (List.nubBy (let f (Isa.Module t _ _ _) = t in \m1 m2 -> f m1 == f m2)
                                                        $ concatMap (\(IsaUnit l _ _) -> l) convertedUnits)
                          _       -> return ()


writeIsaUnit :: AdaptionTable -> [String] -> IsaUnit -> Conversion ()
writeIsaUnit adapt reserved (IsaUnit thys custThys env)
    = mapM_ writeCustomTheory custThys >>
      mapM_ (writeTheory adapt reserved env) thys

writeCustomTheory :: CustomTheory -> Conversion ()
writeCustomTheory cust = 
    do let src = getCustomTheoryPath cust
           filename = takeFileName src
       getOutputDirMaybe (\outDir -> liftIO $ copyFile src (combine outDir filename))

writeTheory :: AdaptionTable -> [String] -> Ident_Env.GlobalE -> Isa.Module -> Conversion ()
writeTheory adapt reserved env thy @ (Isa.Module (Isa.ThyName thyname) _ _ _) = do
  let content = render (pprint adapt reserved env thy)
  let dstName = content `seq` map (\c -> if c == '.' then '_' else c) thyname ++ ".thy"
  getOutputDirMaybe (\outLoc -> do
    let dstPath = combine outLoc dstName
    liftIO $ hPutStr stderr $ "writing " ++ dstName ++ "...\n"
    liftIO $ writeFile dstPath content)

getOutputDirMaybe f = getOutputDir >>= maybe (return ()) f

--

char_escape c =    c >= '\b' && c <= '\n'
                || c == '\r'
                || c == '"'

char c =    char_escape c
         || c >= ' ' && c <= '~' && (c /= '\\' && c /= '<' {- the escaping of string comments for future ML parsing to succeed -})

type SS' = String
type SS = SS' -> SS'

monad_String = showString
monad_Char = showChar
monad_Drop = drop

gshows :: D.Data a => a -> SS
gshows = render `G.extQ` (render_bool :: Bool -> SS)
                `G.extQ` (render_string :: String -> SS)
                `G.extQ` (render_char :: Char -> SS)
                `G.extQ` (render_int :: Int -> SS)
                `G.extQ` (render_integer :: Integer -> SS) where
  render_bool b = monad_String $ if b then "true" else "false"
  render_string s = if all char s then shows s
                    else monad_String $ "\"" ++ concatMap (\c -> if char c && not (char_escape c) then [c]
                                                                 else Printf.printf "\\%03d" (Char.ord c)) s ++ "\""
  render_char c = monad_Char '#' . render_string [c]
  render_int i = if i < 0 then monad_Char '~' . shows (-i) else shows i
  render_integer = render_int
  render t
    | isTuple = commaSlots' '(' "," ')'
    | isListEmpty = monad_String "[]"
    | isList = commaSlots '(' "::" ')'
    | isOption = case D.showConstr . D.toConstr $ t of
                   "Just" -> monad_String "SOME" . commaSlots '(' "," ')'
                   "Nothing" -> monad_String "NONE"
    | isSingleConst = constructor

    | otherwise = constructor
                . commaSlots '(' "," ')'

    where constructor = monad_String . D.showConstr . D.toConstr $ t

          build s = foldr (.) id . D.gmapQ ((monad_String s .) . gshows) $ t
          commaSlots c1 s c2 = monad_Char c1 . monad_Drop (length s) . build s . monad_Char c2
          commaSlots' c1 s c2 = -- this particular arrangement of tuples is following the ordering chosen in Haskabelle
            case D.gmapQ gshows t of x : xs -> foldl (\x1 x2 -> monad_Char c1 . x1 . monad_String s . x2 . monad_Char c2) x xs
          filt s = filter (not . flip elem s) (constructor "")

          isTuple = all (==',') (filt "()")
          isListEmpty = null (filt "[]")
          isList = constructor "" == "(:)"
          isOption = let c = constructor "" in c == "Just" || c == "Nothing"
          isSingleConst = null (D.gmapQ (\_ -> ()) t)

gshow f = gshows f ""
