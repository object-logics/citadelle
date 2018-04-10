{-| Author: Tobias C. Rittweiler, TU Muenchen

Internal importer main interfaces.
-}

module Importer.Conversion (importFiles, importProject) where

import Importer.Library

import qualified Data.List as List
import Text.PrettyPrint (render)

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
import qualified Importer.Conversion.SML as SML


importProject :: Config -> FilePath -> [String] -> IO ()
importProject config adaptDir hsk_cts = do
  adapt <- readAdapt adaptDir
  runConversion config (convertFiles adapt hsk_cts)

importFiles :: [FilePath] -> Maybe FilePath -> Bool -> Bool -> Bool -> Maybe FilePath -> Bool -> Bool -> FilePath -> [String] -> IO ()
importFiles files out exportCode tryImport onlyTypes basePathAbs getIgnoreNotInScope absMutParams
  = importProject (defaultConfig defaultCustomisations files out exportCode tryImport onlyTypes basePathAbs getIgnoreNotInScope absMutParams)

convertFiles :: Adaption -> [String] -> Conversion ()
convertFiles adapt hsk_cts = do

  inFiles <- getInputFilesRecursively
  outDir <- getOutputDir
  exportCode <- getExportCode
  tryImport <- getTryImport
  onlyTypes <- getOnlyTypes
  basePathAbs <- getBasePathAbs
  ignoreNotInScope <- getIgnoreNotInScope
  absMutParams <- getAbsMutParams
  custs <- getCustomisations
  
  exists <- liftIO $ mapM doesDirectoryExist outDir
  when (case exists of Just False -> True ; _ -> False) $ liftIO $ maybe (return ()) createDirectory outDir

  units <- parseHskFiles tryImport onlyTypes basePathAbs (map Right hsk_cts ++ map Left (filter Hsx.isHaskellSourceFile inFiles))
  let (adaptTable : _, convertedUnits) = map_split (convertHskUnit custs exportCode ignoreNotInScope absMutParams adapt) units

  liftIO $ maybe (return ()) (\outDir -> copyFile (preludeFile adapt) (combine outDir (takeFileName (preludeFile adapt)))) outDir
  sequence_ (map (writeIsaUnit adaptTable (reservedKeywords adapt)) convertedUnits)
  liftIO $ case outDir of Nothing -> putStrLn $ SML.gshow (List.nubBy (let f (Isa.Module t _ _ _) = t in \m1 m2 -> f m1 == f m2)
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
    liftIO $ hPutStrLn stderr $ "writing " ++ dstName ++ "..."
    liftIO $ writeFile dstPath content)

getOutputDirMaybe f = getOutputDir >>= maybe (return ()) f
