{-# OPTIONS_GHC -O -o bin/haskabelle_bin -odir build -hidir build -stubdir build #-}

{-  Author: Florian Haftmann, TU Muenchen

Toplevel interface to Haskabelle importer.
-}

module Main where

import System.Environment (getArgs, getProgName)
import System.Exit (exitWith, ExitCode (ExitFailure))

import Importer.Conversion (importProject, importFiles)
import Importer.Adapt (readAdapt, Adaption (..))
import Importer.Configuration (readConfig)
import Importer.Version (version)

{-
  Usage of the haskabelle binary:

  haskabelle_bin --internal <ADAPT> <SRC1> .. <SRCn> <DST>
  haskabelle_bin --internal <ADAPT> --config <CONFIG>
  haskabelle_bin --version

  Import Haskell files <SRC1> .. <SRCn> into Isabelle theories in directory
  <DST>, optionally using customary adaption in directory <ADAPT> OR import
  Haskell files according to configuration file <CONFIG>.
-}

readBool :: String -> IO Bool
readBool "true" = return True
readBool "false" = return False
readBool _ = exitWith (ExitFailure 2)

mainInterface :: [String] -> IO ()
mainInterface ["--internal", adaptDir, "--export", exportVar, "--config", configFile] = do
  exportCode <- readBool exportVar
  config <- readConfig configFile exportCode
  importProject config adaptDir
mainInterface ("--internal" : adaptDir : "--export" : exportVar : "--dump-output" : srcs @ (_ : _)) = mainInterfaceDump adaptDir exportVar srcs
mainInterface ("--internal" : adaptDir : "--export" : exportVar : src @ [_]) = mainInterfaceDump adaptDir exportVar src
mainInterface ("--internal" : adaptDir : "--export" : exportVar : srcs_dst @ (_ : _ : _)) =
  readBool exportVar >>= importFiles adaptDir (init srcs_dst) (Just (last srcs_dst))

mainInterface ("--internal" : args) = do
  putStrLn "Error calling internal haskabelle binary. Wrong parameters:"
  putStrLn ("  " ++ show args)

mainInterface ("--version" : _) = do
  putStrLn (version ++ ".")

mainInterface _ = do
  putStrLn "Do not invoke linked Haskabelle binary directly"
  putStrLn "  -- invoke it as described in the Haskabelle manual."
  putStrLn ""
  putStrLn "Have a nice day!"
  putStrLn ""
  exitWith (ExitFailure 2)

mainInterfaceDump adaptDir exportVar srcs =
  readBool exportVar >>= importFiles adaptDir srcs Nothing

main :: IO ()
main = getArgs >>= mainInterface
