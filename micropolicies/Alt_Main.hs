module Main where

import Arch_Defs
import Forvis_Spec_I
import PIPE
import Memory
import Data.Bits

import qualified Data.Map.Strict as Data_Map
import Machine_State 

import Run_Program_PIPE
import Generator (genASTFile,genSymbolsFile)

import Test.QuickCheck
import qualified Text.PrettyPrint as P

import qualified TestUserType
import Printing
import Debug.Trace

import Control.Monad

-- Null "show" functions, for things that we don't want QuickCheck trying to print
instance Show Machine_State where
  show _ = ""
instance Show MState where
  show _ = ""

pol = "userType"

load_policy :: IO PolicyPlus
load_policy = do
  case pol of
    "userType" -> TestUserType.load_policy
    otherwise -> error $ "unknown policy '" ++ pol ++ "'"

main_trace = do
  pplus <- load_policy
  (M (ms1,ps1)) <- head <$> sample' (genMState pplus pplus)
  let (res, tr) = run_loop pplus 10 ps1 ms1
      (ps', ms') : _ = tr
  putStrLn ""
--  putStrLn "Initial state:"
--  print_coupled pplus ms1 ps1
--  putStrLn "_______________________________________________________________________"
--  putStrLn "Final state:"
--  print_coupled pplus ms' ps'
--  putStrLn "_______________________________________________________________________"
--  putStrLn "Trace:"
  printTrace pplus tr
--  printTrace pplus (reverse tr)
  putStrLn (show res)

-- The real one
main_test = do
  pplus <- load_policy
  quickCheckWith stdArgs{maxSuccess=1000}

--    $ forAllShrink (genMState pplus pplus)
--           (\m -> (shrinkMState pplus) pplus m)
--           (\m -> prop pplus pplus m)

--    Simple version
    $ forAll (genMState pplus pplus) $ \m -> prop pplus pplus m
    

main = main_test

