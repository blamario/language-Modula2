{-# Language FlexibleInstances #-}
module Main where

import Data.Either.Validation (Validation(..))
import Data.Functor.Identity (Identity(Identity))
import Data.List (isSuffixOf)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Text (Text, unpack)
import Data.Text.IO (readFile)
import Data.Text.Prettyprint.Doc (Pretty(pretty), layoutPretty, defaultLayoutOptions)
import Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath.Posix (combine)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertFailure, assertEqual, testCase)
import Text.Grampa (failureDescription)

import qualified Transformation.Rank2 as Rank2

import Language.Modula2 (parseModule, Placed)
import Language.Modula2.AST (Language, Module)
import Language.Modula2.Pretty ()

import Prelude hiding (readFile)

main = exampleTree "" "examples/" >>= defaultMain . testGroup "Modula-2"

width = 80
contextLines = 3

exampleTree :: FilePath -> FilePath -> IO [TestTree]
exampleTree ancestry path =
   do let fullPath = combine ancestry path
      putStrLn fullPath
      isDir <- doesDirectoryExist fullPath
      if isDir
         then (:[]) . testGroup path . concat <$> (listDirectory fullPath >>= mapM (exampleTree fullPath))
         else return . (:[]) . testCase path $
              do moduleSource <- readFile fullPath
                 prettyModule <- prettyFile ancestry moduleSource
                 prettyModule' <- prettyFile ancestry prettyModule
                 putStrLn fullPath
                 assertEqual "pretty" prettyModule prettyModule'

prettyFile :: FilePath -> Text -> IO Text
prettyFile path src = do
   let parsedModule = parseModule src
   case parsedModule
      of Left err -> error (unpack $ failureDescription src err 4)
         Right [tree] -> return (renderStrict $ layoutPretty defaultLayoutOptions $ pretty tree)
         Right trees -> error (show (length trees) ++ " ambiguous pases.")

instance Pretty (Module Language Language Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)