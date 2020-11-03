{-# Language FlexibleInstances #-}
module Main where

import Control.Monad (unless)
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

import qualified Language.Oberon.Reserializer as Reserializer

import Language.Modula2 (parseModule, parseAndSimplifyModule, Placed, Version(..))
import Language.Modula2.AST (Language, Module)
import qualified Language.Modula2.ISO.AST as ISO (Language)
import qualified Language.Modula2.ConstantFolder -- brings in HasField instances
import qualified Language.Modula2.ISO.ConstantFolder -- brings in HasField instances

import Prelude hiding (readFile)

main = exampleTree "" "examples/" >>= defaultMain . testGroup "Modula-2"

width = 80
contextLines = 3

unparsables = map ("examples/Modula-2_Libraries/" <>)
              ["andrea-m2/applications/eth-hamburg/life/lifemodul.def",
               "andrea-m2/examples/generic/base3-2.mod",
               "andrea-m2/examples/generic/somebits.mod",
               "andrea-m2/lib/generic/bitmapope.mod",
               "andrea-m2/lib/generic/bitsetfun.mod",
               "andrea-m2/lib/generic/largesets.mod",
               "andrea-m2/lib/generic/packarray.mod",
               "andrea-m2/lib/generic/shufflefa.mod",
               "andrea-m2/lib/multiscope/bitmapop.mod",
               "andrea-m2/lib/eth-hamburg/blockio.mod",
               "andrea-m2/lib/eth-hamburg/cmdline.mod",
               "andrea-m2/lib/eth-hamburg/dateopera.mod",
               "andrea-m2/lib/eth-hamburg/directacc.mod",
               "andrea-m2/lib/eth-hamburg/extendstr.mod",
               "andrea-m2/lib/eth-hamburg/foreignco.mod",
               "andrea-m2/lib/eth-hamburg/fortrandi.def",
               "andrea-m2/lib/eth-hamburg/fortranfo.def",
               "andrea-m2/lib/eth-hamburg/fortranjp.def",
               "andrea-m2/lib/eth-hamburg/getcharac.mod",
               "andrea-m2/lib/eth-hamburg/memorysta.mod",
               "andrea-m2/lib/eth-hamburg/moremath.mod",
               "andrea-m2/lib/eth-hamburg/realinout.mod",
               "andrea-m2/lib/eth-hamburg/simplescr.mod",
               "andrea-m2/lib/eth-hamburg/simplewin.mod",
               "andrea-m2/lib/eth-hamburg/systemcon.def",
               "C.-Lins_Modula-2_Software_Component_Library/Vol4/sorting/timesort.mod",
               "PMOS/def/internet.def",
               "PMOS/def/kbdriver.def",
               "PMOS/def/miscpmos.def",
               "PMOS/def/netdb.def",
               "PMOS/sources/notdone/fastwind.mod",
               "PMOS/sources/general/graphics.mod",
               "PMOS/sources/general/lowlevel.def",
               "PMOS/sources/general/mouse33.mod",
               "PMOS/sources/general/play3.mod",
               "PMOS/sources/general/serialmo.mod",
               "PMOS/sources/special/lowlevel.mod"]
              <>
              ["examples/Dipl/BUFFERS.MOD",
               "examples/Dipl/LIBRARY.MOD",
               "examples/Dipl/MACHINE.MOD",
               "examples/Dipl/MEMORY.MOD",
               "examples/Dipl/NAMES.MOD",
               "examples/Dipl/M2/BUFFERS.MOD",
               "examples/Dipl/M2/LIBRARY.MOD",
               "examples/Dipl/M2/MACHINE.MOD",
               "examples/Dipl/M2/MEMORY.MOD",
               "examples/Dipl/M2/NAMES.MOD"]

exampleTree :: FilePath -> FilePath -> IO [TestTree]
exampleTree ancestry path =
   do let fullPath = combine ancestry path
      putStrLn fullPath
      isDir <- doesDirectoryExist fullPath
      if isDir
         then (:[]) . testGroup path . concat <$> (listDirectory fullPath >>= mapM (exampleTree fullPath))
         else return . (:[]) . testCase path . unless (any (`isSuffixOf` path) [".BNF", ".bnf", ".GRM"]) $
              do moduleSource <- readFile fullPath
                 (originalModule, prettyModule) <- prettyFile fullPath moduleSource
                 (originalModule', prettyModule') <- prettyFile fullPath originalModule
                 (originalModule'', prettyModule'') <- prettyFile fullPath prettyModule
                 putStrLn fullPath
                 assertEqual "original=original" originalModule originalModule'
                 assertEqual "pretty=pretty" prettyModule prettyModule'
                 assertEqual "pretty=pretty'" prettyModule prettyModule''
                 assertEqual "original=pretty" originalModule'' prettyModule''

prettyFile :: FilePath -> Text -> IO (Text, Text)
prettyFile path src
   | path `elem` unparsables = case (parsedModule1, parsedModule2) of
       (Left err1, Left err2)
          | err1 == err2 -> putStrLn (unpack $ failureDescription src err1 4) *> pure (src, src)
          | otherwise -> putStrLn (unpack $ failureDescription src err1 4 <> failureDescription src err2 4) *> pure (src, src)
       _ -> error (path ++ " is supposed to be unparseable")
   | otherwise = case parsedModule1 of
       Right [tree] -> return (Reserializer.reserialize tree, renderStrict $ layoutPretty defaultLayoutOptions $ pretty tree)
       Right trees -> error (show (length trees) ++ " ambiguous parses.")
       Left err1 -> case parsedModule2 of
         Left err2
          | err1 == err2 -> error (unpack $ failureDescription src err1 4)
          | otherwise -> error (unpack $ failureDescription src err1 4 <> failureDescription src err2 4)
         Right [tree] -> return (Reserializer.reserialize tree, renderStrict $ layoutPretty defaultLayoutOptions $ pretty tree)
         Right trees -> error (show (length trees) ++ " ambiguous parses.")
   where parsedModule1 = parseAndSimplifyModule Report src
         parsedModule2 = parseAndSimplifyModule ISO src

instance {-# overlaps #-} Pretty a => Pretty (Placed a) where
   pretty = pretty . snd

instance Pretty (Module Language Language Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)
instance Pretty (Module ISO.Language ISO.Language Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)
