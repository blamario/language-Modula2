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

import Language.Modula2 (parseModule, Placed, Version(..))
import Language.Modula2.AST (Language, Module)
import qualified Language.Modula2.ISO.AST as ISO (Language)

import Prelude hiding (readFile)

main = exampleTree "" "examples/" >>= defaultMain . testGroup "Modula-2"

width = 80
contextLines = 3

knownFailure path = any (`isSuffixOf` path) [".BNF", ".bnf", ".GRM"]
                    || path `elem` (map ("examples/Modula-2_Libraries/" <>)
                                    ["andrea-m2/applications/eth-hamburg/life/lifemodul.def",
                                     "andrea-m2/applications/eth-hamburg/life/lifemodul.mod",
                                     "andrea-m2/applications/eth-hamburg/life/makelife.mod",
                                     "andrea-m2/applications/eth-hamburg/text-tools/countwords.mod",
                                     "andrea-m2/applications/eth-hamburg/text-tools/kwic.mod",
                                     "andrea-m2/applications/eth-hamburg/text-tools/words.mod",
                                     "andrea-m2/applications/fst/search/search.mod",
                                     "andrea-m2/applications/generic/misc/un_stream.mod",
                                     "andrea-m2/applications/multiscope/symmetry/symm3.mod",
                                     "andrea-m2/applications/multiscope/symmetry/symm4.mod",
                                     "andrea-m2/examples/eth-hamburg/get-2.mod",
                                     "andrea-m2/examples/eth-hamburg/pig_latin.mod",
                                     "andrea-m2/examples/generic/base3-2.mod",
                                     "andrea-m2/examples/generic/graphics_2.mod",
                                     "andrea-m2/examples/generic/paint.mod",
                                     "andrea-m2/examples/generic/somebits.mod",
                                     "andrea-m2/lib/generic/base2.mod",
                                     "andrea-m2/lib/generic/base3.mod",
                                     "andrea-m2/lib/generic/bitmapope.mod",
                                     "andrea-m2/lib/generic/bitsetfun.mod",
                                     "andrea-m2/lib/generic/largenumb.mod",
                                     "andrea-m2/lib/generic/largesets.mod",
                                     "andrea-m2/lib/generic/moreio.mod",
                                     "andrea-m2/lib/generic/packarray.mod",
                                     "andrea-m2/lib/generic/psdots.mod",
                                     "andrea-m2/lib/generic/romannume.mod",
                                     "andrea-m2/lib/generic/saynumber.mod",
                                     "andrea-m2/lib/generic/shufflefa.mod",
                                     "andrea-m2/lib/generic/specialin.mod",
                                     "andrea-m2/lib/generic/stringope.mod",
                                     "andrea-m2/lib/multiscope/bitmapop.mod",
                                     "andrea-m2/lib/multiscope/cmdline.mod",
                                     "andrea-m2/lib/multiscope/dateoper.mod",
                                     "andrea-m2/lib/multiscope/formedit.mod",
                                     "andrea-m2/lib/multiscope/moreio.mod",
                                     "andrea-m2/lib/multiscope/screenio.mod",
                                     "andrea-m2/lib/multiscope/serial.mod",
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
                                     "andrea-m2/lib/eth-hamburg/regisgrap.mod",
                                     "andrea-m2/lib/eth-hamburg/simplescr.mod",
                                     "andrea-m2/lib/eth-hamburg/simplewin.mod",
                                     "andrea-m2/lib/eth-hamburg/systemcon.def",
                                     "andrea-m2/lib/eth-hamburg/veryscree.mod",
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
                                     "examples/Dipl/DECODER.MOD",
                                     "examples/Dipl/LIBRARY.MOD",
                                     "examples/Dipl/MACHINE.MOD",
                                     "examples/Dipl/MEMORY.MOD",
                                     "examples/Dipl/NAMES.MOD",
                                     "examples/Dipl/M2/BUFFERS.MOD",
                                     "examples/Dipl/M2/DECODER.MOD",
                                     "examples/Dipl/M2/LIBRARY.MOD",
                                     "examples/Dipl/M2/MACHINE.MOD",
                                     "examples/Dipl/M2/MEMORY.MOD",
                                     "examples/Dipl/M2/NAMES.MOD"])

exampleTree :: FilePath -> FilePath -> IO [TestTree]
exampleTree ancestry path =
   do let fullPath = combine ancestry path
      putStrLn fullPath
      isDir <- doesDirectoryExist fullPath
      if isDir
         then (:[]) . testGroup path . concat <$> (listDirectory fullPath >>= mapM (exampleTree fullPath))
         else return . (:[]) . testCase path . unless (knownFailure fullPath) $
              do moduleSource <- readFile fullPath
                 prettyModule <- prettyFile ancestry moduleSource
                 prettyModule' <- prettyFile ancestry prettyModule
                 putStrLn fullPath
                 assertEqual "pretty" prettyModule prettyModule'

prettyFile :: FilePath -> Text -> IO Text
prettyFile path src = do
   let parsedModule1 = parseModule Report src
   let parsedModule2 = parseModule ISO src
   case parsedModule1
      of Right [tree] -> return (renderStrict $ layoutPretty defaultLayoutOptions $ pretty tree)
         Right trees -> error (show (length trees) ++ " ambiguous parses.")
         Left err1 -> case parsedModule2
                      of Left err2 -> error (unpack $ failureDescription src err1 4 <> failureDescription src err2 4)
                         Right [tree] -> return (renderStrict $ layoutPretty defaultLayoutOptions $ pretty tree)
                         Right trees -> error (show (length trees) ++ " ambiguous parses.")

instance Pretty (Module Language Language Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)
instance Pretty (Module ISO.Language ISO.Language Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)
