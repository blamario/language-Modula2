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
                    || path `elem` ["examples/Modula-2_Libraries/andrea-m2/applications/eth-hamburg/life/lifemodul.def",
                                    "examples/Modula-2_Libraries/andrea-m2/applications/eth-hamburg/life/lifemodul.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/applications/eth-hamburg/life/makelife.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/applications/eth-hamburg/text-tools/countwords.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/applications/eth-hamburg/text-tools/kwic.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/applications/eth-hamburg/text-tools/words.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/applications/fst/search/search.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/applications/generic/misc/un_stream.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/applications/multiscope/symmetry/symm3.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/applications/multiscope/symmetry/symm4.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/examples/eth-hamburg/get-2.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/examples/eth-hamburg/pig_latin.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/examples/generic/graphics_2.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/examples/generic/paint.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/examples/generic/somebits.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/base2.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/base3.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/bitmapope.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/bitsetfun.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/largenumb.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/largesets.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/moreio.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/packarray.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/psdots.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/romannume.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/saynumber.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/shufflefa.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/specialin.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/generic/stringope.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/multiscope/bitmapop.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/multiscope/cmdline.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/multiscope/dateoper.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/multiscope/formedit.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/multiscope/moreio.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/multiscope/screenio.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/multiscope/serial.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/blockio.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/cmdline.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/dateopera.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/directacc.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/extendstr.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/foreignco.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/fortrandi.def",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/fortranfo.def",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/fortranjp.def",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/getcharac.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/memorysta.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/moremath.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/realinout.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/regisgrap.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/simplescr.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/simplewin.mod",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/systemcon.def",
                                    "examples/Modula-2_Libraries/andrea-m2/lib/eth-hamburg/veryscree.mod",
                                    "examples/Modula-2_Libraries/C.-Lins_Modula-2_Software_Component_Library/Vol4/sorting/timesort.mod",
                                    "examples/Modula-2_Libraries/PMOS/def/internet.def",
                                    "examples/Modula-2_Libraries/PMOS/def/kbdriver.def",
                                    "examples/Modula-2_Libraries/PMOS/def/miscpmos.def",
                                    "examples/Modula-2_Libraries/PMOS/def/netdb.def",
                                    "examples/Modula-2_Libraries/PMOS/sources/notdone/fastwind.mod",
                                    "examples/Modula-2_Libraries/PMOS/sources/general/graphics.mod",
                                    "examples/Modula-2_Libraries/PMOS/sources/general/lowlevel.def",
                                    "examples/Modula-2_Libraries/PMOS/sources/general/mouse33.mod",
                                    "examples/Modula-2_Libraries/PMOS/sources/general/play3.mod",
                                    "examples/Modula-2_Libraries/PMOS/sources/general/serialmo.mod",
                                    "examples/Modula-2_Libraries/PMOS/sources/special/lowlevel.mod",
                                    "examples/Dipl/BUFFERS.MOD",
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
                                    "examples/Dipl/M2/NAMES.MOD"]

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
