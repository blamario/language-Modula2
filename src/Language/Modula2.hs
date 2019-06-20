{-# Language FlexibleContexts, GADTs, StandaloneDeriving, TypeFamilies #-}
-- | Every function in this module takes a flag that determines whether the input is a Modula2 module.

module Language.Modula2 (parseModule, resolvePosition, resolvePositions, Placed, Version(..), SomeVersion(..)) where

import qualified Language.Modula2.Abstract as Abstract
import Language.Modula2.AST (Import(Import), Module(..))
import qualified Language.Modula2.AST as Report (Language)
import qualified Language.Modula2.ISO.AST as ISO (Language)
import qualified Language.Modula2.Grammar as Grammar
import qualified Language.Modula2.ISO.Grammar as ISO.Grammar
import Language.Modula2.Pretty ()
import Language.Modula2.ISO.Pretty ()

import qualified Rank2 as Rank2 (snd)
import qualified Transformation.Rank2 as Rank2
import qualified Transformation.Deep as Deep

import Control.Monad (when)
import Data.Functor.Compose (Compose(Compose, getCompose))
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (readFile)
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete, failureDescription, positionOffset)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
import System.Directory (doesFileExist)
import System.FilePath (FilePath, addExtension, combine, takeDirectory)

import Prelude hiding (readFile)

type Placed = ((,) Int)

data Version l where
   Report :: Version Report.Language
   ISO    :: Version ISO.Language

data SomeVersion where
   SomeVersion :: Version l -> SomeVersion

deriving instance Show (Version l)
deriving instance Show SomeVersion

resolvePositions :: (p ~ Grammar.NodeWrap, q ~ Placed, Deep.Functor (Rank2.Map p q) g p q)
                 => Text -> g p p -> g q q
resolvePositions src t = resolvePosition src Rank2.<$> t

resolvePosition :: Text -> Grammar.NodeWrap a -> Placed a
resolvePosition src = \(pos, a)-> (positionOffset src pos, a)

-- | Parse the given text of a single module, without resolving the syntactic ambiguities.
parseModule :: Version l -> Text -> ParseResults [Abstract.Module l l Placed Placed]
parseModule Report source = resolve source (parseComplete Grammar.modula2grammar source)
parseModule ISO source = resolve source (Rank2.snd $ parseComplete ISO.Grammar.modula2ISOgrammar source)

resolve source results = getCompose (resolvePositions source <$> Grammar.compilationUnit results)

{-
parseNamedModule :: FilePath -> Text -> IO (ParseResults [Module Language Language Placed Placed])
parseNamedModule path name =
   do let basePath = combine path (unpack name)
      isDefn <- doesFileExist (addExtension basePath "Def")
      src <- readFile (addExtension basePath $ if isDefn then "Def" else "Mod")
      return (getCompose $ resolvePositions src <$> Grammar.compilationUnit (parseComplete Grammar.modula2grammar src))

parseImportsOf :: FilePath -> Map Text (Module Language Language Placed Placed)
               -> IO (Map Text (Module Language Language Placed Placed))
parseImportsOf path modules =
   case filter (`Map.notMember` modules) moduleImports
   of [] -> return modules
      newImports -> (((modules <>) . Map.fromList . map assertSuccess) <$>
                     (traverse . traverse) (parseNamedModule path) [(p, p) | p <- newImports])
                    >>= parseImportsOf path
   where moduleImports = foldMap (fmap importedModule . importsOf) modules
         importedModule (Import _ m) = m
         importsOf (DefinitionModule _ imports _ _) = imports
         importsOf (ImplementationModule _ _ imports _) = imports
         importsOf (ProgramModule _ _ imports _) = imports
         assertSuccess (m, Left err) = error ("Parse error in module " <> unpack m)
         assertSuccess (m, Right [p]) = (m, p)
         assertSuccess (m, Right _) = error ("Ambiguous parses of module " <> unpack m)
-}
