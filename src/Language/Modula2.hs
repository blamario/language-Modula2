{-# Language FlexibleContexts, GADTs, OverloadedStrings, ScopedTypeVariables, StandaloneDeriving, TypeFamilies #-}

module Language.Modula2 (parseModule, parseAndCheckModule, resolvePosition, resolvePositions,
                         Placed, Version(..), SomeVersion(..)) where

import qualified Language.Modula2.Abstract as Abstract
import Language.Modula2.AST (Import(Import), Module(..))
import qualified Language.Modula2.AST as Report (Language, Expression)
import qualified Language.Modula2.ISO.AST as ISO (Language)
import qualified Language.Modula2.Grammar as Grammar
import qualified Language.Modula2.ISO.Grammar as ISO.Grammar
import qualified Language.Modula2.ConstantFolder as ConstantFolder
import Language.Modula2.ConstantFolder (Sem, ConstantFold, InhCF, SynCFExp, SynCFMod')
import Language.Modula2.Pretty ()
import Language.Modula2.ISO.Pretty ()

import qualified Rank2 as Rank2 (snd)
import Transformation.AG (Atts, Inherited, Synthesized)
import Transformation.AG.Generics (Auto)
import qualified Transformation.Rank2 as Rank2
import qualified Transformation.Full as Full
import qualified Transformation.Deep as Deep

import Control.Arrow (first)
import Control.Monad (when)
import Data.Functor.Compose (Compose(Compose, getCompose))
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (readFile)
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete, failureDescription)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
import qualified Text.Parser.Input.Position as Position
import System.Directory (doesFileExist)
import System.FilePath (FilePath, addExtension, combine, takeDirectory)

import Prelude hiding (readFile)

type Placed = (,) (Int, Grammar.ParsedLexemes)

data Options = Options{
   foldConstants :: Bool,
   checkTypes :: Bool,
   version :: SomeVersion}

data Version l where
   Report :: Version Report.Language
   ISO    :: Version ISO.Language

data SomeVersion where
   SomeVersion :: Version l -> SomeVersion

deriving instance Show (Version l)
deriving instance Show SomeVersion

resolvePositions :: (p ~ Grammar.NodeWrap, q ~ Placed, Deep.Functor (Rank2.Map p q) g)
                 => Text -> g p p -> g q q
resolvePositions src t = resolvePosition src Rank2.<$> t

resolvePosition :: Text -> Grammar.NodeWrap a -> Placed a
resolvePosition src = \((pos, ws), a)-> ((Position.offset src pos, ws), a)

-- | Parse and check the given text of a single module.
parseAndCheckModule :: forall l.
                       (Abstract.Modula2 l, Abstract.Nameable l,
                        Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
                        Abstract.Expression l ~ Report.Expression l,
                        Atts (Inherited (Auto ConstantFold)) (Abstract.Block l l Sem Sem) ~ InhCF l,
                        Atts (Inherited (Auto ConstantFold)) (Abstract.Definition l l Sem Sem) ~ InhCF l,
                        Atts (Inherited (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ InhCF l,
                        Atts (Synthesized (Auto ConstantFold)) (Abstract.Block l l Sem Sem)
                        ~ SynCFMod' l (Abstract.Block l l),
                        Atts (Synthesized (Auto ConstantFold)) (Abstract.Block l l Placed Placed)
                        ~ SynCFMod' l (Abstract.Block l l),
                        Atts (Synthesized (Auto ConstantFold)) (Abstract.Definition l l Placed Placed)
                        ~ SynCFMod' l (Abstract.Definition l l),
                        Atts (Synthesized (Auto ConstantFold)) (Abstract.Definition l l Sem Sem)
                        ~ SynCFMod' l (Abstract.Definition l l),
                        Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp l l,
                        Full.Functor (Auto ConstantFold) (Abstract.Block l l),
                        Full.Functor (Auto ConstantFold) (Abstract.Definition l l),
                        Full.Functor (Auto ConstantFold) (Abstract.Expression l l))
                    => Version l -> Text -> ParseResults Text [Module l l Placed Placed]
parseAndCheckModule version source =
   (ConstantFolder.foldConstants (predefined $ SomeVersion version) <$>) <$> parseModule version source
   where predefined :: SomeVersion -> ConstantFolder.Environment l
         predefined (SomeVersion Report) = Map.fromList $ map (first Abstract.nonQualIdent) $
            [("TRUE", Just Abstract.true),
             ("FALSE", Just Abstract.false)]
            ++ map builtin ["BITSET", "BOOLEAN", "CARDINAL", "CHAR", "INTEGER", "PROC", "REAL",
                            "ABS", "CAP", "CHR", "FLOAT", "HIGH", "MAX", "MIN",
                            "ODD", "ORD", "TRUNC", "VAL"]
            where builtin name = (name, Just $ Abstract.builtin name)
         predefined (SomeVersion ISO) = predefined (SomeVersion Report)

-- | Parse the given text of a single module.
parseModule :: Version l -> Text -> ParseResults Text [Module l l Placed Placed]
parseModule Report source = resolve source (parseComplete Grammar.modula2grammar source)
parseModule ISO source = resolve source (Rank2.snd $ parseComplete ISO.Grammar.modula2ISOgrammar source)

resolve :: Deep.Functor (Rank2.Map Grammar.NodeWrap Placed) (Abstract.Module l l)
        => Text
        -> Grammar.Modula2Grammar l Grammar.NodeWrap (Compose (Compose (ParseResults Text) []) ((,) [[Grammar.Lexeme]]))
        -> ParseResults Text [Abstract.Module l l Placed Placed]
resolve source results = getCompose (resolvePositions source . snd <$> getCompose (Grammar.compilationUnit results))

{-
parseNamedModule :: FilePath -> Text -> IO (ParseResults Text [Module Language Language Placed Placed])
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
