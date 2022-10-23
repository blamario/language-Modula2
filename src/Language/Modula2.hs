{-# Language FlexibleContexts, GADTs, OverloadedStrings, ScopedTypeVariables, StandaloneDeriving, TypeFamilies #-}

-- | The programming language Modula-2

module Language.Modula2 (parseModule, parseAndSimplifyModule, resolvePosition, resolvePositions,
                         Placed, Version(..), SomeVersion(..)) where

import qualified Language.Modula2.Abstract as Abstract
import qualified Language.Modula2.AST as Report (Language)
import qualified Language.Modula2.ISO.AST as ISO (Language)
import qualified Language.Modula2.Grammar as Grammar
import qualified Language.Modula2.ISO.Grammar as ISO.Grammar
import qualified Language.Modula2.ConstantFolder as ConstantFolder
import qualified Language.Modula2.ISO.ConstantFolder as ISO.ConstantFolder
import Language.Modula2.ConstantFolder (ConstantFold)
import Language.Modula2.Pretty ()
import Language.Modula2.ISO.Pretty ()

import qualified Language.Oberon.Reserializer as Reserializer

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
import qualified Text.Parser.Input.Position as Position
import System.Directory (doesFileExist)
import System.FilePath (FilePath, addExtension, combine, takeDirectory)

import Prelude hiding (readFile)

-- | Every node in a parsed and resolved AST is wrapped with this functor
type Placed = (,) (Int, Grammar.ParsedLexemes, Int)

-- | The modes of operation
data Options = Options{
   -- | whether to fold the constants in the parsed module
   foldConstants :: Bool,
   -- whether to check the types
   -- checkTypes :: Bool,
   -- | which version of the Modula-2 language?
   version :: SomeVersion}

data Version l where
   -- | the version specified by Niklaus Wirth's ''Report on the Programming Language Modula-2''
   Report :: Version Report.Language
   -- | the version specified by the ISO standard
   ISO    :: Version ISO.Language

-- | The language version in existential container
data SomeVersion where
   SomeVersion :: Version l -> SomeVersion

deriving instance Show (Version l)
deriving instance Show SomeVersion

-- | Replace the stored positions in the entire tree with offsets from the start of the given source text
resolvePositions :: (p ~ Grammar.NodeWrap, q ~ Placed, Deep.Functor (Rank2.Map p q) g)
                 => Text -> p (g p p) -> q (g q q)
resolvePositions src t = resolvePosition src ((resolvePosition src Rank2.<$>) <$> t)

-- | Replace the stored positions of the given node with offset from the start of the given source text
resolvePosition :: Text -> Grammar.NodeWrap a -> Placed a
resolvePosition src = \((start, ws, end), a)-> ((Position.offset src start, ws, Position.offset src end), a)

-- | Parse the given text of a single module and fold constants inside it.
parseAndSimplifyModule :: (Abstract.Modula2 l, Abstract.Nameable l,
                           Full.Functor (Auto ConstantFold) (Abstract.Expression l l))
                    => Version l -> Text -> ParseResults Text [Placed (Abstract.Module l l Placed Placed)]
parseAndSimplifyModule Report source =
   (Reserializer.adjustPositions . (ConstantFolder.foldConstants (predefined Report) <$>) <$>)
   <$> parseModule Report source
parseAndSimplifyModule ISO source =
   (Reserializer.adjustPositions . (ISO.ConstantFolder.foldConstants (predefined ISO) <$>) <$>)
   <$> parseModule ISO source

-- | The predefined environment of types, constants, and procedures for the given language version.
predefined :: (Abstract.Modula2 l, Ord (Abstract.QualIdent l)) => Version l -> ConstantFolder.Environment l
predefined Report = Map.fromList $ map (first Abstract.nonQualIdent) $
   [("TRUE", Just Abstract.true),
    ("FALSE", Just Abstract.false)]
   ++ map builtin ["BITSET", "BOOLEAN", "CARDINAL", "CHAR", "INTEGER", "PROC", "REAL",
                   "ABS", "CAP", "CHR", "FLOAT", "HIGH", "MAX", "MIN", "ODD", "ORD", "TRUNC", "VAL"]
   where builtin name = (name, Just $ Abstract.builtin name)
predefined ISO = Map.fromList $ map (first Abstract.nonQualIdent) $
   [("TRUE", Just Abstract.true),
    ("FALSE", Just Abstract.false)]
   ++ map builtin ["BITSET", "BOOLEAN", "CARDINAL", "CHAR", "INTEGER", "PROC", "REAL",
                   "ABS", "CAP", "CHR", "FLOAT", "HIGH", "MAX", "MIN", "ODD", "ORD", "TRUNC", "VAL"]
   where builtin name = (name, Just $ Abstract.builtin name)

-- | Parse the given text of a single module.
parseModule :: Version l -> Text -> ParseResults Text [Placed (Abstract.Module l l Placed Placed)]
parseModule Report source = resolve source (parseComplete Grammar.modula2grammar source)
parseModule ISO source = resolve source (Rank2.snd $ parseComplete ISO.Grammar.modula2ISOgrammar source)

resolve :: Deep.Functor (Rank2.Map Grammar.NodeWrap Placed) (Abstract.Module l l)
        => Text
        -> Grammar.Modula2Grammar l Grammar.NodeWrap (Compose (Compose (ParseResults Text) []) ((,) [[Grammar.Lexeme]]))
        -> ParseResults Text [Placed (Abstract.Module l l Placed Placed)]
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
