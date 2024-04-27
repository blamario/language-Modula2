{-# LANGUAGE FlexibleContexts, FlexibleInstances, RankNTypes, RecordWildCards,
             ScopedTypeVariables, TypeFamilies, TypeOperators #-}

module Main where

import Language.Modula2 (Placed, Version(Report, ISO), SomeVersion(SomeVersion), parseModule, parseAndSimplifyModule,
                         resolvePosition, resolvePositions)
import Language.Modula2.AST (Language, Module(..), StatementSequence, Statement, Expression)
import Language.Modula2.ConstantFolder (ConstantFold)
import qualified Language.Modula2.Abstract as Abstract
import qualified Language.Modula2.AST as AST
import qualified Language.Modula2.Grammar as Grammar
import qualified Language.Modula2.ConstantFolder -- brings in HasField instances
import qualified Language.Modula2.ISO.AST as ISO.AST
import qualified Language.Modula2.ISO.Grammar as ISO.Grammar
import qualified Language.Modula2.ISO.ConstantFolder -- brings in HasField instances

import qualified Language.Oberon.Reserializer as Reserializer

import qualified Rank2 as Rank2 (Product(Pair), snd)
import qualified Transformation.Rank2 as Rank2
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import Transformation.AG.Generics (Auto)

import Data.Text.Prettyprint.Doc (Pretty(pretty))
import Data.Text.Prettyprint.Doc.Util (putDocW)

import Control.Monad
import Data.Data (Data)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Functor.Identity (Identity(Identity))
import Data.Functor.Compose (Compose, getCompose)
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Map.Lazy as Map
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (getLine, readFile, getContents)
import qualified Data.Text.IO as Text
import Data.Typeable (Typeable)
import Options.Applicative
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete, failureDescription)
import ReprTree
import System.FilePath (FilePath, addExtension, combine, takeDirectory)

import Prelude hiding (getLine, getContents, readFile)

import Debug.Trace

data GrammarMode = SimplifiedModuleMode | ModuleMode | StatementsMode | ExpressionMode
    deriving Show

data Output = Original | Plain | Pretty Int | Tree
            deriving Show

data Opts = Opts
    { optsMode        :: GrammarMode
    , optsVersion     :: SomeVersion
    , optsIndex       :: Int
    , optsOutput      :: Output
    , optsInclude     :: Maybe FilePath
    , optsFile        :: Maybe FilePath
    } deriving Show

main :: IO ()
main = execParser opts >>= main'
  where
    opts = info (helper <*> p)
        ( fullDesc
       <> progDesc "Parse a Modula-2 file, or parse interactively"
       <> header "Modula-2 parser")

    p :: Parser Opts
    p = Opts
        <$> mode
        <*> (SomeVersion Report <$ switch (long "report")
             <|> SomeVersion ISO <$ switch (long "ISO" <> long "iso"))
        <*> (option auto (long "index" <> help "Index of ambiguous parse" <> showDefault <> value 0 <> metavar "INT"))
        <*> (Pretty <$> option auto (long "pretty" <> help "Pretty-print output" <> metavar "WIDTH")
             <|> flag' Tree (long "tree" <> help "Print the output as an abstract syntax tree")
             <|> flag' Original (long "original" <> help "Print the output with the original tokens and whitespace")
             <|> pure Plain)
        <*> optional (strOption (short 'i' <> long "include" <> metavar "DIRECTORY"
                                 <> help "Where to look for imports"))
        <*> optional (strArgument
            ( metavar "FILE"
              <> help "Modula-2 file to parse"))

    mode :: Parser GrammarMode
    mode = SimplifiedModuleMode   <$ switch (long "simplified-module")
       <|> ModuleMode          <$ switch (long "module")
       <|> StatementsMode      <$ switch (long "statements")
       <|> ExpressionMode      <$ switch (long "expression")

main' :: Opts -> IO ()
main' Opts{..} =
   case optsVersion
   of SomeVersion Report -> process Report
      SomeVersion ISO -> process ISO
  where
     process :: (Abstract.Modula2 l, Abstract.Nameable l,
                 Full.Functor (Auto ConstantFold) (Abstract.Expression l l)) => Version l -> IO ()
     process version =
         case optsFile of
             Just file -> (if file == "-" then getContents else readFile file)
                          >>= case optsMode
                              of SimplifiedModuleMode ->
                                    \contents-> case version
                                                of Report -> report contents (parseAndSimplifyModule Report contents)
                                                   ISO -> report contents (parseAndSimplifyModule ISO contents)
                                 ModuleMode
                                    | Report <- version -> go Report Grammar.compilationUnit file
                                    | ISO <- version -> go ISO Grammar.compilationUnit file
                                 _ -> error "A file usually contains a whole module."

             Nothing | Report <- version ->
                 forever $
                 getLine >>=
                 case optsMode of
                     ModuleMode     -> go Report Grammar.compilationUnit "<stdin>"
                     StatementsMode -> go Report Grammar.statementSequence "<stdin>"
                     ExpressionMode -> go Report Grammar.expression "<stdin>"
             Nothing | ISO <- version ->
                 forever $
                 getLine >>=
                 case optsMode of
                     ModuleMode     -> go ISO Grammar.compilationUnit "<stdin>"
                     StatementsMode -> go ISO Grammar.statementSequence "<stdin>"
                     ExpressionMode -> go ISO Grammar.expression "<stdin>"
     go :: (Show a, Pretty a, a ~ g l l Placed Placed,
            Deep.Functor (Rank2.Map Grammar.NodeWrap Placed) (g l l),
            Deep.Foldable Reserializer.Serialization (g l l)) =>
           Version l
        -> (forall p. Functor p => Grammar.Modula2Grammar l Grammar.NodeWrap p -> p (Grammar.NodeWrap (g l l Grammar.NodeWrap Grammar.NodeWrap)))
        -> String -> Text -> IO ()
     go Report production filename contents =
        report contents (getCompose $ resolvePositions contents . snd
                         <$> getCompose (production $ parseComplete Grammar.modula2grammar contents))
     go ISO production filename contents =
        report contents (getCompose $ resolvePositions contents . snd
                         <$> getCompose (production $ Rank2.snd $ parseComplete (ISO.Grammar.modula2ISOgrammar) contents))
     report :: (Pretty a, Show a, a ~ Placed (g l l Placed Placed),
                Deep.Foldable Reserializer.Serialization (g l l)) => Text -> ParseResults Text [a] -> IO ()
     report _ (Right [x]) = succeed optsOutput x
     report _ (Right l) = putStrLn ("Ambiguous: " ++ show optsIndex ++ "/" ++ show (length l) ++ " parses")
                          >> succeed optsOutput (l !! optsIndex)
     report contents (Left err) = Text.putStrLn (failureDescription contents err 4)

type NodeWrap = ((,) Int)


succeed :: (Pretty a, Show a, a ~ Placed (g l l Placed Placed),
            Deep.Foldable Reserializer.Serialization (g l l)) => Output -> a -> IO ()
succeed out x = case out
                of Original -> Text.putStr (Reserializer.reserialize x)
                   Pretty width -> putDocW width (pretty x)
                   --Tree -> putStrLn (reprTreeString x)
                   Plain -> print x

instance {-# overlaps #-} Pretty a => Pretty (Placed a) where
   pretty = pretty . snd

instance Pretty (Module Language Language Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)
instance Pretty (StatementSequence Language Language Placed Placed) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Statement Language Language Placed Placed) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Expression Language Language Placed Placed) where
   pretty _ = error "Disambiguate before pretty-printing"

instance Pretty (Module ISO.AST.Language ISO.AST.Language Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)
instance Pretty (StatementSequence ISO.AST.Language ISO.AST.Language Placed Placed) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (ISO.AST.Statement ISO.AST.Language ISO.AST.Language Placed Placed) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (ISO.AST.Expression ISO.AST.Language ISO.AST.Language Placed Placed) where
   pretty _ = error "Disambiguate before pretty-printing"
