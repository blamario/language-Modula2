{-# LANGUAGE FlexibleContexts, FlexibleInstances, RankNTypes, RecordWildCards, ScopedTypeVariables, TypeFamilies #-}

module Main where

import Language.Modula2 (Placed, parseModule, resolvePosition, resolvePositions)
import Language.Modula2.AST (Language, Module(..), StatementSequence, Statement, Expression)
import qualified Language.Modula2.AST as AST
import qualified Language.Modula2.Grammar as Grammar
import qualified Language.Modula2.Pretty ()
import qualified Language.Oberon.Pretty ()

import qualified Transformation.Rank2 as Rank2
import qualified Transformation.Deep as Deep

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
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete, failureDescription, offsetContext)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
import ReprTree
import System.FilePath (FilePath, addExtension, combine, takeDirectory)

import Prelude hiding (getLine, getContents, readFile)

data GrammarMode = ModuleMode | StatementsMode | StatementMode | ExpressionMode
    deriving Show

data Output = Plain | Pretty Int | Tree
            deriving Show

data Opts = Opts
    { optsMode        :: GrammarMode
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
       <> progDesc "Parse an Modula2 file, or parse interactively"
       <> header "Modula2 parser")

    p :: Parser Opts
    p = Opts
        <$> mode
        <*> (option auto (long "index" <> help "Index of ambiguous parse" <> showDefault <> value 0 <> metavar "INT"))
        <*> (Pretty <$> option auto (long "pretty" <> help "Pretty-print output" <> metavar "WIDTH")
             <|> Tree <$ switch (long "tree" <> help "Print the output as an abstract syntax tree")
             <|> pure Plain)
        <*> optional (strOption (short 'i' <> long "include" <> metavar "DIRECTORY"
                                 <> help "Where to look for imports"))
        <*> optional (strArgument
            ( metavar "FILE"
              <> help "Modula2 file to parse"))

    mode :: Parser GrammarMode
    mode = ModuleMode          <$ switch (long "module")
       <|> StatementMode       <$ switch (long "statement")
       <|> StatementsMode      <$ switch (long "statements")
       <|> ExpressionMode      <$ switch (long "expression")

main' :: Opts -> IO ()
main' Opts{..} =
    case optsFile of
        Just file -> (if file == "-" then getContents else readFile file)
                     >>= case optsMode
                         of ModuleMode ->
                              go Grammar.compilationUnit Grammar.modula2grammar file
                            _ -> error "A file usually contains a whole module."

        Nothing ->
            forever $
            getLine >>=
            case optsMode of
                ModuleMode     -> go Grammar.compilationUnit Grammar.modula2grammar "<stdin>"
                StatementMode  -> go Grammar.statement Grammar.modula2grammar "<stdin>"
                StatementsMode -> go Grammar.statementSequence Grammar.modula2grammar "<stdin>"
                ExpressionMode -> \src-> case getCompose ((resolvePosition src . (resolvePositions src <$>))
                                                          <$> Grammar.expression (parseComplete
                                                                                  Grammar.modula2grammar src))
                                         of Right [x] -> succeed optsOutput x
                                            Right l -> putStrLn ("Ambiguous: " ++ show optsIndex ++ "/"
                                                                 ++ show (length l) ++ " parses")
                                                       >> succeed optsOutput (l !! optsIndex)
                                            Left err -> Text.putStrLn (failureDescription src err 4)
  where
    go :: (Show a, Pretty a, a ~ t Placed Placed,
           Deep.Functor (Rank2.Map Grammar.NodeWrap NodeWrap) t Grammar.NodeWrap NodeWrap) =>
          (forall p. Grammar.Modula2Grammar AST.Language Grammar.NodeWrap p -> p (t Grammar.NodeWrap Grammar.NodeWrap))
       -> (Grammar (Grammar.Modula2Grammar AST.Language Grammar.NodeWrap) LeftRecursive.Parser Text)
       -> String -> Text -> IO ()
    go production grammar filename contents =
       case getCompose (resolvePositions contents <$> production (parseComplete grammar contents))
       of Right [x] -> succeed optsOutput x
          Right l -> putStrLn ("Ambiguous: " ++ show optsIndex ++ "/" ++ show (length l) ++ " parses")
                     >> succeed optsOutput (l !! optsIndex)
          Left err -> Text.putStrLn (failureDescription contents err 4)

type NodeWrap = ((,) Int)

succeed :: (Pretty a, Show a) => Output -> a -> IO ()
succeed out x = case out
                of Pretty width -> putDocW width (pretty x)
                   --Tree -> putStrLn (reprTreeString x)
                   Plain -> print x

instance Pretty (Module Language Language Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)
instance Pretty (StatementSequence Language Language NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Statement Language Language NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Expression Language Language NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
