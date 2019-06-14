{-# Language OverloadedStrings, Rank2Types, RecordWildCards, ScopedTypeVariables, TypeFamilies, TemplateHaskell #-}
module Language.Modula2.Grammar where

import Control.Applicative
import Control.Monad (guard, void)
import Data.Char (isAlphaNum, isDigit, isHexDigit, isLetter, isOctDigit, isSpace)
import Data.List.NonEmpty (NonEmpty, toList)
import Data.Monoid ((<>), Endo(Endo, appEndo))
import Data.Text (Text, unpack)
import Numeric (readOct, readDec, readHex, readFloat)
import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive (Parser)
import Text.Parser.Combinators (sepBy, sepBy1, sepByNonEmpty, try)
import Text.Parser.Token (braces, brackets, parens)

import qualified Rank2.TH
import Transformation.Deep as Deep (Product(Pair))

import qualified Language.Modula2.Abstract as Abstract
import qualified Language.Modula2.AST as AST

-- | All the productions of the Modula-2 grammar
data Modula2Grammar l f p = Modula2Grammar {
   ident :: p Abstract.Ident,
   number :: p (Abstract.Expression l l f f),
   integer :: p (Abstract.Expression l l f f),
   real :: p (Abstract.Expression l l f f),
   scaleFactor :: p Text,
   hexDigit :: p Text,
   digit :: p Text,
   octalDigit :: p Text,
   string_prod :: p Text,
   qualident :: p (Abstract.QualIdent l),
   constantDeclaration :: p (Abstract.Declaration l l f f),
   constantDefinition :: p (Abstract.Definition l l f f),
   constExpression :: p (NodeWrap (Abstract.ConstExpression l l f f)),
   relation :: p Abstract.RelOp,
   addOperator :: p (BinOp l f),
   mulOperator :: p (BinOp l f),
   set :: p (Abstract.Expression l l f f),
   element :: p (Abstract.Element l l f f),
   typeDeclaration :: p (Abstract.Declaration l l f f),
   typeDefinition :: p (Abstract.Definition l l f f),
   type_prod :: p (Abstract.Type l l f f),
   simpleType :: p (Abstract.Type l l f f),
   enumeration :: p (Abstract.Type l l f f),
   identList :: p (Abstract.IdentList l),
   subrangeType :: p (Abstract.Type l l f f),
   arrayType :: p (Abstract.Type l l f f),
   recordType :: p (Abstract.Type l l f f),
   fieldListSequence :: p (NonEmpty (f (Abstract.FieldList l l f f))),
   fieldList :: p (Abstract.FieldList l l f f),
   variant :: p (Abstract.Variant l l f f),
   caseLabelList :: p (NonEmpty (f (Abstract.CaseLabels l l f f))),
   caseLabels :: p (Abstract.CaseLabels l l f f),
   setType :: p (Abstract.Type l l f f),
   pointerType :: p (Abstract.Type l l f f),
   procedureType :: p (Abstract.Type l l f f),
   formalTypeList :: p (Abstract.FormalParameters l l f f),
   variableDeclaration :: p (Abstract.Declaration l l f f),
   variableDefinition :: p (Abstract.Definition l l f f),
   designator :: p (Abstract.Designator l l f f),
   expList :: p (NonEmpty (f (Abstract.Expression l l f f))),
   expression :: p (NodeWrap (Abstract.Expression l l f f)),
   simpleExpression :: p (NodeWrap (Abstract.Expression l l f f)),
   term :: p (NodeWrap (Abstract.Expression l l f f)),
   factor :: p (NodeWrap (Abstract.Expression l l f f)),
   actualParameters :: p [f (Abstract.Expression l l f f)],
   statement :: p (Abstract.Statement l l f f),
   assignment :: p (Abstract.Statement l l f f),
   procedureCall :: p (Abstract.Statement l l f f),
   statementSequence :: p (Abstract.StatementSequence l l f f),
   ifStatement :: p (Abstract.Statement l l f f),
   caseStatement :: p (Abstract.Statement l l f f),
   case_prod :: p (Abstract.Case l l f f),
   whileStatement :: p (Abstract.Statement l l f f),
   repeatStatement :: p (Abstract.Statement l l f f),
   forStatement :: p (Abstract.Statement l l f f),
   loopStatement :: p (Abstract.Statement l l f f),
   withStatement :: p (Abstract.Statement l l f f),
   procedureDeclaration :: p (Abstract.Declaration l l f f),
   procedureHeading :: p (Abstract.Ident, Abstract.ProcedureHeading l l f f),
   block :: p (Abstract.Block l l f f),
   declarationSequence :: p [f (Abstract.Declaration l l f f)],
   formalParameters :: p (Abstract.FormalParameters l l f f),
   fPSection :: p (Abstract.FPSection l l f f),
   formalType :: p (Abstract.Type l l f f),
   moduleDeclaration :: p (Abstract.Declaration l l f f),
   priority :: p (NodeWrap (Abstract.Priority l l f f)),
   export :: p (Abstract.Export l),
   import_prod :: p (Abstract.Import l),
   definitionModule :: p (Abstract.Module l l f f),
   definitionSequence :: p [f (Abstract.Definition l l f f)],
   programModule :: p (Abstract.Module l l f f),
   compilationUnit :: p (Abstract.Module l l f f)
   }

type NodeWrap = (,) (Position Text)

modula2grammar :: Grammar (Modula2Grammar AST.Language NodeWrap) Parser Text
modula2grammar = fixGrammar grammar

{- Adjusted from Report on the Programming Language Modula-2 -}
grammar :: forall l g. (Abstract.Modula2 l, Lexical g, LexicalConstraint Parser g Text)
        => GrammarBuilder (Modula2Grammar l NodeWrap) g Parser Text
grammar g@Modula2Grammar{..} = g{
   ident = identifier,
   number = integer <|> real,
   integer = lexicalToken (Abstract.integer . fst . head
                           <$> (readDec . unpack <$> takeCharsWhile1 isDigit
                                <|> readOct . unpack <$> takeCharsWhile1 isOctDigit <* string "B"
                                <|> readHex . unpack <$> (digit <> takeCharsWhile isHexDigit) <* string "H")
                           <|> Abstract.charCode . fst . head . readOct . unpack
                               <$> (octalDigit <> takeCharsWhile isOctDigit <* string "C")),
   real = Abstract.real . fst . head . readFloat . unpack
          <$> lexicalToken (takeCharsWhile1 isDigit <> string "." <> takeCharsWhile isDigit <> moptional scaleFactor),
   scaleFactor = string "E" <> moptional (string "+" <|> string "-") <> takeCharsWhile1 isDigit,
   hexDigit = satisfyCharInput isHexDigit,
   digit = satisfyCharInput isDigit,
   octalDigit = satisfyCharInput isOctDigit,
   string_prod = lexicalToken (char '\'' *> takeCharsWhile (\c-> c /= '\'' && c /= '\n') <* char '\''
                               <|> char '"' *> takeCharsWhile (\c-> c /= '"' && c /= '\n') <* char '"'),
   qualident = Abstract.qualIdent <$> many (ident <* delimiter ".") <*> ident,
   constantDeclaration = Abstract.constantDeclaration <$> (Abstract.identDef <$> ident)
                         <* delimiter "=" <*> constExpression,
   constantDefinition = Abstract.constantDefinition <$> (Abstract.identDef <$> ident)
                        <* delimiter "=" <*> constExpression,
   constExpression = expression,
   relation = Abstract.Equal <$ operator "=" <|> Abstract.Unequal <$ (operator "#" <|> operator "<>")
              <|> Abstract.Less <$ operator "<" <|> Abstract.LessOrEqual <$ operator "<=" 
              <|> Abstract.Greater <$ operator ">" <|> Abstract.GreaterOrEqual <$ operator ">=" 
              <|> Abstract.In <$ keyword "IN",
   addOperator = BinOp . wrapBinary 
                 <$> (Abstract.add <$ operator "+" <|> Abstract.subtract <$ operator "-" 
                      <|> Abstract.or <$ keyword "OR"),
   mulOperator = BinOp . wrapBinary
                 <$> (Abstract.multiply <$ operator "*" <|> Abstract.divide <$ operator "/"
                      <|> Abstract.integerDivide <$ keyword "DIV" <|> Abstract.modulo <$ keyword "MOD" 
                      <|> Abstract.and <$ (operator "&" <|> keyword "AND")),
   set = Abstract.set <$> optional qualident <*> braces (sepBy (wrap element) (delimiter ",")),
   element = Abstract.element <$> expression
             <|> Abstract.range <$> expression <* delimiter ".." <*> expression,
   typeDeclaration = Abstract.typeDeclaration <$> (Abstract.identDef <$> ident) <* delimiter "=" <*> wrap type_prod,
   typeDefinition = Abstract.typeDefinition <$> (Abstract.identDef <$> ident) <*> optional (delimiter "=" *> wrap type_prod),
   type_prod = simpleType <|> arrayType <|> recordType <|> setType <|> pointerType <|> procedureType,
   simpleType = Abstract.typeReference <$> qualident
                <|> enumeration
                <|> subrangeType,
   enumeration = Abstract.enumeration <$> parens identList,
   identList = sepByNonEmpty (Abstract.identDef <$> ident) (delimiter ","),
   subrangeType = brackets (Abstract.subRange (Nothing :: Maybe (Abstract.QualIdent l)) <$> constExpression
                            <* delimiter ".." <*> constExpression),
   arrayType =
      Abstract.arrayType <$ keyword "ARRAY" <*> sepBy1 (wrap simpleType) (delimiter ",") <* keyword "OF" <*> wrap type_prod,
   recordType = Abstract.recordType <$ keyword "RECORD" <*> fieldListSequence <* keyword "END",
   fieldListSequence = sepByNonEmpty (wrap fieldList) (delimiter ";"),
   fieldList = (Abstract.fieldList <$> identList <* delimiter ":" <*> wrap type_prod :: Parser g Text (Abstract.FieldList l l NodeWrap NodeWrap))
               <|> Abstract.caseFieldList <$ keyword "CASE" <*> optional (ident <* delimiter ":") <*> qualident
                                          <* keyword "OF" <*> sepByNonEmpty (wrap variant) (delimiter "|")
                                          <*> moptional (toList <$ keyword "ELSE" <*> fieldListSequence) <* keyword "END"
               <|> pure Abstract.emptyFieldList,
   variant = Abstract.variant <$> caseLabelList <* delimiter ":" <*> fieldListSequence,
   caseLabelList = sepByNonEmpty (wrap caseLabels) (delimiter ","),
   caseLabels = Abstract.singleLabel <$> constExpression
                <|> Abstract.labelRange <$> constExpression <* delimiter ".." <*> constExpression,
   setType = Abstract.setType <$ keyword "SET" <* keyword "OF" <*> wrap simpleType,
   pointerType = Abstract.pointerType <$ keyword "POINTER" <* keyword "TO" <*> wrap type_prod,
   procedureType = Abstract.procedureType <$ keyword "PROCEDURE" <*> optional (wrap formalTypeList),
   formalTypeList = Abstract.formalParameters
                    <$> parens (sepBy (wrap $
                                       Abstract.fpSection <$> (True <$ keyword "VAR" <|> pure False) <*> pure [] <*> wrap formalType)
                                      (delimiter ","))
                    <*> optional (delimiter ":" *> qualident),
   variableDeclaration = Abstract.variableDeclaration <$> identList <* delimiter ":" <*> wrap type_prod,
   variableDefinition = Abstract.variableDefinition <$> identList <* delimiter ":" <*> wrap type_prod,
   designator = Abstract.variable . Abstract.nonQualIdent <$> ident -- qualident
                <|> Abstract.field <$> wrap designator <* delimiter "." <*> ident
                <|> Abstract.index <$> wrap designator <*> brackets expList
                <|> Abstract.dereference <$> wrap designator <* operator "^",
   expList = sepByNonEmpty expression (delimiter ","),
   expression = simpleExpression
                <|> wrap (flip Abstract.relation <$> simpleExpression <*> relation <*> simpleExpression)
                <?> "expression",
   simpleExpression =
      (wrap (Abstract.positive <$ operator "+" <*> term) <|> wrap (Abstract.negative <$ operator "-" <*> term) <|> term)
      <**> (appEndo <$> concatMany (Endo <$> (flip . applyBinOp <$> addOperator <*> term))),
   term = factor <**> (appEndo <$> concatMany (Endo <$> (flip . applyBinOp <$> mulOperator <*> factor))),
   factor = wrap (number
                  <|> Abstract.string <$> string_prod
                  <|> set
                  <|> Abstract.read <$> wrap designator
                  <|> Abstract.functionCall <$> wrap designator <*> actualParameters
                  <|> (Abstract.not <$ (operator "~" <|> keyword "NOT") <*> factor))
            <|> parens expression,
   actualParameters = parens (sepBy expression (delimiter ",")),
   statement = assignment <|> procedureCall <|> ifStatement <|> caseStatement 
               <|> whileStatement <|> repeatStatement <|> loopStatement <|> forStatement <|> withStatement 
               <|> Abstract.exitStatement <$ keyword "EXIT" 
               <|> Abstract.returnStatement <$ keyword "RETURN" <*> optional expression
               <|> pure Abstract.emptyStatement
               <?> "statement",
   assignment  =  Abstract.assignment <$> wrap designator <* delimiter ":=" <*> expression,
   procedureCall = Abstract.procedureCall <$> wrap designator <*> optional actualParameters,
   statementSequence = Abstract.statementSequence <$> sepByNonEmpty (wrap statement) (delimiter ";"),
   ifStatement = Abstract.ifStatement <$ keyword "IF"
       <*> sepByNonEmpty (wrap $ Deep.Pair <$> expression <* keyword "THEN" <*> wrap statementSequence)
                         (keyword "ELSIF")
       <*> optional (keyword "ELSE" *> wrap statementSequence) <* keyword "END",
   caseStatement = Abstract.caseStatement <$ keyword "CASE" <*> expression
       <*  keyword "OF" <*> sepByNonEmpty (wrap case_prod) (delimiter "|")
       <*> optional (keyword "ELSE" *> wrap statementSequence) <* keyword "END",
   case_prod = Abstract.caseAlternative <$> caseLabelList <* delimiter ":" <*> wrap statementSequence,
   whileStatement = Abstract.whileStatement <$ keyword "WHILE" <*> expression <* keyword "DO"
                    <*> wrap statementSequence <* keyword "END",
   repeatStatement = Abstract.repeatStatement <$ keyword "REPEAT"
                     <*> wrap statementSequence <* keyword "UNTIL" <*> expression,
   forStatement = 
      Abstract.forStatement <$ keyword "FOR" <*> ident <* delimiter ":=" <*> expression
      <* keyword "TO" <*> expression <*> optional (keyword "BY" *> constExpression)
      <* keyword "DO" <*> wrap statementSequence <* keyword "END",
   loopStatement = Abstract.loopStatement <$ keyword "LOOP" <*> wrap statementSequence <* keyword "END",
   withStatement = Abstract.withStatement <$ keyword "WITH" <*> wrap designator <* keyword "DO"
                   <*> wrap statementSequence <* keyword "END",
   procedureDeclaration = do (procedureName, heading) <- sequenceA <$> wrap procedureHeading
                             delimiter ";"
                             body <- wrap block
                             lexicalToken (string procedureName)
                             return (Abstract.procedureDeclaration heading body),
   procedureHeading = Abstract.procedureHeading <$ keyword "PROCEDURE"
                      <**> do name <- ident
                              params <- optional (wrap formalParameters)
                              return (\proc-> (name, proc name params)),
   block = Abstract.block <$> declarationSequence <*> optional (keyword "BEGIN" *> wrap statementSequence)
           <* keyword "END",
   declarationSequence = concatMany (keyword "CONST" *> many (wrap constantDeclaration <* delimiter ";")
                                     <|> keyword "TYPE" *> many (wrap typeDeclaration <* delimiter ";")
                                     <|> keyword "VAR" *> many (wrap variableDeclaration <* delimiter ";")
                                     <|> (:[]) <$> (wrap procedureDeclaration <* delimiter ";"
                                                    <|> wrap moduleDeclaration <* delimiter ";"))
                         <?> "declarations",
   formalParameters = Abstract.formalParameters <$> parens (sepBy (wrap fPSection) (delimiter ";"))
                      <*> optional (delimiter ":" *> qualident),
   fPSection = Abstract.fpSection <$> (True <$ keyword "VAR" <|> pure False) 
               <*> sepBy1 ident (delimiter ",") <* delimiter ":" <*> wrap formalType,
   formalType = Abstract.arrayType [] <$ keyword "ARRAY" <* keyword "OF" <*> wrap formalType 
                <|> Abstract.typeReference <$> qualident,
   moduleDeclaration = do keyword "MODULE"
                          name <- ident
                          Abstract.moduleDeclaration name <$> optional priority <* delimiter ";"
                             <*> many import_prod <*> optional export <*> wrap block <* lexicalToken (string name),
   priority = brackets constExpression,
   export = Abstract.moduleExport <$ keyword "EXPORT" <*> (True <$ keyword "QUALIFIED" <|> pure False)
            <*> identList <* delimiter ";",
   import_prod = Abstract.moduleImport <$> optional (keyword "FROM" *> ident)
                 <* keyword "IMPORT" <*> identList <* delimiter ";",
   definitionModule = keyword "DEFINITION" *> keyword "MODULE" *>
                      do name <- ident
                         delimiter ";"
                         Abstract.definitionModule name <$> many import_prod <*> optional export <*> definitionSequence
                                                   <* keyword "END" <* lexicalToken (string name) <* delimiter ".",
   definitionSequence =  concatMany (keyword "CONST" *> many (wrap constantDefinition <* delimiter ";")
                                     <|> keyword "TYPE" *> many (wrap typeDefinition <* delimiter ";")
                                     <|> keyword "VAR" *> many (wrap variableDefinition <* delimiter ";")
                                     <|> (:[]) <$> (wrap (Abstract.procedureDefinition <$> wrap (snd <$> procedureHeading))
                                                    <* delimiter ";"))
                         <?> "definitions",
   programModule = do con <- (Abstract.implementationModule <$ keyword "IMPLEMENTATION"
                              <|> pure Abstract.programModule) <* keyword "MODULE"
                      name <- ident
                      con name <$> optional priority <* delimiter ";" <*> many import_prod
                               <*> wrap block <* lexicalToken (string name) <* delimiter ".",
   compilationUnit = lexicalWhiteSpace *> (definitionModule <|> programModule) <* skipMany (char '\x1a' *> lexicalWhiteSpace)
   }

newtype BinOp l f = BinOp {applyBinOp :: (f (Abstract.Expression l l f f)
                                          -> f (Abstract.Expression l l f f)
                                          -> f (Abstract.Expression l l f f))}

instance Show (BinOp l f) where
   show = const "BinOp{}"

instance Lexical (Modula2Grammar l f) where
   type LexicalConstraint p (Modula2Grammar l f) s = (s ~ Text, p ~ Parser)
   lexicalComment = comment
   lexicalWhiteSpace = takeCharsWhile isSpace *> skipMany (lexicalComment *> takeCharsWhile isSpace)
   isIdentifierStartChar = isLetter
   isIdentifierFollowChar = isAlphaNum
   identifierToken word = lexicalToken (do w <- word
                                           guard (w `notElem` reservedWords)
                                           return w)

comment :: Parser g Text ()
comment = try (string "(*"
               *> skipMany (comment <|> notFollowedBy (string "*)") <* anyToken <* takeCharsWhile isCommentChar)
               <* string "*)")
   where isCommentChar c = c /= '*' && c /= '('

wrap :: Parser g Text a -> Parser g Text (NodeWrap a)
wrap = ((,) <$> getSourcePos <*>)

wrapBinary :: (NodeWrap a -> NodeWrap a -> a) -> (NodeWrap a -> NodeWrap a -> NodeWrap a)
wrapBinary op a@(pos, _) b = (pos, op a b)

moptional p = p <|> mempty

delimiter, operator :: (Lexical g, LexicalConstraint Parser g Text) => Text -> Parser g Text ()

delimiter s = void (lexicalToken $ string s) <?> ("delimiter " <> show s)
operator s = void (lexicalToken $ string s) <?> ("operator " <> show s)

reservedWords :: [Text]
reservedWords = ["AND", "ARRAY", "BEGIN", "BY",
                 "CASE", "CONST", "DEFINITION", "DIV", "DO",
                 "ELSE", "ELSIF", "END", "EXIT", "EXPORT", "FOR", "FROM",
                 "IF", "IMPLEMENTATION", "IMPORT", "IN", "LOOP",
                 "MOD", "MODULE", "NOT",
                 "OF", "OR", "POINTER", "PROCEDURE",
                 "QUALIFIED", "RECORD", "REPEAT", "RETURN",
                 "SET", "THEN", "TO", "TYPE",
                 "UNTIL", "VAR", "WHILE", "WITH"]

$(Rank2.TH.deriveAll ''Modula2Grammar)
