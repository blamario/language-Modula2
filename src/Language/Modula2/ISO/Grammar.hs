{-# Language FlexibleContexts, FlexibleInstances, OverloadedStrings, Rank2Types, RecordWildCards, ScopedTypeVariables,
             TypeFamilies, TypeSynonymInstances, TemplateHaskell #-}
-- | Modula-2 grammar adapted from the ISO specification of the language.

module Language.Modula2.ISO.Grammar where

import Control.Applicative
import Control.Monad (guard, void)
import Data.Char (isAlphaNum, isDigit, isHexDigit, isLetter, isOctDigit, isSpace)
import Data.List.NonEmpty (NonEmpty, toList)
import Data.Maybe (catMaybes)
import Data.Monoid ((<>), Endo(Endo, appEndo))
import Data.Text (Text, unpack)
import Numeric (readOct, readDec, readHex, readFloat)
import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive.Transformer (lift, tmap)
import Text.Parser.Combinators (sepBy, sepBy1, sepByNonEmpty, try)
import Text.Parser.Token (braces, brackets, parens)

import qualified Rank2
import qualified Rank2.TH
import Transformation.Deep as Deep (Product(Pair))

import Language.Oberon.Grammar (TokenType(..))

import qualified Language.Modula2.Abstract as Abstract
import qualified Language.Modula2.ISO.Abstract as ISO.Abstract
import qualified Language.Modula2.ISO.AST as AST
import qualified Language.Modula2.Grammar as ReportGrammar
import           Language.Modula2.Grammar (delimiter, wrap)

type Parser = ReportGrammar.Parser

-- | The names and types of all the new grammar productions in the ISO specification
data ISOMixin l f p = ISOMixin{
   machineAddress :: p (f (Abstract.ConstExpression l l f f)),
   packedSetType :: p (Abstract.Type l l f f),
   moduleBody :: p (Abstract.Block l l f f),
   variableIdentifierList :: p (NonEmpty (f (ISO.Abstract.AddressedIdent l l f f))),
   retryStatement :: p (Abstract.Statement l l f f),
   arrayConstructor :: p (Abstract.Expression l l f f),
   recordConstructor :: p (Abstract.Expression l l f f),
   arrayConstructedValue :: p [f (ISO.Abstract.Item l l f f)],
   recordConstructedValue :: p [f (Abstract.Expression l l f f)],
   setConstructedValue :: p [f (Abstract.Element l l f f)],
   arrayPart :: p (ISO.Abstract.Item l l f f),
   structureComponent  :: p (f (Abstract.Expression l l f f))}

-- | The new grammar productions in the ISO specification
isoMixin :: (ISO.Abstract.Modula2 l, LexicalParsing (Parser g Text))
         => ReportGrammar.Modula2Grammar l ReportGrammar.NodeWrap (Parser g Text)
         -> ISOMixin l ReportGrammar.NodeWrap (Parser g Text)
         -> ISOMixin l ReportGrammar.NodeWrap (Parser g Text)
isoMixin ReportGrammar.Modula2Grammar{..} ISOMixin{..} = ISOMixin{
   machineAddress = brackets constExpression,
   variableIdentifierList =
        sepByNonEmpty (wrap (ISO.Abstract.unaddressedIdent <$> ident
                             <|> ISO.Abstract.addressedIdent <$> ident <*> brackets constExpression))
                      (delimiter ","),
   packedSetType = ISO.Abstract.packedSetType <$ keyword "PACKED" <* keyword "SET" <* keyword "OF" <*> wrap simpleType,
   moduleBody = ISO.Abstract.exceptionHandlingBlock <$> declarationSequence
                <*> optional (keyword "BEGIN" *> statementSequence)
                <*> optional (keyword "EXCEPT" *> statementSequence)
                <*> optional (keyword "FINALLY" *> statementSequence) <* keyword "END",
   retryStatement = ISO.Abstract.retryStatement <$ keyword "RETRY",
   arrayConstructor = ISO.Abstract.array . Just <$> qualident <*> arrayConstructedValue,
   arrayConstructedValue = braces (sepBy1 (wrap arrayPart) (delimiter ",")),
   arrayPart = ISO.Abstract.single <$> structureComponent
               <|> ISO.Abstract.repeated <$> structureComponent <* keyword "BY" <*> constExpression,
   structureComponent = expression <|> wrap (ISO.Abstract.array Nothing <$> arrayConstructedValue
                                             <|> ISO.Abstract.record Nothing <$> recordConstructedValue
                                             <|> Abstract.set Nothing <$> setConstructedValue),
   recordConstructor = ISO.Abstract.record . Just <$> qualident <*> recordConstructedValue,
   recordConstructedValue = braces (sepBy structureComponent (delimiter ",")),
   setConstructedValue = braces (sepBy (wrap element) (delimiter ","))
   }

type ISOGrammar l = Rank2.Product (ISOMixin l ReportGrammar.NodeWrap) (ReportGrammar.Modula2Grammar l ReportGrammar.NodeWrap)

modula2ISOgrammar :: Grammar (ISOGrammar AST.Language) Parser Text
modula2ISOgrammar = fixGrammar isoGrammar

-- | All the productions of the ISO Modula-2 grammar
isoGrammar :: forall l g. (ISO.Abstract.Modula2 l, LexicalParsing (Parser g Text))
           => GrammarBuilder (ISOGrammar l) g Parser Text
isoGrammar (Rank2.Pair iso@ISOMixin{..} report@ReportGrammar.Modula2Grammar{..}) =
   Rank2.Pair (isoMixin report iso) $
   reportGrammar{
      ReportGrammar.variableDeclaration =
           ISO.Abstract.addressedVariableDeclaration <$> variableIdentifierList <* delimiter ":" <*> wrap type_prod,
      ReportGrammar.procedureDeclaration =
           ReportGrammar.procedureDeclaration reportGrammar
           <|> ISO.Abstract.forwardProcedureDeclaration <$> wrap (snd <$> procedureHeading)
               <* delimiter ";" <* keyword "FORWARD",
      ReportGrammar.type_prod = ReportGrammar.type_prod reportGrammar <|> packedSetType,
      ReportGrammar.subrangeType = uncurry <$> (Abstract.subRange <$> optional qualident)
                                   <*> brackets ((,) <$> constExpression <* delimiter ".." <*> constExpression),
      ReportGrammar.variant = ReportGrammar.variant reportGrammar <|> pure ISO.Abstract.emptyVariant,
      ReportGrammar.block = ISO.Abstract.exceptionHandlingBlock <$> declarationSequence
                            <*> optional (keyword "BEGIN" *> statementSequence)
                            <*> optional (keyword "EXCEPT" *> statementSequence) <*> pure Nothing <* keyword "END",
      ReportGrammar.statement = ReportGrammar.statement reportGrammar <|> retryStatement,
      ReportGrammar.caseStatement = Abstract.caseStatement <$ keyword "CASE" <*> expression
       <*  keyword "OF" <*> (catMaybes <$> sepBy1 (optional $ wrap case_prod) (delimiter "|"))
       <*> optional (keyword "ELSE" *> statementSequence) <* keyword "END",
      ReportGrammar.factor = ReportGrammar.factor reportGrammar <<|> wrap arrayConstructor <<|> wrap recordConstructor,
      ReportGrammar.set = Abstract.set . Just <$> qualident <*> setConstructedValue,
      ReportGrammar.mulOperator = ReportGrammar.mulOperator reportGrammar
                                  <|> ReportGrammar.BinOp . ReportGrammar.wrapBinary
                                      <$> (ISO.Abstract.remainder <$ keyword "REM")}
   where reportGrammar = ReportGrammar.grammar report

instance TokenParsing (Parser (ISOGrammar l) Text) where
   someSpace = someLexicalSpace
   token = lexicalToken

instance LexicalParsing (Parser (ISOGrammar l) Text) where
   lexicalComment = do c <- ReportGrammar.comment
                       lift ([[ReportGrammar.Comment c]], ())
   lexicalWhiteSpace = ReportGrammar.whiteSpace
   isIdentifierStartChar = isLetter
   isIdentifierFollowChar c = isAlphaNum c || c == '_'
   identifierToken word = lexicalToken (do w <- word
                                           guard (w `notElem` reservedWords)
                                           return w)
   lexicalToken p = snd <$> tmap addOtherToken (match p) <* lexicalWhiteSpace
      where addOtherToken ([], (i, x)) = ([[ReportGrammar.Token Other i]], (i, x))
            addOtherToken (t, (i, x)) = (t, (i, x))
   keyword s = lexicalToken (string s
                             *> notSatisfyChar isAlphaNum
                             <* lift ([[ReportGrammar.Token Keyword s]], ()))
               <?> ("keyword " <> show s)

reservedWords = ReportGrammar.reservedWords <> ["EXCEPT", "FINALLY", "FORWARD", "PACKEDSET", "REM", "RETRY"]

$(Rank2.TH.deriveAll ''ISOMixin)

{-
compilation module = program module | definition module | implementation module,
program module =
   "MODULE", module identifier, [protection], semicolon,
   import lists, module block, module identifier, period,
module identifier = identifier,
protection = left bracket, protection expression, right bracket,
protection expression = constant expression,
definition module =
   "DEFINITION", "MODULE", module identifier, semicolon,
   import lists, definitions, "END", module identifier, period,
implementation module =
   "IMPLEMENTATION", "MODULE", module identifier, [protection], 
   semicolon, import lists, module block, module identifier, period,
import lists = {import list},
import list = simple import | unqualified import,
simple import = "IMPORT", identifier list, semicolon,
unqualified import = "FROM", module identifier, "IMPORT", identifier list, semicolon,
export list = unqualified export | qualified export,
unqualified export = "EXPORT", identifier list, semicolon,
qualified export = "EXPORT", "QUALIFIED", identifier list, semicolon,
qualified identifier = {module identifier, period}, identifier,
definitions = {definition},
definition =
   "CONST", {constant declaration, semicolon} |
   "TYPE", {type definition, semicolon} |
   "VAR", {variable declaration, semicolon} |
   procedure heading, semicolon,
procedure heading = proper procedure heading | function procedure heading,
type definition = type declaration | opaque type definition,
opaque type definition = identifier,
proper procedure heading = "PROCEDURE", procedure identifier, [formal parameters],
formal parameters = left parenthesis, [formal parameter list], right parenthesis,
formal parameter list = formal parameter, {semicolon, formal parameter},
function procedure heading = "PROCEDURE", procedure identifier, formal parameters,
   colon, function result type,
function result type = type identifier,
formal parameter = value parameter specification | variable parameter specification,
value parameter specification = identifier list, colon, formal type,
variable parameter specification = "VAR", identifier list, colon, formal type,
declarations = {declaration},
declaration =
   "CONST", {constant declaration, semicolon} |
   "TYPE", {type declaration, semicolon} |
   "VAR", {variable declaration, semicolon} |
   procedure declaration, semicolon |
   local module declaration, semicolon,
constant declaration = identifier, equals, constant expression,
type declaration = identifier, equals, type denoter,
variable declaration = variable identifier list, colon, type denoter,

variable identifier list =
   identifier, [ machine address], {comma, identifier, 
   [machine address] },
machine address =
   left bracket, value of address type, right bracket,
value of address type =
   constant expression,
procedure declaration = proper procedure declaration | function procedure declaration,
proper procedure declaration =
   proper procedure heading, semicolon, (proper procedure block, 
   procedure identifier | "FORWARD"),
procedure identifier =
   identifier,
function procedure declaration =
   function procedure heading, semicolon, (function procedure block,
    procedure identifier | "FORWARD"),
local module declaration =
   "MODULE", module identifier, [protection], semicolon,
   import lists, [export list], module block, module identifier,
type denoter =
   type identifier |new type,
ordinal type denoter =
   ordinal type identifier | new ordinal type,
type identifier =
   qualified identifier,
ordinal type identifier =
   type identifier,
new type =
   new ordinal type | set type | packedset type | pointer type |
   procedure type | array type | record type,
new ordinal type =
   enumeration type | subrange type,
enumeration type =
   left parenthesis, identifier list, right parenthesis,
identifier list =
   identifier, {comma, identifier},
subrange type =
   [range type], left bracket, constant expression, ellipsis,
   constant expression, right bracket,
range type =
   ordinal type identifier,
set type =
   "SET", "OF", base type,
base type =
   ordinal type denoter,
packedset type =
   "PACKEDSET", "OF", base type,
pointer type =
   "POINTER", "TO", bound type,
bound type =
   type denoter,
procedure type =
   proper procedure type | function procedure type,
proper procedure type =
   "PROCEDURE", [left parenthesis, [formal parameter type list],
    right parenthesis],
function procedure type =
   "PROCEDURE", left parenthesis, [formal parameter type list],
    right parenthesis, colon, function result type,
formal parameter type list =
   formal parameter type, {comma, formal parameter type},
formal parameter type =
   variable formal type | value formal type,
variable formal type =
   "VAR", formal type,
value formal type =
   formal type,
formal type =
   type identifier | open array formal type,
open array formal type =
   "ARRAY", "OF", {"ARRAY", "OF"}, type identifier,
array type =
   "ARRAY", index type, {comma, index type}, "OF", component type,
index type =
   ordinal type denoter,
component type =
   type denoter,
record type =
   "RECORD", field list, "END",
field list =
   fields, {semicolon, fields},
fields =
   [fixed fields | variant fields],
fixed fields =
   identifier list, colon, field type,
field type =
   type denoter,
variant fields =
   "CASE", [tag identifier], colon, tag type, "OF",
   variant list, "END",
tag identifier =
   identifier,
tag type =
   ordinal type identifier,
variant list =
   variant, {case separator, variant}, [variant else part],
variant else part =
   "ELSE", field list,
variant =
   [variant label list, colon, field list],
variant label list =
   variant label, {comma, variant label},
variant label =
   constant expression, [ellipsis, constant expression],
proper procedure block =
   declarations, [procedure body], "END",
procedure body =
   "BEGIN", block body,
function procedure block =
   declarations, function body, "END",
function body =
   "BEGIN", block body,
module block =
   declarations, [module body], "END",
module body =
   initialization body, [finalization body],,
initialization body =
   "BEGIN", block body,
finalization body =
   "FINALLY", block body,
block body =
   normal part, ["EXCEPT", exceptional part],
normal part =
   statement sequence,
exceptional part =
   statement sequence,
statement =
   empty statement | assignment statement | procedure call |
    return statement |retry statement | with statement |
    if statement | case statement |while statement |
    repeat statement | loop statement |exit statement |for statement,
statement sequence =
   statement, {semicolon, statement},
empty statement =
  ,
assignment statement =
   variable designator, assignment operator, expression,
procedure call =
   procedure designator, [actual parameters],
procedure designator =
   value designator,
return statement =
   simple return statement | function return statement,
simple return statement =
   "RETURN",
function return statement =
   "RETURN", expression,
retry statement =
   "RETRY",
with statement =
   "WITH", record designator, "DO", statement sequence, "END",
record designator =
   variable designator | value designator,
if statement =
   guarded statements, [if else part], "END",
guarded statements =
   "IF", boolean expression, "THEN", statement sequence,
   {"ELSIF", boolean expression, "THEN", statement sequence},
if else part =
   "ELSE", statement sequence,
boolean expression =
   expression,
case statement =
   "CASE", case selector, "OF", case list, "END",
case selector =
   ordinal expression,
case list =
   case alternative, {case separator, case alternative},
   [case else part],
case else part =
   "ELSE", statement sequence,
case alternative =
   [case label list, colon, statement sequence],
case label list =
   case label, {comma, case label},
case label =
   constant expression, [ellipsis, constant expression],
while statement =
   "WHILE", boolean expression, "DO", statement sequence, "END",
repeat statement =
   "REPEAT", statement sequence, "UNTIL", boolean expression,
loop statement =
   "LOOP", statement sequence, "END",
exit statement =
   "EXIT",
for statement =
   "FOR", control variable identifier, assignment operator, 
   initial value, "TO", final value, ["BY", step size], "DO",
   statement sequence, "END",
control variable identifier =
   identifier,
initial value =
   ordinal expression,
final value =
   ordinal expression,
step size =
   constant expression,
variable designator =
   entire designator | indexed designator |
   selected designator | dereferenced designator,
entire designator =
   qualified identifier,
indexed designator =
   array variable designator, left bracket, index expression,
   {comma, index expression}, right bracket,
array variable designator =
   variable designator,
index expression =
   ordinal expression,
selected designator =
   record variable designator, period, field identifier,
record variable designator =
   variable designator,
field identifier =
   identifier,
dereferenced designator =
   pointer variable designator, dereferencing operator,
pointer variable designator =
   variable designator,
expression =
   simple expression, [relational operator, simple expression],
simple expression =
   [sign], term, {term operator, term},
term =
   factor, {factor operator, factor},
factor =
   left parenthesis, expression, right parenthesis | 
   logical negation operator, factor |
   value designator | function call |
   value constructor | constant literal,
ordinal expression =
   expression,
relational operator =
   equals operator | inequality operator | less than operator |
   greater than operator | less than or equal operator |
   subset operator | greater than or equal operator | 
   superset operator | set membership operator,
term operator =
   plus operator | set union operator | minus operator |
   set difference operator | logical disjunction operator | 
   string catenate symbol,
factor operator =
   multiplication operator | set intersection operator | 
   division operator | symmetric set difference operator |
   rem operator | div operator | mod operator |
   logical conjunction operator,
value designator =
  entire value | indexed value | selected value | dereferenced value,
entire value =
   qualified identifier,
indexed value =
   array value, left bracket, index expression,
   {comma, index expression}, right bracket,
array value =
   value designator,
selected value =
   record value, period, field identifier,
record value =
   value designator,
dereferenced value =
   pointer value, dereferencing operator,
pointer value =
   value designator,
function call =
   function designator, actual parameters,
function designator =
   value designator,
value constructor =
   array constructor | record constructor | set constructor,
array constructor =
   array type identifier, array constructed value,
array type identifier =
   type identifier,
array constructed value =
   left brace, repeated structure component,
   {comma, repeated structure component}, right brace,
repeated structure component =
   structure component, ["BY", repetition factor],
repetition factor =
   constant expression,
structure component =
   expression | array constructed value |
   record constructed value | set constructed value,
record constructor =
   record type identifier, record constructed value,
record type identifier =
   type identifier,
record constructed value =
   left brace, [structure component, {comma, structure component}],
   right brace,

set constructor =
   set type identifier, set constructed value,
set type identifier =
   type identifier,
set constructed value =
   left brace, [member, {comma, member}], right brace,
member =
   interval | singleton,
interval =
   ordinal expression, ellipsis, ordinal expression,
singleton =
   ordinal expression,
constant literal =
   whole number literal | real literal |
   string literal | pointer literal,
constant expression =
   expression,
actual parameters =
   left parenthesis, [actual parameter list], right parenthesis,
actual parameter list =
   actual parameter, {comma, actual parameter},
actual parameter =
   variable designator | expression | type parameter,
type parameter =
   type identifier,
   -}
