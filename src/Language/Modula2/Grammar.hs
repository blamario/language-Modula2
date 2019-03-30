module Language.Modula2.Grammar where

{- Adjusted from Report on the Programming Language Modula-2 -}

--ident = letter {letter I digit}.
--number = integer I real.
integer = digit {digit} I octalDigit {octal Digit} ("B" I "C") I digit {hexDigit} "H".
--real = digit {digit} "." {digit} [ScaleFactor].
Scale Factor = "E" ["+" I "-"] digit {digit}.
--hexDigit = digit I "A" I "B" I "C" I "D" I "E" I"F".
--digit = octal Digit I "8" I "9".
octal Digit = "0" I "1" I "2" I "3" I "4" I "5" I "6" 1"7".
string = "'" {character} "'" I '"' {character} '"' .
qualident = ident {"." ident}.
--ConstantDeclaration = ident "=" ConstExpression.
---ConstExpression = SimpleConstExpr [relation SimpleConstExpr].
relation = "=" I "#" I "<>" I "<" I "<=" i ">" I ">=" I IN.
---SimpleConstExpr = ["+" I "-"] ConstTerm {AddOperator ConstTerm}.
--AddOperator = "+" I "-" I OR .
---ConstTerm = ConstFactor {MulOperator ConstFactor}.
--MulOperator = "*" I "/" I DIV  I MOD I AND I "&" .
---ConstFactor = qualident I number I string I set I "(" ConstExpression ")" I NOT ConstFactor.
set = [qualident] "{" [element {"," element}] "}".
--element = ConstExpression [ ".." ConstExpression].
--TypeDeclaration = ident "=" type.
type = SimpleType I ArrayType I RecordType I SetType I PointerType I ProcedureType.
SimpleType = qualident I enumeration I SubrangeType.
enumeration = "(" Identlist ")".
--Identlist = ident {"," ident}.
SubrangeType = "[" ConstExpression ".." ConstExpression "]".
ArrayType = ARRAY SimpleType {"," SimpleType} OF type.
RecordType = RECORD FieldlistSequence END.
--FieldlistSequence = Fieldlist {";" Fieldlist}.
Fieldlist = [Identlist ":" type I CASE [ident ":"] qualident OF variant {"|" variant} [ELSE FieldlistSequence] END].
variant = CaseLabellist ":" FieldlistSequence.
--CaseLabellist = CaseLabels {"," CaseLabels}.
--CaseLabels = ConstExpression [" .. " ConstExpression].
SetType = SET OF SimpleType.
--PointerType = POINTER TO type.
ProcedureType = PROCEDURE [FormaITypelist].
FormalTypelist = "(" [[VAR] FormalType {"," [VAR] FormalType}] ")" [":" qualident].
--VariableDeclaration = Identlist ":" type.
designator = qualident {"." ident I "[" ExpList "]" I "^"}.
--ExpList = expression {"," expression}.
--expression = SimpleExpression [relation SimpleExpression].
--SimpleExpression = ["+" I"_"] term {AddOperator term}.
--term = factor {MuIOperator factor}.
factor = number I string I set I designator [ActuaIParameters] I (" expression ") I NOT factor.
--ActualParameters = "(" [ExpList] ")" .
--statement = [assignment I ProcedureCall I If Statement I CaseStatement
--             I WhileStatement I RepeatStatement I LoopStatement I ForStatement I WithStatement I EXIT I RETURN [expression] ].
--assignment = designator ":=" expression.
--ProcedureCall = designator [ActuaIParameters].
--StatementSequence = statement {";" statement}.
--If Statement = IF expression THEN StatementSequence {ELSIF expression THEN StatementSequence} [ELSE StatementSequence] END.
--CaseStatement = CASE expression OF case {" I" case} [ELSE StatementSequence] END.
case = CaseLabelList ":" StatementSequence.
--WhileStatement = WHILE expression DO StatementSequence END.
--RepeatStatement = REPEAT StatementSequence UNTIL expression.
ForStatement = FOR ident ":=" expression TO expression [BY ConstExpression] DO StatementSequence END.
--LoopStatement = LOOP StatementSequence END.
WithStatement = WITH designator DO StatementSequence END.
ProcedureDeclaration = ProcedureHeading ";" block ident.
ProcedureHeading = PROCEDURE ident [FormaIParameters].
block = {declaration} [BEGIN StatementSequence] END.
declaration = CONST {ConstantDeclaration ";"} I TYPE {TypeDeclaration ";"} I VAR {VariableDeclaration ";"}
              I ProcedureDeclaration ";"  I ModuleDeclaration.
--FormalParameters = "(" [FPSection {";" FPSection}] ")" [":" qualident].
--FPSection = [VAR] IdentList ":" FormalType.
FormalType = [ARRAY OF]  qualident.
ModuleDeclaration = MODULE ident [priority] ";" {import} [export] block ident.
priority = ,. [,. ConstExpression "]".
export = EXPORT [QUALIFIED] IdentList ";".
import = [FROM ident] IMPORT IdentList ";".
DefinitionModule = DEFINITION MODULE ident ";" {import} [export] {definition} END ident ".".
definition = CONST {ConstantDeclaration ";"} I TYPE {ident ["=" type] ";"} I VAR {VariableDeclaration ";"} I ProcedureHeading ";" .
ProgramModule = MODULE ident [priority] ";" {import} block ident "." .
Compilation Unit = DefinitionModule I {IMPLEMENTATION] ProgramModule.
