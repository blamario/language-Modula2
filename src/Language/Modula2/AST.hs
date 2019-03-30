{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, GADTs, DataKinds, KindSignatures, MultiParamTypeClasses, UndecidableInstances,
             ScopedTypeVariables, StandaloneDeriving, TemplateHaskell, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Modula-2 Abstract Syntax Tree definitions

module Language.Modula2.AST (module Language.Modula2.AST,
                             Oberon.Element(..), Oberon.FormalParameters(..), Oberon.FPSection(..),
                             Oberon.ProcedureBody(..), Oberon.StatementSequence(..),
                             Oberon.Case(..), Oberon.CaseLabels(..),
                             Oberon.RelOp(..)) where

import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import Transformation.Deep (Product)
import qualified Transformation.Deep.TH
import qualified Rank2 as Rank2
import qualified Rank2.TH

import qualified Language.Modula2.Abstract as Abstract
import Language.Modula2.Abstract (Ident)
import qualified Language.Oberon.AST as Oberon

data Language = Language deriving (Data, Typeable)

instance Abstract.Wirthy Language where
   type Module Language = Module Language
   type Declaration Language = Declaration True Language
   type Type Language = Type Language
   type Statement Language = Statement Language
   type Expression Language = Expression Language
   type Designator Language = Designator Language

   type Import Language = Import Language
   type FieldList Language = FieldList Language
   type ProcedureHeading Language = ProcedureHeading Language
   type FormalParameters Language = Oberon.FormalParameters Language
   type FPSection Language = Oberon.FPSection Language
   type ProcedureBody Language = Oberon.ProcedureBody Language
   type StatementSequence Language = Oberon.StatementSequence Language
   type Case Language = Oberon.Case Language
   type CaseLabels Language = Oberon.CaseLabels Language
   type Element Language = Oberon.Element Language

   type IdentDef Language = IdentDef Language
   type QualIdent Language = QualIdent Language
   
   -- Declaration
   constantDeclaration = ConstantDeclaration
   typeDeclaration = TypeDeclaration
   variableDeclaration = VariableDeclaration
   procedureDeclaration = ProcedureDeclaration

   formalParameters = Oberon.FormalParameters
   fpSection = Oberon.FPSection
   procedureBody = Oberon.ProcedureBody
   
   fieldList = FieldList
   emptyFieldList = EmptyFieldList

   -- Type
   arrayType = ArrayType
   pointerType = PointerType
   procedureType = ProcedureType
   recordType = RecordType
   typeReference = TypeReference

   -- Statement
   assignment = Assignment
   caseStatement = CaseStatement
   emptyStatement = EmptyStatement
   exitStatement = Exit
   ifStatement = If
   loopStatement = Loop
   procedureCall = ProcedureCall
   repeatStatement = Repeat
   returnStatement = Return
   whileStatement = While

   caseAlternative = Oberon.Case
   emptyCase = Oberon.EmptyCase
   labelRange = Oberon.LabelRange
   singleLabel = Oberon.SingleLabel
   
   statementSequence = Oberon.StatementSequence

   -- Expression
   add = Add
   subtract = Subtract
   and = And
   or = Or
   divide = Divide
   integerDivide = IntegerDivide
   modulo = Modulo
   multiply = Multiply
   functionCall = FunctionCall
   integer = Integer
   negative = Negative
   positive = Positive
   nil = Nil
   not = Not
   read = Read
   real = Real
   relation = Relation
   string = String

   element = Oberon.Element
   range = Oberon.Range

   -- Designator
   variable = Variable
   field = Field
   index = Index
   dereference = Dereference

   -- Identifier
   identDef = IdentDef
   nonQualIdent = QualIdent []

instance Abstract.Nameable Language where
   getProcedureName (ProcedureHeading name _) = name
   getIdentDefName (IdentDef name) = name
   getNonQualIdentName (QualIdent [] name) = Just name
   getNonQualIdentName _ = Nothing

instance Abstract.Modula2 Language where
   type Export Language = Export Language
   type Definition Language = Declaration False Language
   type Block Language = Oberon.ProcedureBody Language
   type Variant Language = Variant Language

   -- Module
   programModule = ProgramModule
   definitionModule = DefinitionModule

   -- Declaration
   moduleDeclaration = ModuleDeclaration
   procedureDefinition = ProcedureDefinition

   procedureHeading = ProcedureHeading
   caseFieldList = CaseFieldList
   variant = Variant
   block = Oberon.ProcedureBody

   forStatement = For
   withStatement = With

   enumeration = EnumerationType
   subRange = SubrangeType
   set = Set
   qualIdent = QualIdent

data Module l f' f = DefinitionModule Ident
                        [Abstract.Import l] (Maybe (Abstract.Export l)) [f (Abstract.Definition l f' f')]
                   | ProgramModule Ident (Maybe (f (Abstract.Priority l f' f')))
                        [Abstract.Import l] (Maybe (f (Abstract.Block l f' f')))

data Import l = Import (Maybe Ident) (Abstract.IdentList l)
data Export l = Export Bool (Abstract.IdentList l)

deriving instance (Typeable l, Typeable f, Typeable f', Data (Abstract.Import l), Data (Abstract.Export l),
                   Data (f (Abstract.Priority l f' f')),
                   Data (f (Abstract.Declaration l f' f')), Data (f (Abstract.Definition l f' f')),
                   Data (f (Abstract.Block l f' f'))) => Data (Module l f' f)
deriving instance (Show (Abstract.Import l), Show (Abstract.Export l), Show (f (Abstract.Priority l f' f')),
                   Show (f (Abstract.Declaration l f' f')), Show (f (Abstract.Definition l f' f')),
                   Show (f (Abstract.Block l f' f'))) => Show (Module l f' f)

data Declaration (full :: Bool) l (f' :: * -> *) (f :: * -> *) where
   ConstantDeclaration :: Abstract.IdentDef l -> f (Abstract.ConstExpression l f' f') -> Declaration x l f' f
   TypeDeclaration :: Abstract.IdentDef l -> f (Abstract.Type l f' f') -> Declaration x l f' f
   VariableDeclaration :: Abstract.IdentList l -> f (Abstract.Type l f' f') -> Declaration x l f' f
   ProcedureDeclaration :: f (Abstract.ProcedureHeading l f' f') -> f (Abstract.ProcedureBody l f' f')
                        -> Declaration True l f' f
   ProcedureDefinition :: f (Abstract.ProcedureHeading l f' f') -> Declaration False l f' f
   ModuleDeclaration :: Ident -> Maybe (f (Abstract.Priority l f' f')) -> [Abstract.Import l] -> f (Abstract.Block l f' f')
                     -> Declaration True l f' f

{-
deriving instance (Data l, Typeable x, Typeable f, Typeable f', Show (Abstract.Import l),
                   Data (Abstract.Import l), Data (f (Abstract.Type l f' f')), Data (f (Abstract.ConstExpression l f' f')),
                   Data (f (Abstract.FormalParameters l f' f')), Data (f (Abstract.ProcedureHeading l f' f')),
                   Data (f (Abstract.ProcedureBody l f' f')), Data (f (Abstract.Block l f' f')),
                   Data (Abstract.IdentDef l)) => Data (Declaration x l f' f)
-}
deriving instance (Show (Abstract.Import l), Show (f (Abstract.Type l f' f')), Show (f (Abstract.ConstExpression l f' f')),
                   Show (f (Abstract.FormalParameters l f' f')), Show (f (Abstract.ProcedureHeading l f' f')),
                   Show (f (Abstract.ProcedureBody l f' f')), Show (f (Abstract.Block l f' f')),
                   Show (Abstract.IdentDef l)) => Show (Declaration x l f' f)

data QualIdent l = QualIdent [Ident] Ident 
   deriving (Data, Eq, Ord, Show)

newtype IdentDef l = IdentDef Ident
   deriving (Data, Eq, Ord, Show)

data Expression l f' f = Relation Oberon.RelOp (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | IsA (f (Abstract.Expression l f' f')) (Abstract.QualIdent l)
                       | Positive (f (Abstract.Expression l f' f'))
                       | Negative (f (Abstract.Expression l f' f'))
                       | Add (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Subtract (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Or (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Multiply (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Divide (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | IntegerDivide (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Modulo (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | And (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Integer Text
                       | Real Text
                       | String Text
                       | Nil 
                       | Set (Maybe (Abstract.QualIdent l)) [f (Abstract.Element l f' f')]
                       | Read (f (Abstract.Designator l f' f'))
                       | FunctionCall (f (Abstract.Designator l f' f')) [f (Abstract.Expression l f' f')]
                       | Not (f (Abstract.Expression l f' f'))

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.QualIdent l),
                   Data (f (Abstract.Designator l f' f')), Data (f (Abstract.Element l f' f')),
                   Data (f (Abstract.Expression l f' f'))) =>
                  Data (Expression l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.Designator l f' f')),
                   Show (f (Abstract.Element l f' f')), Show (f (Abstract.Expression l f' f'))) =>
                  Show (Expression l f' f)
deriving instance (Eq (Abstract.QualIdent l), Eq (f (Abstract.Designator l f' f')), Eq (f (Abstract.Element l f' f')),
                  Eq (f (Abstract.Expression l f' f'))) => Eq (Expression l f' f)

data Designator l f' f = Variable (Abstract.QualIdent l)
                       | Field (f (Abstract.Designator l f' f')) Ident 
                       | Index (f (Abstract.Designator l f' f')) (NonEmpty (f (Abstract.Expression l f' f')))
                       | Dereference (f (Abstract.Designator l f' f'))

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.QualIdent l),
                   Data (f (Abstract.Designator l f' f')), Data (f (Abstract.Expression l f' f'))) =>
                  Data (Designator l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.Designator l f' f')),
                   Show (f (Abstract.Expression l f' f'))) => Show (Designator l f' f)
deriving instance (Eq (Abstract.QualIdent l), Eq (f (Abstract.Designator l f' f')),
                   Eq (f (Abstract.Expression l f' f'))) => Eq (Designator l f' f)

data Type l f' f = TypeReference (Abstract.QualIdent l)
                 | ArrayType [f (Abstract.ConstExpression l f' f')] (f (Abstract.Type l f' f'))
                 | EnumerationType (Abstract.IdentList l)
                 | SubrangeType (f (Abstract.ConstExpression l f' f')) (f (Abstract.ConstExpression l f' f'))
                 | RecordType (Maybe (Abstract.BaseType l)) (NonEmpty (f (Abstract.FieldList l f' f')))
                 | PointerType (f (Abstract.Type l f' f'))
                 | ProcedureType (Maybe (f (Abstract.FormalParameters l f' f')))

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.QualIdent l), Data (Abstract.IdentList l),
                   Data (f (Abstract.Type l f' f')), Data (f (Abstract.ConstExpression l f' f')),
                   Data (f (Abstract.FormalParameters l f' f')), Data (f (Abstract.FieldList l f' f'))) =>
                  Data (Type l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (Abstract.IdentList l), Show (f (Abstract.Type l f' f')),
                   Show (f (Abstract.ConstExpression l f' f')), Show (f (Abstract.FormalParameters l f' f')),
                   Show (f (Abstract.FieldList l f' f'))) =>
                  Show (Type l f' f)

data FieldList l f' f = FieldList (Abstract.IdentList l) (f (Abstract.Type l f' f'))
                      | CaseFieldList (Maybe Ident) (Abstract.QualIdent l) (NonEmpty (f (Abstract.Variant l f' f')))
                                      (NonEmpty (f (Abstract.FieldList l f' f')))
                      | EmptyFieldList

data Variant l f' f = Variant (NonEmpty (f (Abstract.CaseLabels l f' f'))) (NonEmpty (f (Abstract.FieldList l f' f')))

deriving instance (Data l, Typeable f, Typeable f',
                   Data (Abstract.QualIdent l), Data (Abstract.IdentList l), Data (f (Abstract.Type l f' f')),
                   Data (f (Abstract.Expression l f' f')), Data (f (Abstract.Variant l f' f')),
                   Data (f (Abstract.FieldList l f' f'))) => Data (FieldList l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (Abstract.IdentList l), Show (f (Abstract.Type l f' f')),
                   Show (f (Abstract.Expression l f' f')), Show (f (Abstract.Variant l f' f')),
                   Show (f (Abstract.FieldList l f' f'))) => Show (FieldList l f' f)

deriving instance (Data l, Typeable f, Typeable f', Data (f (Abstract.CaseLabels l f' f')),
                   Data (f (Abstract.FieldList l f' f'))) => Data (Variant l f' f)
deriving instance (Show (f (Abstract.CaseLabels l f' f')), Show (f (Abstract.FieldList l f' f')))
               => Show (Variant l f' f)

data ProcedureHeading l f' f = ProcedureHeading Ident (Maybe (f (Abstract.FormalParameters l f' f')))

deriving instance (Data l, Typeable f, Typeable f', Data (f (Abstract.FormalParameters l f' f'))) =>
                  Data (ProcedureHeading l f' f)
deriving instance (Show (f (Abstract.FormalParameters l f' f'))) =>
                  Show (ProcedureHeading l f' f)

data Statement l f' f = EmptyStatement
                      | Assignment (f (Abstract.Designator l f' f')) (f (Abstract.Expression l f' f'))
                      | ProcedureCall (f (Abstract.Designator l f' f')) (Maybe [f (Abstract.Expression l f' f')])
                      | If (NonEmpty (f (Product (Abstract.Expression l) (Abstract.StatementSequence l) f' f')))
                           (Maybe (f (Abstract.StatementSequence l f' f')))
                      | CaseStatement (f (Abstract.Expression l f' f')) 
                                      (NonEmpty (f (Abstract.Case l f' f'))) 
                                      (Maybe (f (Abstract.StatementSequence l f' f')))
                      | While (f (Abstract.Expression l f' f')) (f (Abstract.StatementSequence l f' f'))
                      | Repeat (f (Abstract.StatementSequence l f' f')) (f (Abstract.Expression l f' f'))
                      | For Ident (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f')) 
                            (Maybe (f (Abstract.Expression l f' f'))) (f (Abstract.StatementSequence l f' f'))
                      | Loop (f (Abstract.StatementSequence l f' f'))
                      | With (f (Abstract.Designator l f' f')) (f (Abstract.StatementSequence l f' f'))
                      | Exit
                      | Return (Maybe (f (Abstract.Expression l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f',
                   Data (f (Abstract.Designator l f' f')), Data (f (Abstract.Expression l f' f')),
                   Data (f (Product (Abstract.Expression l) (Abstract.StatementSequence l) f' f')),
                   Data (f (Abstract.Case l f' f')),
                   Data (f (Abstract.StatementSequence l f' f'))) => Data (Statement l f' f)
deriving instance (Show (f (Abstract.Designator l f' f')), Show (f (Abstract.Expression l f' f')),
                   Show (f (Product (Abstract.Expression l) (Abstract.StatementSequence l) f' f')),
                   Show (f (Abstract.Case l f' f')),
                   Show (f (Abstract.StatementSequence l f' f'))) => Show (Statement l f' f)

$(mconcat <$> mapM Transformation.Deep.TH.deriveAll
  [''Module, ''Declaration, ''Type, ''Statement, ''Expression,
   ''Designator, ''FieldList, ''Variant, ''ProcedureHeading])
