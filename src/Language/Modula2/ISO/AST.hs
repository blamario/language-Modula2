{-# LANGUAGE DataKinds, DeriveDataTypeable, FlexibleInstances, GADTs, KindSignatures, InstanceSigs,
             MultiParamTypeClasses, UndecidableInstances,
             ScopedTypeVariables, StandaloneDeriving, TemplateHaskell, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | ISO Modula-2 Abstract Syntax Tree definitions

module Language.Modula2.ISO.AST where

import Control.Applicative (ZipList(ZipList, getZipList))
import Control.Monad (forM, mapM)
import Data.Coerce (coerce)
import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import qualified Transformation.Shallow.TH
import qualified Transformation.Deep.TH
import qualified Rank2 as Rank2
import qualified Rank2.TH

import qualified Language.Modula2.Abstract as Abstract
import qualified Language.Modula2.ISO.Abstract as ISO.Abstract
import qualified Language.Modula2.AST as Report
import Language.Modula2.Abstract (Ident)
import Language.Modula2.AST hiding (Language, Block(..), Declaration(..), Expression(..), Statement(..),
                                    Type(..), Variant(..))

-- | Data type representing the Modula-2 language, as specified by the ISO standard.
data Language = Language deriving (Data, Typeable)

instance Abstract.Wirthy Language where
   type Module Language = Module Language
   type Declaration Language = Declaration True Language
   type Type Language = Type Language
   type Statement Language = Statement Language
   type Expression Language = Expression Language
   type Designator Language = Designator Language
   type Value Language = Value Language

   type Import Language = Import Language
   type FieldList Language = FieldList Language
   type ProcedureHeading Language = ProcedureHeading Language
   type FormalParameters Language = FormalParameters Language
   type FPSection Language = FPSection Language
   type Block Language = Block Language
   type StatementSequence Language = StatementSequence Language
   type Case Language = Case Language
   type CaseLabels Language = CaseLabels Language
   type ConditionalBranch Language = ConditionalBranch Language
   type Element Language = Element Language

   type IdentDef Language = Ident
   type QualIdent Language = QualIdent Language

   -- Declaration
   constantDeclaration = ConstantDeclaration
   typeDeclaration = TypeDeclaration
   variableDeclaration = VariableDeclaration
   procedureDeclaration = ProcedureDeclaration

   formalParameters = FormalParameters . ZipList
   fpSection = FPSection
   block = Block . ZipList
   
   fieldList = FieldList

   -- Type
   pointerType = PointerType
   procedureType = ProcedureType
   typeReference = TypeReference

   -- Statement
   assignment = Assignment
   caseStatement scrutinee cases = CaseStatement scrutinee (ZipList cases)
   emptyStatement = EmptyStatement
   exitStatement = Exit
   ifStatement (branch :| branches) = If branch (ZipList branches)
   loopStatement = Loop
   procedureCall proc args = ProcedureCall proc (ZipList <$> args)
   repeatStatement = Repeat
   returnStatement = Return
   whileStatement = While

   conditionalBranch = ConditionalBranch
   caseAlternative (c :| cs) = Case c (ZipList cs)
   labelRange = LabelRange
   singleLabel = SingleLabel
   
   statementSequence = StatementSequence . ZipList

   -- Expression
   add = Add
   subtract = Subtract
   and = And
   or = Or
   divide = Divide
   integerDivide = IntegerDivide
   literal = Literal
   modulo = Modulo
   multiply = Multiply
   functionCall fun args = FunctionCall fun (ZipList args)
   negative = Negative
   positive = Positive
   not = Not
   read = Read
   relation = Relation

   element = Element
   range = Range

   -- Value
   builtin = Builtin
   integer = Integer
   nil = Nil
   real = Real
   string = String
   charCode = CharCode
   false = Boolean False
   true = Boolean True

   -- Designator
   variable = Variable
   field = Field
   index array (index :| indexes) = Index array index (ZipList indexes)
   dereference = Dereference

   -- Identifier
   identDef = id
   nonQualIdent = QualIdent []

instance Abstract.CoWirthy Language where
   type TargetClass Language = ISO.Abstract.Modula2
   coDeclaration (ConstantDeclaration name value) = Abstract.constantDeclaration name value
   coDeclaration (TypeDeclaration name ty) = Abstract.typeDeclaration name ty
   coDeclaration (VariableDeclaration name ty) = Abstract.variableDeclaration name ty
   coDeclaration (ProcedureDeclaration heading body) = Abstract.procedureDeclaration heading body
   coDeclaration (AddressedVariableDeclaration var vars tp) =
      ISO.Abstract.addressedVariableDeclaration (var :| getZipList vars) tp
   coDeclaration (ForwardProcedureDeclaration heading) = ISO.Abstract.forwardProcedureDeclaration heading
   coDeclaration (ModuleDeclaration name priority imports exports body) =
      Abstract.moduleDeclaration name priority imports exports body

   coType (ArrayType dimensions itemType) = Abstract.arrayType (getZipList dimensions) itemType
   coType (EnumerationType names) = Abstract.enumeration names
   coType (PackedSetType base) = ISO.Abstract.packedSetType base
   coType (PointerType destination) = Abstract.pointerType destination
   coType (ProcedureType params) = Abstract.procedureType params
   coType (RecordType fields) = Abstract.recordType (getZipList fields)
   coType (SetType itemType) = Abstract.setType itemType
   coType (SubrangeType base low high) = Abstract.subRange base low high
   coType (TypeReference q) = Abstract.typeReference q

   coStatement EmptyStatement = Abstract.emptyStatement
   coStatement (Assignment destination expression) = Abstract.assignment destination expression
   coStatement (ProcedureCall procedure parameters) = Abstract.procedureCall procedure $ getZipList <$> parameters
   coStatement (If branch elsifs fallback) = Abstract.ifStatement (branch :| getZipList elsifs) fallback
   coStatement (CaseStatement scrutinee cases fallback) =
      Abstract.caseStatement scrutinee (getZipList cases) fallback
   coStatement (While condition body) = Abstract.whileStatement condition body
   coStatement (Repeat body condition) = Abstract.repeatStatement body condition
   coStatement (Loop body) = Abstract.loopStatement body
   coStatement (With designator body) = Abstract.withStatement designator body
   coStatement Exit = Abstract.exitStatement
   coStatement (Return result) = Abstract.returnStatement result
   coStatement (For index from to by body) = Abstract.forStatement index from to by body
   coStatement RetryStatement = ISO.Abstract.retryStatement

   coExpression (Relation op left right) = Abstract.relation op left right
   coExpression (Positive e) = Abstract.positive e
   coExpression (Negative e) = Abstract.negative e
   coExpression (Add left right) = Abstract.add left right
   coExpression (Subtract left right) = Abstract.subtract left right
   coExpression (Or left right) = Abstract.or left right
   coExpression (Multiply left right) = Abstract.multiply left right
   coExpression (Divide left right) = Abstract.divide left right
   coExpression (IntegerDivide left right) = Abstract.integerDivide left right
   coExpression (Modulo left right) = Abstract.modulo left right
   coExpression (And left right) = Abstract.and left right
   coExpression (Literal value) = Abstract.literal value
   coExpression (Read var) = Abstract.read var
   coExpression (FunctionCall function parameters) = Abstract.functionCall function $ getZipList parameters
   coExpression (Not e) = Abstract.not e
   coExpression (Set itemType elements) = Abstract.set itemType (getZipList elements)
   coExpression (Remainder left right) = ISO.Abstract.remainder left right
   coExpression (Array itemType items) = ISO.Abstract.array itemType items
   coExpression (Record tp fields) = ISO.Abstract.record tp fields

   coValue Nil = Abstract.nil
   coValue (Boolean False) = Abstract.false
   coValue (Boolean True) = Abstract.true
   coValue (Builtin name) = Abstract.builtin name
   coValue (Integer n) = Abstract.integer n
   coValue (Real r) = Abstract.real r
   coValue (String s) = Abstract.string s
   coValue (CharCode c) = Abstract.charCode c

   coDesignator (Variable q) = Abstract.variable q
   coDesignator (Field record name) = Abstract.field record name
   coDesignator (Index array index indexes) = Abstract.index array (index :| getZipList indexes)
   coDesignator (Dereference pointer) = Abstract.dereference pointer

instance Abstract.Nameable Language where
   getProcedureName (ProcedureHeading name _) = name
   getIdentDefName = id
   getNonQualIdentName (QualIdent [] name) = Just name
   getNonQualIdentName _ = Nothing

instance Abstract.Modula2 Language where
   type Export Language = Export Language
   type Definition Language = Declaration False Language
   type Variant Language = Variant Language

   -- Module
   definitionModule name imports exports definitions = DefinitionModule name imports exports (ZipList definitions)
   implementationModule = ImplementationModule
   programModule = ProgramModule

   moduleExport = Export
   moduleImport = Import
   
   -- Definition
   constantDefinition = ConstantDeclaration
   typeDefinition = \name-> maybe (OpaqueTypeDeclaration name) (TypeDeclaration name)
   variableDefinition = VariableDeclaration
   procedureDefinition = ProcedureDefinition

   -- Declaration
   moduleDeclaration = ModuleDeclaration

   -- Type
   arrayType = ArrayType . ZipList
   recordType = RecordType . ZipList

   procedureHeading = ProcedureHeading
   caseFieldList n t (variant :| variants) fallback = CaseFieldList n t variant (ZipList variants) (ZipList fallback)
   variant (case1 :| cases) fields = Variant case1 (ZipList cases) (ZipList fields)

   forStatement = For
   withStatement = With

   enumeration = EnumerationType
   subRange = SubrangeType
   setType = SetType
   
   -- Expression
   set memberType members = Set memberType (ZipList members)
   qualIdent = QualIdent

instance ISO.Abstract.Modula2 Language where
   type AddressedIdent Language = AddressedIdent Language
   type Item Language = Item Language

   -- Declaration
   emptyVariant = EmptyVariant
   addressedVariableDeclaration (var :| vars) = AddressedVariableDeclaration var (ZipList vars)
   forwardProcedureDeclaration = ForwardProcedureDeclaration
   exceptionHandlingBlock = ExceptionHandlingBlock . ZipList
   addressedIdent = AddressedIdent
   unaddressedIdent = UnaddressedIdent

   -- Type
   packedSetType = PackedSetType

   -- Statement
   retryStatement = RetryStatement

    -- Expression
   array = Array
   record = Record
   remainder = Remainder

   -- Compound expression
   single = Single
   repeated = Repeated

data Declaration (full :: Bool) λ l (f' :: * -> *) (f :: * -> *) where
   ConstantDeclaration :: Abstract.IdentDef l -> f (Abstract.ConstExpression l l f' f') -> Declaration x λ l f' f
   TypeDeclaration :: Abstract.IdentDef l -> f (Abstract.Type l l f' f') -> Declaration x λ l f' f
   OpaqueTypeDeclaration :: Abstract.IdentDef l -> Declaration False λ l f' f
   VariableDeclaration :: Abstract.IdentList l -> f (Abstract.Type l l f' f') -> Declaration x λ l f' f
   AddressedVariableDeclaration :: f (ISO.Abstract.AddressedIdent l l f' f')
                                -> ZipList (f (ISO.Abstract.AddressedIdent l l f' f'))
                                -> f (Abstract.Type l l f' f')
                                -> Declaration True λ l f' f
   ProcedureDeclaration :: f (Abstract.ProcedureHeading l l f' f') -> f (Abstract.Block l l f' f')
                        -> Declaration True λ l f' f
   ProcedureDefinition :: f (Abstract.ProcedureHeading l l f' f') -> Declaration False λ l f' f
   ForwardProcedureDeclaration :: f (Abstract.ProcedureHeading l l f' f') -> Declaration True λ l f' f
   ModuleDeclaration :: Ident -> Maybe (f (Abstract.Priority l l f' f')) -> [Abstract.Import l]
                     -> Maybe (Abstract.Export l) -> f (Abstract.Block l l f' f') -> Declaration True λ l f' f

deriving instance (Show (Abstract.Export l), Show (Abstract.Import l), Show (f (ISO.Abstract.AddressedIdent l l f' f')),
                   Show (f (Abstract.Type l l f' f')), Show (f (Abstract.ConstExpression l l f' f')),
                   Show (f (Abstract.FormalParameters l l f' f')), Show (f (Abstract.ProcedureHeading l l f' f')),
                   Show (f (Abstract.Block l l f' f')), Show (f (Abstract.Block l l f' f')),
                   Show (Abstract.IdentDef l)) => Show (Declaration x λ l f' f)

data AddressedIdent λ l f' f = AddressedIdent Ident (f (Abstract.ConstExpression l l f' f'))
                             | UnaddressedIdent Ident

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f',
                   Data (f (Abstract.ConstExpression l l f' f'))) => Data (AddressedIdent λ l f' f)
deriving instance (Show (f (Abstract.ConstExpression l l f' f'))) => Show (AddressedIdent λ l f' f)

data Type λ l f' f = TypeReference (Abstract.QualIdent l)
                   | ArrayType (ZipList (f (Abstract.Type l l f' f'))) (f (Abstract.Type l l f' f'))
                   | EnumerationType (Abstract.IdentList l)
                   | SubrangeType (Maybe (Abstract.QualIdent l))
                                  (f (Abstract.ConstExpression l l f' f')) (f (Abstract.ConstExpression l l f' f'))
                   | SetType (f (Abstract.Type l l f' f'))
                   | PackedSetType (f (Abstract.Type l l f' f'))
                   | RecordType (ZipList (f (Abstract.FieldList l l f' f')))
                   | PointerType (f (Abstract.Type l l f' f'))
                   | ProcedureType (Maybe (f (Abstract.FormalParameters l l f' f')))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f',
                   Data (Abstract.QualIdent l), Data (Abstract.IdentList l),
                   Data (f (Abstract.Type l l f' f')), Data (f (Abstract.ConstExpression l l f' f')),
                   Data (f (Abstract.FormalParameters l l f' f')), Data (f (Abstract.FieldList l l f' f'))) =>
                  Data (Type λ l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (Abstract.IdentList l), Show (f (Abstract.Type l l f' f')),
                   Show (f (Abstract.ConstExpression l l f' f')), Show (f (Abstract.FormalParameters l l f' f')),
                   Show (f (Abstract.FieldList l l f' f'))) =>
                  Show (Type λ l f' f)

data Expression λ l f' f = Relation RelOp (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Positive (f (Abstract.Expression l l f' f'))
                         | Negative (f (Abstract.Expression l l f' f'))
                         | Add (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Subtract (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Or (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Multiply (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Divide (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | IntegerDivide (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Modulo (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Remainder (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | And (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Array (Maybe (Abstract.QualIdent l)) [f (ISO.Abstract.Item l l f' f')]
                         | Record (Maybe (Abstract.QualIdent l)) [f (Abstract.Expression l l f' f')]
                         | Set (Maybe (Abstract.QualIdent l)) (ZipList (f (Abstract.Element l l f' f')))
                         | Read (f (Abstract.Designator l l f' f'))
                         | FunctionCall (f (Abstract.Designator l l f' f')) (ZipList (f (Abstract.Expression l l f' f')))
                         | Not (f (Abstract.Expression l l f' f'))
                         | Literal (f (Abstract.Value l l f' f'))

data Item λ l f' f = Single (f (Abstract.Expression l l f' f'))
                   | Repeated (f (Abstract.Expression l l f' f')) (f (Abstract.ConstExpression l l f' f'))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (Abstract.QualIdent l),
                   Data (f (Abstract.Designator l l f' f')), Data (f (Abstract.Element l l f' f')),
                   Data (f (ISO.Abstract.Item l l f' f')), Data (f (Abstract.Value l l f' f')),
                   Data (f (Abstract.Expression l l f' f'))) =>
                  Data (Expression λ l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.Designator l l f' f')),
                   Show (f (Abstract.Element l l f' f')), Show (f (ISO.Abstract.Item l l f' f')),
                   Show (f (Abstract.Value l l f' f')), Show (f (Abstract.Expression l l f' f'))) => Show (Expression λ l f' f)
deriving instance (Eq (Abstract.QualIdent l), Eq (f (Abstract.Designator l l f' f')),
                   Eq (f (Abstract.Element l l f' f')), Eq (f (ISO.Abstract.Item l l f' f')),
                   Eq (f (Abstract.Value l l f' f')), Eq (f (Abstract.Expression l l f' f'))) => Eq (Expression λ l f' f)
deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (f (Abstract.Expression l l f' f')),
                   Data (f (Abstract.Expression l l f' f'))) =>
                  Data (Item λ l f' f)
deriving instance (Show (f (Abstract.Expression l l f' f'))) => Show (Item λ l f' f)
deriving instance (Eq (f (Abstract.Expression l l f' f'))) => Eq (Item λ l f' f)


data Variant λ l f' f =
   Variant (f (Abstract.CaseLabels l l f' f')) (ZipList (f (Abstract.CaseLabels l l f' f')))
           (ZipList (f (Abstract.FieldList l l f' f')))
   | EmptyVariant

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (f (Abstract.CaseLabels l l f' f')),
                   Data (f (Abstract.FieldList l l f' f'))) => Data (Variant λ l f' f)
deriving instance (Show (f (Abstract.CaseLabels l l f' f')), Show (f (Abstract.FieldList l l f' f')))
               => Show (Variant λ l f' f)


data Block λ l f' f = Block (ZipList (f (Abstract.Declaration l l f' f'))) (Maybe (f (Abstract.StatementSequence l l f' f')))
                    | ExceptionHandlingBlock (ZipList (f (Abstract.Declaration l l f' f')))
                                             (Maybe (f (Abstract.StatementSequence l l f' f')))
                                             (Maybe (f (Abstract.StatementSequence l l f' f')))
                                             (Maybe (f (Abstract.StatementSequence l l f' f')))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (f (Abstract.Declaration l l f' f')),
                   Data (f (Abstract.Designator l l f' f')), Data (f (Abstract.Expression l l f' f')),
                   Data (f (Abstract.StatementSequence l l f' f'))) =>
                  Data (Block λ l f' f)
deriving instance (Show (f (Abstract.Declaration l l f' f')), Show (f (Abstract.Designator l l f' f')),
                   Show (f (Abstract.Expression l l f' f')), Show (f (Abstract.StatementSequence l l f' f'))) =>
                  Show (Block λ l f' f)

data Statement λ l f' f = EmptyStatement
                        | Assignment (f (Abstract.Designator l l f' f')) (f (Abstract.Expression l l f' f'))
                        | ProcedureCall (f (Abstract.Designator l l f' f')) (Maybe (ZipList (f (Abstract.Expression l l f' f'))))
                        | If (f (Abstract.ConditionalBranch l l f' f'))
                             (ZipList (f (Abstract.ConditionalBranch l l f' f')))
                             (Maybe (f (Abstract.StatementSequence l l f' f')))
                        | CaseStatement (f (Abstract.Expression l l f' f')) 
                                        (ZipList (f (Abstract.Case l l f' f')))
                                        (Maybe (f (Abstract.StatementSequence l l f' f')))
                        | While (f (Abstract.Expression l l f' f')) (f (Abstract.StatementSequence l l f' f'))
                        | Repeat (f (Abstract.StatementSequence l l f' f')) (f (Abstract.Expression l l f' f'))
                        | For Ident (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f')) 
                              (Maybe (f (Abstract.Expression l l f' f'))) (f (Abstract.StatementSequence l l f' f'))
                        | Loop (f (Abstract.StatementSequence l l f' f'))
                        | With (f (Abstract.Designator l l f' f')) (f (Abstract.StatementSequence l l f' f'))
                        | Exit
                        | Return (Maybe (f (Abstract.Expression l l f' f')))
                        | RetryStatement

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f',
                   Data (f (Abstract.Designator l l f' f')), Data (f (Abstract.Expression l l f' f')),
                   Data (f (Abstract.Case l l f' f')), Data (f (Abstract.ConditionalBranch l l f' f')),
                   Data (f (Abstract.StatementSequence l l f' f'))) => Data (Statement λ l f' f)
deriving instance (Show (f (Abstract.Designator l l f' f')), Show (f (Abstract.Expression l l f' f')),
                   Show (f (Abstract.Case l l f' f')), Show (f (Abstract.ConditionalBranch l l f' f')),
                   Show (f (Abstract.StatementSequence l l f' f'))) => Show (Statement λ l f' f)

$(concat <$>
  (forM [Rank2.TH.deriveFunctor, Rank2.TH.deriveFoldable, Rank2.TH.deriveTraversable,
         Transformation.Shallow.TH.deriveAll, Transformation.Deep.TH.deriveAll] $
   \derive-> mconcat <$> mapM derive
             [''AddressedIdent, ''Block, ''Declaration, ''Expression, ''Item, ''Statement, ''Type, ''Variant]))

$(mconcat <$> mapM Rank2.TH.unsafeDeriveApply
   [''AddressedIdent, ''Block, ''Declaration, ''Type, ''Statement, ''Expression, ''Item, ''Variant])
