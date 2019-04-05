{-# LANGUAGE DeriveDataTypeable, KindSignatures, PolyKinds, TypeFamilies, TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Modula-2 Finally Tagless Abstract Syntax Tree definitions

module Language.Modula2.Abstract (Ident, IdentList, BaseType, ConstExpression, Priority,
                                  Wirthy(..), Nameable(..), Modula2(..), RelOp(..)) where

import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import Transformation.Deep (Product)
import Language.Oberon.Abstract

type Priority l = ConstExpression l

class Wirthy l => Modula2 l where
   type Export l = x | x -> l
   type Definition l = (d :: (* -> *) -> (* -> *) -> *) | d -> l
   type Variant l = (v :: (* -> *) -> (* -> *) -> *) | v -> l
   
   -- Module
   definitionModule :: Ident -> [Import l] -> Maybe (Export l) -> [f (Definition l f' f')] -> Module l f' f
   implementationModule,
      programModule :: Ident -> Maybe (f (Priority l f' f')) -> [Import l] -> f (Block l f' f') -> Module l f' f

   moduleExport :: Bool -> IdentList l -> Export l
   moduleImport :: Maybe Ident -> IdentList l -> Import l

   -- Definition
   constantDefinition :: IdentDef l -> f (ConstExpression l f' f') -> Definition l f' f
   typeDefinition :: IdentDef l -> f (Type l f' f') -> Definition l f' f
   variableDefinition :: IdentList l -> f (Type l f' f') -> Definition l f' f
   procedureDefinition :: f (ProcedureHeading l f' f') -> Definition l f' f

   -- Declaration
   moduleDeclaration :: Ident -> Maybe (f (Priority l f' f'))
                     -> [Import l] -> Maybe (Export l) -> f (Block l f' f') -> Declaration l f' f

   procedureHeading :: Ident -> Maybe (f (FormalParameters l f' f')) -> ProcedureHeading l f' f
   caseFieldList :: Maybe Ident -> QualIdent l -> NonEmpty (f (Variant l f' f')) -> [f (FieldList l f' f')]
                 -> FieldList l f' f
   variant :: NonEmpty (f (CaseLabels l f' f')) -> NonEmpty (f (FieldList l f' f')) -> Variant l f' f

   -- Type
   enumeration :: IdentList l -> Type l f' f
   subRange :: f (ConstExpression l f' f') -> f (ConstExpression l f' f') -> Type l f' f
   arrayType :: [f (Type l f' f')] -> f (Type l f' f') -> Type l f' f
   setType :: f (Type l f' f') -> Type l f' f
   recordType :: NonEmpty (f (FieldList l f' f')) -> Type l f' f

   -- Statement
   withStatement :: f (Designator l f' f') -> f (StatementSequence l f' f') -> Statement l f' f
   forStatement :: Ident -> f (Expression l f' f') -> f (Expression l f' f') -> Maybe (f (Expression l f' f')) 
                -> f (StatementSequence l f' f') 
                -> Statement l f' f

   -- Expression
   set :: Maybe (QualIdent l) -> [f (Element l f' f')] -> Expression l f' f
   qualIdent :: [Ident] -> Ident -> QualIdent l
