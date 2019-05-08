{-# LANGUAGE DeriveDataTypeable, KindSignatures, PolyKinds, TypeFamilies, TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Modula-2 Finally Tagless Abstract Syntax Tree definitions

module Language.Modula2.Abstract (Ident, IdentList, BaseType, ConstExpression, Priority,
                                  Wirthy(..), CoWirthy(..), Nameable(..), Modula2(..), RelOp(..)) where

import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import Transformation.Deep (Product)
import Language.Oberon.Abstract

type Priority l = ConstExpression l

class Wirthy l => Modula2 l where
   type Export l = x | x -> l
   type Definition l = (d :: * -> (* -> *) -> (* -> *) -> *) | d -> l
   type Variant l = (v :: * -> (* -> *) -> (* -> *) -> *) | v -> l
   
   -- Module
   definitionModule :: Ident -> [Import l'] -> Maybe (Export l') -> [f (Definition l' l' f' f')] -> Module l l' f' f
   implementationModule,
      programModule :: Ident -> Maybe (f (Priority l' l' f' f')) -> [Import l'] -> f (Block l' l' f' f')
                    -> Module l l' f' f

   moduleExport :: Bool -> IdentList l -> Export l
   moduleImport :: Maybe Ident -> IdentList l -> Import l

   -- Definition
   constantDefinition :: IdentDef l' -> f (ConstExpression l' l' f' f') -> Definition l l' f' f
   typeDefinition :: IdentDef l' -> Maybe (f (Type l' l' f' f')) -> Definition l l' f' f
   variableDefinition :: IdentList l' -> f (Type l' l' f' f') -> Definition l l' f' f
   procedureDefinition :: f (ProcedureHeading l' l' f' f') -> Definition l l' f' f

   -- Declaration
   moduleDeclaration :: Ident -> Maybe (f (Priority l' l' f' f'))
                     -> [Import l'] -> Maybe (Export l') -> f (Block l' l' f' f') -> Declaration l l' f' f

   procedureHeading :: Ident -> Maybe (f (FormalParameters l' l' f' f')) -> ProcedureHeading l l' f' f
   caseFieldList :: Maybe Ident -> QualIdent l' -> NonEmpty (f (Variant l' l' f' f')) -> [f (FieldList l' l' f' f')]
                 -> FieldList l l' f' f
   variant :: NonEmpty (f (CaseLabels l' l' f' f')) -> NonEmpty (f (FieldList l' l' f' f')) -> Variant l l' f' f

   -- Type
   enumeration :: IdentList l' -> Type l l' f' f
   subRange :: f (ConstExpression l' l' f' f') -> f (ConstExpression l' l' f' f') -> Type l l' f' f
   arrayType :: [f (Type l' l' f' f')] -> f (Type l' l' f' f') -> Type l l' f' f
   setType :: f (Type l' l' f' f') -> Type l l' f' f
   recordType :: NonEmpty (f (FieldList l' l' f' f')) -> Type l l' f' f

   -- Statement
   withStatement :: f (Designator l' l' f' f') -> f (StatementSequence l' l' f' f') -> Statement l l' f' f
   forStatement :: Ident -> f (Expression l' l' f' f') -> f (Expression l' l' f' f')
                -> Maybe (f (Expression l' l' f' f')) -> f (StatementSequence l' l' f' f')
                -> Statement l l' f' f

   -- Expression
   set :: Maybe (QualIdent l') -> [f (Element l' l' f' f')] -> Expression l l' f' f
   qualIdent :: [Ident] -> Ident -> QualIdent l
