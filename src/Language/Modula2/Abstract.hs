{-# LANGUAGE DeriveDataTypeable, KindSignatures, PolyKinds, ScopedTypeVariables,
             TypeApplications, TypeFamilies, TypeFamilyDependencies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Finally Tagless Abstract Syntax Tree definitions for the programming language Modula-2

module Language.Modula2.Abstract (Ident, IdentList, BaseType, ConstExpression, Priority,
                                  Wirthy(..), CoWirthy(..), Nameable(..), Modula2(..),
                                  RelOp(..), WirthySubsetOf(..), Maybe3(..), just3, maybe3, nothing3) where

import Data.Data (Data, Typeable)
import qualified Data.Kind as K (Type)
import Data.List.NonEmpty
import Data.Text (Text)

import Language.Oberon.Abstract

-- | Module priority
type Priority l = ConstExpression l

-- | The finally-tagless associated types and methods relevant to the Modula-2 language. Every non-leaf node type has
-- four type variables:
--
-- * type variable @l@ represents the language of the constructs built by the methods,
-- * @l'@ is the language of the child node constructs,
-- * @f'@ wraps all descendant nodes, except
-- * @f@ wraps all direct children of the node.
class Wirthy l => Modula2 l where
   type Export l = x | x -> l
   type Definition l = (d :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | d -> l
   type Variant l = (v :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | v -> l

   -- Module
   definitionModule :: Ident -> [Import l'] -> Maybe (Export l') -> [f (Definition l' l' f' f')] -> Module l l' f' f
   implementationModule,
      programModule :: Ident -> Maybe (f (Priority l' l' f' f')) -> [Import l'] -> f (Block l' l' f' f')
                    -> Module l l' f' f

   moduleExport :: Bool -> NonEmpty Ident -> Export l
   moduleImport :: Maybe Ident -> NonEmpty Ident -> Import l

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
   variant :: NonEmpty (f (CaseLabels l' l' f' f')) -> [f (FieldList l' l' f' f')] -> Variant l l' f' f

   -- Type
   enumeration :: IdentList l' -> Type l l' f' f
   subRange :: Maybe (QualIdent l') -> f (ConstExpression l' l' f' f') -> f (ConstExpression l' l' f' f')
            -> Type l l' f' f
   arrayType :: [f (Type l' l' f' f')] -> f (Type l' l' f' f') -> Type l l' f' f
   setType :: f (Type l' l' f' f') -> Type l l' f' f
   recordType :: [f (FieldList l' l' f' f')] -> Type l l' f' f

   -- Statement
   withStatement :: f (Designator l' l' f' f') -> f (StatementSequence l' l' f' f') -> Statement l l' f' f
   forStatement :: Ident -> f (Expression l' l' f' f') -> f (Expression l' l' f' f')
                -> Maybe (f (Expression l' l' f' f')) -> f (StatementSequence l' l' f' f')
                -> Statement l l' f' f

   -- Expression
   set :: Maybe (QualIdent l') -> [f (Element l' l' f' f')] -> Expression l l' f' f
   qualIdent :: [Ident] -> Ident -> QualIdent l

instance Wirthy l => Modula2 (WirthySubsetOf l) where
   type Export (WirthySubsetOf l) = Maybe (Export l)
   type Definition (WirthySubsetOf l) = Maybe3 (Definition l)
   type Variant (WirthySubsetOf l) = Maybe3 (Variant l)
   definitionModule = const $ const $ const $ const nothing3
   implementationModule = const $ const $ const $ const nothing3
   programModule = const $ const $ const $ const nothing3

   moduleExport = const $ const Nothing
   moduleImport = const $ const Nothing

   -- Definition
   constantDefinition = const $ const nothing3
   typeDefinition = const $ const nothing3
   variableDefinition = const $ const nothing3
   procedureDefinition = const nothing3

   -- Declaration
   moduleDeclaration = const $ const $ const $ const $ const nothing3

   procedureHeading = const $ const nothing3
   caseFieldList = const $ const $ const $ const nothing3
   variant = const $ const nothing3

   -- Type
   enumeration = const nothing3
   subRange = const $ const $ const nothing3
   arrayType = const $ const nothing3
   setType = const nothing3
   recordType = const nothing3

   -- Statement
   withStatement = const $ const nothing3
   forStatement = const $ const $ const $ const $ const nothing3

   -- Expression
   set = const $ const nothing3
   qualIdent = const $ const Nothing
