{-# LANGUAGE DeriveDataTypeable, KindSignatures, PolyKinds,
             TypeFamilies, TypeFamilyDependencies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Modula-2 Finally Tagless Abstract Syntax Tree definitions

module Language.Modula2.ISO.Abstract (Modula2(..)) where

import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import qualified Language.Modula2.Abstract as Report
import Language.Modula2.Abstract hiding (Modula2)

type Priority l = ConstExpression l

class Report.Modula2 l => Modula2 l where
   type AddressedIdent l = (d :: * -> (* -> *) -> (* -> *) -> *) | d -> l
   type Item l = (i :: * -> (* -> *) -> (* -> *) -> *) | i -> l

   -- Declaration
   emptyVariant :: Variant l l' f' f
   addressedVariableDeclaration :: NonEmpty (f (AddressedIdent l' l' f' f')) -> f (Type l' l' f' f')
                                -> Declaration l l' f' f
   forwardProcedureDeclaration :: f (ProcedureHeading l' l' f' f') -> Declaration l l' f' f
   exceptionHandlingBlock :: [f (Declaration l' l' f' f')] -> Maybe (f (StatementSequence l' l' f' f'))
                          -> Maybe (f (StatementSequence l' l' f' f')) -> Maybe (f (StatementSequence l' l' f' f'))
                          -> Block l l' f' f
   addressedIdent :: Ident -> f (ConstExpression l' l' f' f') -> AddressedIdent l l' f' f
   unaddressedIdent :: Ident -> AddressedIdent l l' f' f

   -- Type
   packedSetType :: f (Type l' l' f' f') -> Type l l' f' f

   -- Statement
   retryStatement :: Statement l l' f' f

    -- Expression
   array :: Maybe (QualIdent l') -> [f (Item l' l' f' f')] -> Expression l l' f' f
   record :: Maybe (QualIdent l') -> [f (Expression l' l' f' f')] -> Expression l l' f' f
   remainder :: f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Expression l l' f' f

   -- Compound expression
   single :: f (Expression l' l' f' f') -> Item l l' f' f
   repeated :: f (Expression l' l' f' f') -> f (ConstExpression l' l' f' f') -> Item l l' f' f

instance Wirthy l => Modula2 (WirthySubsetOf l) where
   type AddressedIdent (WirthySubsetOf l) = Maybe3 (AddressedIdent l)
   type Item (WirthySubsetOf l) = Maybe3 (Item l)
   emptyVariant = nothing3
   addressedVariableDeclaration = const $ const nothing3
   forwardProcedureDeclaration = const nothing3
   exceptionHandlingBlock = const $ const $ const $ const nothing3
   addressedIdent = const $ const nothing3
   unaddressedIdent = const nothing3

   -- Type
   packedSetType = const nothing3

   -- Statement
   retryStatement = nothing3

    -- Expression
   array = const $ const nothing3
   record = const $ const nothing3
   remainder = const $ const nothing3

   -- Compound expression
   single = const nothing3
   repeated = const $ const nothing3
