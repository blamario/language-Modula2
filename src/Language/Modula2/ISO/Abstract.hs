{-# LANGUAGE DeriveDataTypeable, KindSignatures, PolyKinds, TypeFamilies, TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Modula-2 Finally Tagless Abstract Syntax Tree definitions

module Language.Modula2.ISO.Abstract (Modula2(..)) where

import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import Transformation.Deep (Product)
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
