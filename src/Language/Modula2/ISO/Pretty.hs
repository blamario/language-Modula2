{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs, OverloadedStrings, ScopedTypeVariables,
             TypeApplications, TypeFamilies, UndecidableInstances #-}

-- | This module exports the instances of the 'Pretty' type class necessary for printing of an ISO Modula-2 abstract
-- syntax tree.

module Language.Modula2.ISO.Pretty () where

import Control.Applicative (ZipList(ZipList, getZipList))
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity(..))
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty((:|)), fromList, toList)
import qualified Data.Text as Text
import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)

import qualified Language.Oberon.Abstract
import qualified Language.Oberon.AST
import qualified Language.Modula2.Abstract as Abstract
import qualified Language.Modula2.ISO.Abstract as ISO.Abstract
import Language.Modula2.ISO.AST
import Language.Oberon.Pretty (Precedence(Precedence))
import Language.Modula2.Pretty ()
import qualified Language.Modula2.AST as Report

instance (Abstract.Nameable l, Pretty (Abstract.IdentDef l),
          Pretty (Abstract.Export l), Pretty (Abstract.Import l),
          Pretty (Abstract.Type l l Identity Identity),
          Pretty (Abstract.Declaration l l Identity Identity),
          Pretty (Abstract.Expression l l Identity Identity),
          Pretty (Abstract.FormalParameters l l Identity Identity),
          Pretty (Abstract.ProcedureHeading l l Identity Identity),
          Pretty (Abstract.Block l l Identity Identity)) =>
         Pretty (Declaration False Language l Identity Identity) where
   pretty (ProcedureDefinition heading) = pretty heading <> semi
   pretty (ConstantDeclaration ident (Identity expr)) = "CONST" <+> pretty ident <+> "=" <+> pretty expr <> semi
   pretty (TypeDeclaration ident typeDef) = "TYPE" <+> pretty ident <+> "=" <+> pretty typeDef <> semi
   pretty (OpaqueTypeDeclaration ident) = "TYPE" <+> pretty ident <> semi
   pretty (VariableDeclaration idents varType) =
      "VAR" <+> hsep (punctuate comma $ pretty <$> toList idents) <+> colon <+> pretty varType <> semi

instance (Abstract.Nameable l, Pretty (Abstract.IdentDef l),
          Pretty (Abstract.Export l), Pretty (Abstract.Import l),
          Pretty (ISO.Abstract.AddressedIdent l l Identity Identity),
          Pretty (Abstract.Type l l Identity Identity),
          Pretty (Abstract.Declaration l l Identity Identity),
          Pretty (Abstract.Expression l l Identity Identity),
          Pretty (Abstract.FormalParameters l l Identity Identity),
          Pretty (Abstract.ProcedureHeading l l Identity Identity),
          Pretty (Abstract.Block l l Identity Identity)) =>
         Pretty (Declaration True Language l Identity Identity) where
   pretty (AddressedVariableDeclaration var vars varType) =
      "VAR" <+> hsep (punctuate comma $ pretty <$> (var : getZipList vars)) <> colon <+> pretty varType <> semi
   pretty (ForwardProcedureDeclaration heading) = pretty heading <> semi <> "FORWARD" <> semi
   pretty (ModuleDeclaration name priority imports export body) =
      vsep $ intersperse mempty $
      ["MODULE" <+> pretty name <> maybe mempty (brackets . pretty) priority <> semi,
       vsep (pretty <$> imports),
       foldMap pretty export,
       pretty body,
       "END" <+> pretty name <> semi]
   pretty dec = Abstract.maybe3 mempty pretty (Abstract.coDeclaration @Language @(Abstract.WirthySubsetOf Report.Language) dec)

instance Pretty (Abstract.ConstExpression l l Identity Identity) => Pretty (AddressedIdent l l Identity Identity) where
   pretty (AddressedIdent name address) = pretty name <> brackets (pretty address)
   pretty (UnaddressedIdent name) = pretty name

instance (Pretty (Abstract.IdentDef l), Pretty (Abstract.FormalParameters l l Identity Identity),
          Pretty (Abstract.FieldList l l Identity Identity),
          Pretty (Abstract.ConstExpression l l Identity Identity), Pretty (Abstract.Type l l Identity Identity),
          Pretty (Abstract.BaseType l)) => Pretty (Type Language l Identity Identity) where
   pretty (ArrayType dimensions itemType) =
      "ARRAY" <+> hsep (punctuate comma $ pretty . runIdentity <$> getZipList dimensions) <+> "OF" <+> pretty itemType
   pretty (EnumerationType values) = "(" <> hsep (punctuate comma $ toList $ pretty <$> values) <> ")"
   pretty (SubrangeType enumType min max) = foldMap pretty enumType <> "[" <> pretty min <+> ".." <+> pretty max <> "]"
   pretty (SetType memberType) = "SET" <+> "OF" <+> pretty memberType
   pretty (PackedSetType memberType) = "PACKED" <+> "SET" <+> "OF" <+> pretty memberType
   pretty (RecordType fields) = vsep ["RECORD",
                                       indent 3 (vsep $ punctuate semi $ pretty <$> getZipList fields),
                                       "END"]
   pretty (ProcedureType parameters) = "PROCEDURE" <+> adjust (pretty parameters)
      where adjust = pretty . Text.replace " : " "" . Text.replace ";" "," . renderStrict . layoutCompact
   pretty ty = Abstract.maybe3 mempty pretty (Abstract.coType @Language @(Abstract.WirthySubsetOf Report.Language) ty)

instance (Pretty (Abstract.IdentDef l), Pretty (Abstract.QualIdent l), Pretty (Abstract.Type l l Identity Identity),
          Pretty (Abstract.Value l l Identity Identity),
          Pretty (Abstract.FieldList l l Identity Identity), Pretty (Abstract.Variant l l Identity Identity)) =>
         Pretty (Report.FieldList Language l Identity Identity) where
   pretty fl = pretty (coerce fl :: Report.FieldList Report.Language l Identity Identity)

instance (Pretty (Abstract.CaseLabels l l Identity Identity), Pretty (Abstract.FieldList l l Identity Identity)) =>
         Pretty (Variant λ l Identity Identity) where
   pretty EmptyVariant = mempty
   pretty (Variant label labels fields) = pretty (Report.Variant label labels fields)

instance (Pretty (Abstract.Declaration l l Identity Identity), Pretty (Abstract.StatementSequence l l Identity Identity)) =>
         Pretty (Block λ l Identity Identity) where
   pretty (Block declarations body) =
      vsep ((indent 3 . pretty <$> getZipList declarations)
            ++ foldMap (\statements-> ["BEGIN", prettyBody statements]) body)
   pretty (ExceptionHandlingBlock declarations body except finally) =
      vsep ((indent 3 . pretty <$> getZipList declarations)
            ++ foldMap (\statements-> ["BEGIN", prettyBody statements]) body
            ++ foldMap (\statements-> ["EXCEPT", prettyBody statements]) except
            ++ foldMap (\statements-> ["FINALLY", prettyBody statements]) finally)

instance (Pretty (Abstract.ConstExpression l l Identity Identity),
          Pretty (Abstract.Designator l l Identity Identity),
          Pretty (Abstract.Case l l Identity Identity),
          Pretty (Abstract.ConditionalBranch l l Identity Identity),
          Pretty (Language.Oberon.Abstract.WithAlternative l l Identity Identity),
          Pretty (Abstract.StatementSequence l l Identity Identity)) =>
         Pretty (Statement Language l Identity Identity) where
   prettyList l = vsep (dropEmptyTail $ punctuate semi $ pretty <$> l)
      where dropEmptyTail
               | not (null l), EmptyStatement <- last l = init
               | otherwise = id
   pretty (For index from to by body) = vsep ["FOR" <+> pretty index <+> ":=" <+> pretty from <+> "TO" <+> pretty to
                                              <+> foldMap ("BY" <+>) (pretty <$> by) <+> "DO",
                                              prettyBody body,
                                              "END"]
   pretty (With designator body) = vsep ["WITH" <+> pretty designator <+> "DO",
                                         prettyBody body,
                                         "END"]
   pretty RetryStatement = "RETRY"
   pretty stat = Abstract.maybe3 mempty pretty (Abstract.coStatement @Language @(Abstract.WirthySubsetOf Report.Language) stat)

instance (Pretty (Precedence (Abstract.Expression l l Identity Identity)),
          Pretty (Abstract.Expression l l Identity Identity),
          Pretty (Abstract.Value l l Identity Identity),
          Pretty (Abstract.Element l l Identity Identity),
          Pretty (ISO.Abstract.Item l l Identity Identity),
          Pretty (Abstract.Designator l l Identity Identity),
          Pretty (Abstract.QualIdent l)) => Pretty (Expression Language l Identity Identity) where
   pretty e = pretty (Precedence 0 e)

instance Pretty (Abstract.Value l l Identity Identity) => Pretty (Report.Value Language l Identity Identity) where
   pretty v = Abstract.maybe3 mempty pretty (Abstract.coValue @Language @(Abstract.WirthySubsetOf Report.Language) v)

instance (Pretty (Abstract.Expression l l Identity Identity)) => Pretty (Item Language l Identity Identity) where
   pretty (Single e) = pretty e
   pretty (Repeated e count) = pretty e <+> "BY" <+> pretty count

instance (Pretty (Precedence (Abstract.Expression l l Identity Identity)),
          Pretty (Abstract.Expression l l Identity Identity),
          Pretty (Abstract.Value l l Identity Identity),
          Pretty (Abstract.Element l l Identity Identity),
          Pretty (ISO.Abstract.Item l l Identity Identity),
          Pretty (Abstract.Designator l l Identity Identity),
          Pretty (Abstract.QualIdent l)) =>
         Pretty (Precedence (Expression Language l Identity Identity)) where
   pretty (Precedence p e@(Remainder left right))
      | p < 4 = pretty (Precedence 4 $ runIdentity left) <+> "REM" <+> pretty (Precedence 4 $ runIdentity right)
      | otherwise = parens (pretty e)
   pretty (Precedence _ (Array itemType items)) =
      foldMap pretty itemType <+> braces (hsep $ punctuate comma $ pretty <$> items)
   pretty (Precedence _ (Record recordType fields)) =
      foldMap pretty recordType <+> braces (hsep $ punctuate comma $ pretty <$> fields)
   pretty (Precedence _ (Set setType elements)) =
      foldMap pretty setType <+> braces (hsep $ punctuate comma $ pretty <$> getZipList elements)
   pretty (Precedence p e) =
      Abstract.maybe3 mempty (pretty . Precedence p) (Abstract.coExpression @Language @(Abstract.WirthySubsetOf Report.Language) e)

instance (Pretty (Abstract.QualIdent l), Pretty (Abstract.Designator l l Identity Identity),
          Pretty (Abstract.Expression l l Identity Identity)) =>
         Pretty (Report.Designator Language l Identity Identity) where
   pretty d = Abstract.maybe3 mempty pretty (Abstract.coDesignator @Language @(Abstract.WirthySubsetOf Report.Language) d)

-- not used at run-time
instance Language.Oberon.Abstract.Oberon Language where
   type WithAlternative Language = Language.Oberon.AST.WithAlternative Language

prettyBody (Identity statements) = indent 3 (pretty statements)
