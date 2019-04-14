{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs, OverloadedStrings, ScopedTypeVariables,
             TypeApplications, TypeFamilies, UndecidableInstances #-}

-- | This module exports the instances of the 'Pretty' type class necessary for printing of a Modula-2 abstract syntax
-- tree.

module Language.Modula2.Pretty () where

import Data.Functor.Identity (Identity(..))
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty((:|)), fromList, toList)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Numeric (showHex, showOct)
import Transformation.Deep as Deep (Product(Pair))

import qualified Language.Oberon.Abstract
import qualified Language.Oberon.AST
import qualified Language.Modula2.Abstract as Abstract
import Language.Modula2.AST
import Language.Oberon.Pretty (Precedence(Precedence))
import qualified Language.Oberon.AST as Oberon

instance (Pretty (Abstract.Priority l l Identity Identity),
          Pretty (Abstract.Export l),
          Pretty (Abstract.Import l),
          Pretty (Abstract.Declaration l l Identity Identity),
          Pretty (Abstract.Definition l l Identity Identity),
          Pretty (Abstract.Block l l Identity Identity)) =>
         Pretty (Module λ l Identity Identity) where
   pretty (DefinitionModule name imports export declarations) =
      vsep $ intersperse mempty $
      ["DEFINITION" <+> "MODULE" <+> pretty name <> semi,
       vsep (pretty <$> imports),
       foldMap pretty export]
      <> (pretty <$> declarations)
   pretty (ImplementationModule name priority imports body) =
     "IMPLEMENTATION" <+> pretty (ProgramModule name priority imports body)
   pretty (ProgramModule name priority imports body) =
      vsep $ intersperse mempty $
      ["MODULE" <+> pretty name <> maybe mempty (brackets . pretty) priority <> semi,
       vsep (pretty <$> imports)]
      <> [vsep (foldMap (\statements-> ["BEGIN" <#> indent 3 (pretty statements)]) body
                <> ["END" <+> pretty name <> "." <> line])]

instance Pretty (Import l) where
  pretty (Import origin names) =
    maybe id ((<+>) . ("FROM" <+>) . pretty) origin ("IMPORT" <+> hsep (punctuate comma $ toList $ pretty <$> names))
    <> semi

instance Pretty (Export l) where
  pretty (Export qualified names) =
    "EXPORT" <+> (if qualified then ("QUALIFIED" <+>) else id) (hsep $ punctuate comma $ toList $ pretty <$> names)
    <> semi

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
   pretty (VariableDeclaration idents varType) =
      "VAR" <+> hsep (punctuate comma $ pretty <$> toList idents) <+> colon <+> pretty varType <> semi

instance (Abstract.Nameable l, Pretty (Abstract.IdentDef l),
          Pretty (Abstract.Export l), Pretty (Abstract.Import l),
          Pretty (Abstract.Type l l Identity Identity),
          Pretty (Abstract.Declaration l l Identity Identity),
          Pretty (Abstract.Expression l l Identity Identity),
          Pretty (Abstract.FormalParameters l l Identity Identity),
          Pretty (Abstract.ProcedureHeading l l Identity Identity),
          Pretty (Abstract.Block l l Identity Identity)) =>
         Pretty (Declaration True Language l Identity Identity) where
   pretty (ProcedureDeclaration heading body) = vsep [pretty heading <> semi,
                                                      pretty body,
                                                      "END" <+> pretty (Abstract.getProcedureName $ runIdentity heading)
                                                      <> semi]
   pretty (ModuleDeclaration name priority imports export body) =
      vsep $ intersperse mempty $
      ["MODULE" <+> pretty name <> maybe mempty (brackets . pretty) priority <> semi,
       vsep (pretty <$> imports),
       foldMap pretty export,
       pretty body]
   pretty declaration = foldMap pretty (Abstract.coDeclaration declaration
                                        :: Maybe (Oberon.Declaration Oberon.Language l Identity Identity))

instance (Pretty (Precedence (Abstract.Expression l l Identity Identity)),
          Pretty (Abstract.Expression l l Identity Identity),
          Pretty (Abstract.Element l l Identity Identity),
          Pretty (Abstract.Designator l l Identity Identity),
          Pretty (Abstract.QualIdent l)) => Pretty (Expression Language l Identity Identity) where
   pretty (Set ty elements) = pretty ty <+> braces (hsep $ punctuate comma $ pretty <$> elements)
   pretty e = foldMap pretty (Abstract.coExpression e :: Maybe (Oberon.Expression Oberon.Language l Identity Identity))

instance Pretty (Expression Language l Identity Identity) =>
         Pretty (Precedence (Expression Language l Identity Identity)) where
  pretty (Precedence _ e) = pretty e

instance (Pretty (Abstract.QualIdent l), Pretty (Abstract.Designator l l Identity Identity),
          Pretty (Abstract.Expression l l Identity Identity)) => Pretty (Designator Language l Identity Identity) where
   pretty d = foldMap pretty (Abstract.coDesignator d :: Maybe (Oberon.Designator Oberon.Language l Identity Identity))

instance (Pretty (Abstract.FormalParameters l l Identity Identity), Pretty (Abstract.FieldList l l Identity Identity),
          Pretty (Abstract.ConstExpression l l Identity Identity), Pretty (Abstract.Type l l Identity Identity),
          Pretty (Abstract.BaseType l)) => Pretty (Type Language l Identity Identity) where
   pretty (TypeReference q) = pretty q
   pretty (ArrayType dimensions itemType) =
      "ARRAY" <+> hsep (punctuate comma $ pretty . runIdentity <$> dimensions) <+> "OF" <+> pretty itemType
   pretty (RecordType fields) = vsep ["RECORD",
                                       indent 3 (vsep $ punctuate semi $ pretty <$> toList fields),
                                       "END"]
   pretty ty = foldMap pretty (Abstract.coType ty :: Maybe (Oberon.Type Oberon.Language l Identity Identity))

instance Pretty (QualIdent l) where
   pretty (QualIdent modulePath name) = mconcat (punctuate dot $ pretty <$> (modulePath <> [name]))

instance (Pretty (Abstract.IdentDef l), Pretty (Abstract.QualIdent l), Pretty (Abstract.Type l l Identity Identity),
          Pretty (Abstract.FieldList l l Identity Identity), Pretty (Abstract.Variant l l Identity Identity)) =>
         Pretty (FieldList Language l Identity Identity) where
   pretty (CaseFieldList localName name variants fallback) =
     vsep (["CASE" <+> maybe id ((<+>) . (<+> ":") . pretty) localName (pretty name) <+> "OF"]
           <> punctuate "|" (pretty <$> toList variants)
           <> if null fallback then []
              else ["ELSE" <#>
                    indent 3 (vsep $ punctuate semi $ pretty . runIdentity <$> fallback)]
           <> ["END"])
   pretty (FieldList names t) = hsep (punctuate comma $ pretty <$> toList names) <+> ":" <+> pretty t
   pretty EmptyFieldList = mempty

instance (Pretty (Abstract.CaseLabels l l Identity Identity), Pretty (Abstract.FieldList l l Identity Identity)) =>
         Pretty (Variant λ l Identity Identity) where
  pretty (Variant labels fields) = vsep [hsep (punctuate comma $ pretty <$> toList labels) <> ":",
                                         indent 3 (vsep $ punctuate semi $ pretty <$> toList fields)]

instance (Pretty (Abstract.IdentDef l), Pretty (Abstract.FormalParameters l l Identity Identity),
          Pretty (Abstract.Type l l Identity Identity)) =>
         Pretty (ProcedureHeading l l Identity Identity) where
   pretty (ProcedureHeading name parameters) =
      "PROCEDURE" <> pretty name <> pretty parameters

instance (Pretty (Abstract.ConstExpression l l Identity Identity),
          Pretty (Abstract.Designator l l Identity Identity),
          Pretty (Abstract.Case l l Identity Identity),
          Pretty (Language.Oberon.Abstract.WithAlternative l l Identity Identity),
          Pretty (Abstract.StatementSequence l l Identity Identity)) =>
         Pretty (Statement Language l Identity Identity) where
   pretty (For index from to by body) = vsep ["FOR" <+> pretty index <+> ":=" <+> pretty from <+> "TO" <+> pretty to
                                              <+> foldMap ("BY" <+>) (pretty <$> by) <+> "DO",
                                              prettyBody body,
                                              "END"]
   pretty (With designator body) = vsep ["WITH" <+> pretty designator <+> "DO",
                                         prettyBody body,
                                         "END"]
   pretty stat = foldMap pretty (Abstract.coStatement stat :: Maybe (Oberon.Statement Oberon.Language l Identity Identity))

instance Language.Oberon.Abstract.Oberon Language where
   type WithAlternative Language = Language.Oberon.AST.WithAlternative Language
--instance Pretty (Language.Oberon.AST.WithAlternative Language Language Identity Identity) where
--   pretty _ = error "There's no WithAlternative in Modula-2."

prettyBody :: Pretty (Abstract.StatementSequence l l Identity Identity) =>
              Identity (Abstract.StatementSequence l l Identity Identity) -> Doc ann
prettyBody (Identity statements) = indent 3 (pretty statements)

a <#> b = vsep [a, b]
