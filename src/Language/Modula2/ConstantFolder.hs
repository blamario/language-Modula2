{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes,
             ScopedTypeVariables, TemplateHaskell, TypeFamilies, UndecidableInstances #-}

module Language.Modula2.ConstantFolder where

import Control.Applicative (liftA2, ZipList(ZipList, getZipList))
import Control.Arrow (first)
import Control.Monad (join)
import Data.Bits (shift)
import Data.Char (chr, ord, toUpper)
import Data.Functor.Identity (Identity(..))
import Data.Int (Int32)
import Data.Foldable (fold)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..))
import qualified Data.Text as Text
import Foreign.Storable (sizeOf)
import Language.Haskell.TH (appT, conT, varT, varE, newName)

import qualified Rank2
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Full.TH
import qualified Transformation.AG as AG
import Transformation.AG (Attribution(..), Atts, Inherited(..), Synthesized(..), Semantics)

import qualified Language.Modula2.Abstract as Abstract
import qualified Language.Modula2.AST as AST

foldConstants :: (Abstract.Modula2 l, Abstract.Nameable l,
                  Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
                  Abstract.Expression l ~ AST.Expression l,
                  Atts (Inherited ConstantFold) (Abstract.Block l l Sem Sem) ~ InhCF l,
                  Atts (Inherited ConstantFold) (Abstract.Definition l l Sem Sem) ~ InhCF l,
                  Atts (Inherited ConstantFold) (Abstract.Expression l l Sem Sem) ~ InhCF l,
                  Atts (Synthesized ConstantFold) (Abstract.Block l l Sem Sem) ~ SynCFMod' l (Abstract.Block l l),
                  Atts (Synthesized ConstantFold) (Abstract.Definition l l Sem Sem) ~ SynCFMod' l (Abstract.Definition l l),
                  Atts (Synthesized ConstantFold) (Abstract.Expression l l Sem Sem) ~ SynCFExp l,
                  Full.Functor ConstantFold (Abstract.Block l l),
                  Full.Functor ConstantFold (Abstract.Declaration l l),
                  Full.Functor ConstantFold (Abstract.Definition l l),
                  Full.Functor ConstantFold (Abstract.Expression l l),
                  Full.Functor ConstantFold (Abstract.StatementSequence l l),
                  Deep.Functor ConstantFold (Abstract.Declaration l l),
                  Deep.Functor ConstantFold (Abstract.Expression l l),
                  Deep.Functor ConstantFold (Abstract.StatementSequence l l))
              => Environment l -> AST.Module l l Placed Placed -> AST.Module l l Placed Placed
foldConstants predef aModule =
   snd $ moduleFolded $
   syn (Transformation.apply ConstantFold (0, ConstantFold Deep.<$> aModule)
        `Rank2.apply`
        Inherited (InhCF predef undefined))

type Environment l = Map (Abstract.QualIdent l) (Maybe (Abstract.Value l l ((,) Int) ((,) Int)))

newtype Modules l f' f = Modules {getModules :: Map AST.Ident (f (AST.Module l l f' f'))}

data ConstantFold = ConstantFold

type Sem = Semantics ConstantFold

data ConstantFoldSyn l = ConstantFoldSyn (InhCF l)

instance Transformation.Transformation ConstantFold where
   type Domain ConstantFold = Placed
   type Codomain ConstantFold = Semantics ConstantFold

instance Transformation.Transformation (ConstantFoldSyn l) where
   type Domain (ConstantFoldSyn l) = Semantics ConstantFold
   type Codomain (ConstantFoldSyn l) = Placed

instance (Atts (Synthesized ConstantFold) (f ((,) Int) ((,) Int)) ~ SynCF' f,
          Atts (Inherited ConstantFold) (f ((,) Int) ((,) Int)) ~ InhCF l) =>
         Transformation.At (ConstantFoldSyn l) (f ((,) Int) ((,) Int)) where
   ConstantFoldSyn inheritance $ f = folded (syn $ Rank2.apply f $ Inherited inheritance)

data InhCFRoot l = InhCFRoot{rootEnv :: Environment l}

data InhCF l = InhCF{env           :: Environment l,
                     currentModule :: AST.Ident}

data SynCF a = SynCF{folded :: (Int, a)}

data SynCFMod l a = SynCFMod{moduleEnv    :: Environment l,
                             moduleFolded :: (Int, a)}

data SynCFExp l = SynCFExp{foldedExp   :: (Int, AST.Expression l l ((,) Int) ((,) Int)),
                           foldedValue :: Maybe (AST.Value l l ((,) Int) ((,) Int))}

data SynCFRoot a = SynCFRoot{modulesFolded :: a}

-- * Modules instances, TH candidates
instance (Transformation.Transformation t, Functor (Transformation.Domain t), Deep.Functor t (AST.Module l l),
          Transformation.At t (AST.Module l l (Transformation.Codomain t) (Transformation.Codomain t))) =>
         Deep.Functor t (Modules l) where
   t <$> ~(Modules ms) = Modules (mapModule <$> ms)
      where mapModule m = t Transformation.$ ((t Deep.<$>) <$> m)

instance Rank2.Functor (Modules l f') where
   f <$> ~(Modules ms) = Modules (f <$> ms)

instance Rank2.Apply (Modules l f') where
   ~(Modules fs) <*> ~(Modules ms) = Modules (Map.intersectionWith Rank2.apply fs ms)

-- * Boring attribute types
type instance Atts (Synthesized ConstantFold) (Modules l _ _) = SynCFRoot (Modules l ((,) Int) Identity)
type instance Atts (Synthesized ConstantFold) (AST.Module l l _ _) = SynCFMod' l (AST.Module l l)
type instance Atts (Synthesized ConstantFold) (AST.Block l l _ _) = SynCFMod' l (AST.Block l l)
type instance Atts (Synthesized ConstantFold) (AST.Declaration full l l _ _) = SynCFMod' l (AST.Declaration full l l)
type instance Atts (Synthesized ConstantFold) (AST.ProcedureHeading l l _ _) = SynCF' (AST.ProcedureHeading l l)
type instance Atts (Synthesized ConstantFold) (AST.FormalParameters l l _ _) = SynCF' (AST.FormalParameters l l)
type instance Atts (Synthesized ConstantFold) (AST.FPSection l l _ _) = SynCF' (AST.FPSection l l)
type instance Atts (Synthesized ConstantFold) (AST.Type l l _ _) = SynCF' (AST.Type l l)
type instance Atts (Synthesized ConstantFold) (AST.FieldList l l _ _) = SynCF' (AST.FieldList l l)
type instance Atts (Synthesized ConstantFold) (AST.StatementSequence l l _ _) = SynCF' (AST.StatementSequence l l)
type instance Atts (Synthesized ConstantFold) (AST.Expression l l _ _) = SynCFExp l
type instance Atts (Synthesized ConstantFold) (AST.Element l l _ _) = SynCF' (AST.Element l l)
type instance Atts (Synthesized ConstantFold) (AST.Value l l _ _) = SynCF' (AST.Value l l)
type instance Atts (Synthesized ConstantFold) (AST.Designator l l _ _) =
   SynCF (AST.Designator l l ((,) Int) ((,) Int), Maybe (AST.Value l l ((,) Int) ((,) Int)))
type instance Atts (Synthesized ConstantFold) (AST.Statement l l _ _) = SynCF' (AST.Statement l l)
type instance Atts (Synthesized ConstantFold) (AST.Case l l _ _) = SynCF' (AST.Case l l)
type instance Atts (Synthesized ConstantFold) (AST.CaseLabels l l _ _) = SynCF' (AST.CaseLabels l l)
type instance Atts (Synthesized ConstantFold) (AST.ConditionalBranch l l _ _) = SynCF' (AST.ConditionalBranch l l)
type instance Atts (Synthesized ConstantFold) (AST.Variant l l _ _) = SynCF' (AST.Variant l l)

type instance Atts (Inherited ConstantFold) (Modules l _ _) = InhCFRoot l
type instance Atts (Inherited ConstantFold) (AST.Module l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Declaration full l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.ProcedureHeading l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Block l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.FormalParameters l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.FPSection l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Type l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.FieldList l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.StatementSequence l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Expression l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Element l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Value l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Designator l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Statement l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Case l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.CaseLabels l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.ConditionalBranch l l _ _) = InhCF l
type instance Atts (Inherited ConstantFold) (AST.Variant l l _ _) = InhCF l

type SynCF' node = SynCF (node ((,) Int) ((,) Int))
type SynCFMod' l node = SynCFMod l (node ((,) Int) ((,) Int))

-- * Rules

instance Ord (Abstract.QualIdent l) => Attribution ConstantFold (Modules l) Sem ((,) Int) where
   attribution ConstantFold (_, Modules self) (Inherited inheritance, Modules ms) =
     (Synthesized SynCFRoot{modulesFolded= Modules (pure . snd . moduleFolded . syn <$> ms)},
      Modules (Map.mapWithKey moduleInheritance self))
     where moduleInheritance name mod = Inherited InhCF{env= rootEnv inheritance <> foldMap (moduleEnv . syn) ms,
                                                        currentModule= name}

instance (Abstract.Modula2 l, Abstract.Nameable l, Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
          Abstract.Expression l ~ AST.Expression l,
          Atts (Synthesized ConstantFold) (Abstract.Block l l Sem Sem) ~ SynCFMod' l (Abstract.Block l l),
          Atts (Synthesized ConstantFold) (Abstract.Definition l l Sem Sem) ~ SynCFMod' l (Abstract.Definition l l),
          Atts (Synthesized ConstantFold) (Abstract.Expression l l Sem Sem) ~ SynCFExp l,
          Atts (Inherited ConstantFold) (Abstract.Block l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.Definition l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.Expression l l Sem Sem) ~ InhCF l) =>
         Attribution ConstantFold (AST.Module l l) Sem ((,) Int) where
   attribution ConstantFold (_, mod) (Inherited inheritance, mod') =
      case (mod, mod') of
        (AST.DefinitionModule moduleName imports exports _definitions,
         AST.DefinitionModule _ _ _ definitions) ->
           (Synthesized SynCFMod{moduleEnv= foldMap (moduleEnv . syn) definitions,
                                 moduleFolded= (0, AST.DefinitionModule moduleName imports exports
                                                                        (moduleFolded . syn <$> definitions))},
            AST.DefinitionModule moduleName imports exports (pure $ Inherited inheritance))
        (AST.ImplementationModule moduleName _priority imports _block,
         AST.ImplementationModule _ priority _ block) ->
           (Synthesized SynCFMod{moduleEnv= mempty,
                                 moduleFolded= (0, AST.ImplementationModule moduleName (foldedExp . syn <$> priority)
                                                                            imports (moduleFolded $ syn block))},
            AST.ImplementationModule moduleName (pure $ Inherited $ localEnv block) imports (Inherited
                                                                                             $ localEnv block))
        (AST.ProgramModule moduleName _priority imports _block,
         AST.ProgramModule _ priority _ block) ->
           (Synthesized SynCFMod{moduleEnv= mempty,
                                 moduleFolded= (0, AST.ProgramModule moduleName (foldedExp . syn <$> priority)
                                                                     imports (moduleFolded $ syn block))},
            AST.ProgramModule moduleName (pure $ Inherited $ localEnv block) imports (Inherited $ localEnv block))
      where localEnv block = InhCF (moduleEnv (syn block) `Map.union` env inheritance) (currentModule inheritance)

instance (Abstract.Modula2 l, Abstract.Nameable l, Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
          Abstract.Expression l ~ AST.Expression l,
          Atts (Inherited ConstantFold) (Abstract.StatementSequence l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.Declaration l l Sem Sem) ~ InhCF l,
          Atts (Synthesized ConstantFold) (Abstract.Declaration l l Sem Sem) ~ SynCFMod' l (Abstract.Declaration l l),
          Atts (Synthesized ConstantFold) (Abstract.StatementSequence l l Sem Sem)
          ~ SynCF' (Abstract.StatementSequence l l)) =>
         Attribution ConstantFold (AST.Block l l) Sem ((,) Int) where
   bequest ConstantFold (pos, block) inheritance _ = AG.passDown (Inherited inheritance) block
   synthesis ConstantFold (pos, AST.Block{}) _ (AST.Block decls stats) =
      SynCFMod{moduleEnv= fold (moduleEnv . syn <$> decls),
               moduleFolded = (pos,
                               AST.Block (moduleFolded . syn <$> decls) (folded . syn <$> stats))}

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Abstract.Expression l ~ AST.Expression l, Abstract.Value l ~ AST.Value l,
          Atts (Inherited ConstantFold) (Abstract.Declaration l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.Type l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.Block l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.ProcedureHeading l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.FormalParameters l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.ConstExpression l l Sem Sem) ~ InhCF l,
          Atts (Synthesized ConstantFold) (Abstract.Declaration l l Sem Sem) ~ SynCFMod' l (Abstract.Declaration l l),
          Atts (Synthesized ConstantFold) (Abstract.Type l l Sem Sem) ~ SynCF' (Abstract.Type l l),
          Atts (Synthesized ConstantFold) (Abstract.ProcedureHeading l l Sem Sem)
          ~ SynCF' (Abstract.ProcedureHeading l l),
          Atts (Synthesized ConstantFold) (Abstract.FormalParameters l l Sem Sem)
          ~ SynCF' (Abstract.FormalParameters l l),
          Atts (Synthesized ConstantFold) (Abstract.Block l l Sem Sem) ~ SynCFMod' l (Abstract.Block l l),
          Atts (Synthesized ConstantFold) (Abstract.ConstExpression l l Sem Sem) ~ SynCFExp l) =>
         Attribution ConstantFold (AST.Declaration full l l) Sem ((,) Int) where
   bequest ConstantFold (pos, d) inheritance _ = AG.passDown (Inherited inheritance) d
   synthesis ConstantFold (pos, AST.ConstantDeclaration namedef _) _ (AST.ConstantDeclaration _ expression) =
      SynCFMod{moduleEnv= Map.singleton (Abstract.nonQualIdent name) val,
               moduleFolded = (pos,
                               AST.ConstantDeclaration namedef $
                               maybe (foldedExp $ syn expression) ((,) pos . Abstract.literal . (,) pos) val)}
      where name = Abstract.getIdentDefName namedef
            val = foldedValue (syn expression)
   synthesis ConstantFold (pos, AST.TypeDeclaration namedef _) _ (AST.TypeDeclaration _ definition) =
      SynCFMod{moduleEnv= mempty,
               moduleFolded = (pos, AST.TypeDeclaration namedef (folded $ syn definition))}
   synthesis ConstantFold (pos, AST.OpaqueTypeDeclaration namedef) _ (AST.OpaqueTypeDeclaration _) =
      SynCFMod{moduleEnv= mempty,
               moduleFolded = (pos, AST.OpaqueTypeDeclaration namedef)}
   synthesis ConstantFold (pos, AST.VariableDeclaration names _declaredType) _
             (AST.VariableDeclaration _names declaredType) =
      SynCFMod{moduleEnv= mempty,
               moduleFolded= (pos, AST.VariableDeclaration names (folded $ syn declaredType))}
   synthesis ConstantFold (pos, _) _ (AST.ProcedureDeclaration heading body) =
      SynCFMod{moduleEnv= mempty,
               moduleFolded= (pos, AST.ProcedureDeclaration (folded $ syn heading) (moduleFolded $ syn body))}
   synthesis ConstantFold (pos, AST.ModuleDeclaration name _priority imports exports _body)
                        _ (AST.ModuleDeclaration _name priority _imports _exports body) =
      SynCFMod{moduleEnv= moduleEnv (syn body),
               moduleFolded= (pos, AST.ModuleDeclaration name (foldedExp . syn <$> priority) imports exports
                                                         (moduleFolded $ syn body))}

instance (Abstract.CoWirthy l, Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Abstract.Expression l ~ AST.Expression l, Abstract.Value l ~ AST.Value l,
          Atts (Inherited ConstantFold) (Abstract.Expression l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.Element l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.Designator l l Sem Sem) ~ InhCF l,
          Atts (Synthesized ConstantFold) (Abstract.Expression l l Sem Sem) ~ SynCFExp l,
          Atts (Synthesized ConstantFold) (Abstract.Element l l Sem Sem) ~ SynCF' (Abstract.Element l l),
          Atts (Synthesized ConstantFold) (Abstract.Designator l l Sem Sem)
          ~ SynCF (Abstract.Designator l l ((,) Int) ((,) Int), Maybe (Abstract.Value l l ((,) Int) ((,) Int)))) =>
         Attribution ConstantFold (AST.Expression l l) Sem ((,) Int) where
   bequest ConstantFold (pos, e) inheritance _ = AG.passDown (Inherited inheritance) e
   synthesis ConstantFold (pos, AST.Relation op _ _) _ (AST.Relation _op left right) =
      case join (compareValues <$> foldedValue (syn left) <*> foldedValue (syn right))
      of Just value -> SynCFExp{foldedExp= (pos, Abstract.literal (pos, value)),
                                foldedValue= Just value}
         Nothing -> SynCFExp{foldedExp= (pos, AST.Relation op (foldedExp $ syn left) (foldedExp $ syn right)),
                             foldedValue= Nothing}
      where compareValues (AST.Boolean l) (AST.Boolean r)   = relate op (compare l r)
            compareValues (AST.Integer l) (AST.Integer r)   = relate op (compare l r)
            compareValues (AST.Real l) (AST.Real r)         = relate op (compare l r)
            compareValues (AST.Integer l) (AST.Real r)      = relate op (compare (fromIntegral l) r)
            compareValues (AST.Real l) (AST.Integer r)      = relate op (compare l (fromIntegral r))
            compareValues (AST.CharCode l) (AST.CharCode r) = relate op (compare l r)
            compareValues (AST.String l) (AST.String r)     = relate op (compare l r)
            compareValues (AST.CharCode l) (AST.String r)   = relate op (compare (Text.singleton $ chr l) r)
            compareValues (AST.String l) (AST.CharCode r)   = relate op (compare l (Text.singleton $ chr r))
            compareValues _ _                               = Nothing
            relate Abstract.Equal EQ          = Just Abstract.true
            relate Abstract.Equal _           = Just Abstract.false
            relate Abstract.Unequal EQ        = Just Abstract.false
            relate Abstract.Unequal _         = Just Abstract.true
            relate Abstract.Less LT           = Just Abstract.true
            relate Abstract.Less _            = Just Abstract.false
            relate Abstract.LessOrEqual GT    = Just Abstract.false
            relate Abstract.LessOrEqual _     = Just Abstract.true
            relate Abstract.Greater GT        = Just Abstract.true
            relate Abstract.Greater _         = Just Abstract.false
            relate Abstract.GreaterOrEqual LT = Just Abstract.false
            relate Abstract.GreaterOrEqual _  = Just Abstract.true
            relate Abstract.In _              = Nothing
   synthesis ConstantFold (pos, _) _ (AST.Positive expr) =
      case foldedValue (syn expr)
      of Just (AST.Integer n) -> SynCFExp{foldedExp= (pos, AST.Literal (pos, AST.Integer n)),
                                          foldedValue= Just (AST.Integer n)}
         Just (AST.Real n) -> SynCFExp{foldedExp= (pos, AST.Literal (pos, AST.Real n)),
                                       foldedValue= Just (AST.Real n)}
         _ -> SynCFExp{foldedExp= (pos, AST.Positive $ foldedExp $ syn expr),
                       foldedValue= Nothing}
   synthesis ConstantFold (pos, _) _ (AST.Negative expr) =
      case foldedValue (syn expr)
      of Just (AST.Integer n) -> SynCFExp{foldedExp= (pos, AST.Literal (pos, AST.Integer $ negate n)),
                                          foldedValue= Just (AST.Integer $ negate n)}
         Just (AST.Real n) -> SynCFExp{foldedExp= (pos, AST.Literal (pos, AST.Real $ negate n)),
                                       foldedValue= Just (AST.Real $ negate n)}
         _ -> SynCFExp{foldedExp= (pos, AST.Negative $ foldedExp $ syn expr),
                       foldedValue= Nothing}
   synthesis ConstantFold (pos, _) _ (AST.Add left right) =
      foldBinaryArithmetic pos AST.Add (+) (syn left) (syn right)
   synthesis ConstantFold (pos, _) _ (AST.Subtract left right) =
      foldBinaryArithmetic pos AST.Subtract (-) (syn left) (syn right)
   synthesis ConstantFold (pos, _) _ (AST.Or left right) =
      foldBinaryBoolean pos AST.Or (||) (syn left) (syn right)
   synthesis ConstantFold (pos, _) _ (AST.Multiply left right) =
      foldBinaryArithmetic pos AST.Multiply (*) (syn left) (syn right)
   synthesis ConstantFold (pos, _) _ (AST.Divide left right) =
      foldBinaryFractional pos AST.Divide (/) (syn left) (syn right)
   synthesis ConstantFold (pos, _) _ (AST.IntegerDivide left right) =
      foldBinaryInteger pos AST.IntegerDivide div (syn left) (syn right)
   synthesis ConstantFold (pos, _) _ (AST.Modulo left right) =
      foldBinaryInteger pos AST.Modulo mod (syn left) (syn right)
   synthesis ConstantFold (pos, _) _ (AST.And left right) =
      foldBinaryBoolean pos AST.And (&&) (syn left) (syn right)
   synthesis ConstantFold (pos, _) _ (AST.Not expr) =
      case foldedValue (syn expr)
      of Just (AST.Boolean True) -> SynCFExp{foldedExp= (pos, Abstract.literal (pos, Abstract.false)),
                                             foldedValue= Just Abstract.false}
         Just (AST.Boolean False) -> SynCFExp{foldedExp= (pos, Abstract.literal (pos, Abstract.true)),
                                              foldedValue= Just Abstract.true}
         _ -> SynCFExp{foldedExp= (pos, AST.Not $ foldedExp $ syn expr),
                       foldedValue= Nothing}
   synthesis ConstantFold (pos, AST.Set t _elements) _ (AST.Set _t elements) =
      SynCFExp{foldedExp= (pos, AST.Set t (folded . syn <$> elements)),
               foldedValue= Nothing}
   synthesis ConstantFold (pos, _) _ (AST.Read des) =
      case folded (syn des)
      of (pos', (_, Just val)) -> SynCFExp{foldedExp= (pos, Abstract.literal (pos', val)),
                                           foldedValue= Just val}
         (pos', (des', Nothing)) -> SynCFExp{foldedExp= (pos, AST.Read (pos', des')),
                                             foldedValue= Nothing}
   synthesis ConstantFold (pos, _) _ (AST.FunctionCall fn args) =
      case (snd (snd $ folded $ syn fn), foldedValue . syn <$> getZipList args)
      of (Just (AST.Builtin "CAP"), [Just (AST.String s)])
            | Text.length s == 1, capital <- Text.toUpper s -> literalSynthesis (Abstract.string capital)
         (Just (AST.Builtin "CAP"), [Just (AST.CharCode c)])
            | capital <- ord (toUpper $ chr c) -> literalSynthesis (Abstract.charCode capital)
         (Just (AST.Builtin "CHR"), [Just (AST.Integer code)]) -> literalSynthesis (Abstract.charCode $ fromIntegral code)
         (Just (AST.Builtin "ORD"), [Just (AST.String s)])
            | Text.length s == 1, code <- ord (Text.head s) -> literalSynthesis (Abstract.integer $ toInteger code)
         (Just (AST.Builtin "ORD"), [Just (AST.CharCode code)]) -> literalSynthesis (Abstract.integer $ toInteger code)
         (Just (AST.Builtin "ABS"), [Just (AST.Integer i)]) -> literalSynthesis (Abstract.integer $ abs i)
         (Just (AST.Builtin "ABS"), [Just (AST.Real r)]) -> literalSynthesis (Abstract.real $ abs r)
         (Just (AST.Builtin "ASH"), [Just (AST.Integer i), Just (AST.Integer j)])
            | shifted <- shift i (fromIntegral j) -> literalSynthesis (Abstract.integer shifted)
         (Just (AST.Builtin "TRUNC"), [Just (AST.Real x)]) -> literalSynthesis (Abstract.integer $ floor x)
         (Just (AST.Builtin "FLOAT"), [Just (AST.Integer x)]) -> literalSynthesis (Abstract.real $ fromIntegral x)
         (Just (AST.Builtin "FLOAT"), [Just (AST.Real x)]) -> literalSynthesis (Abstract.real x)
         (Just (AST.Builtin "LEN"), [Just (AST.String s)]) -> literalSynthesis (Abstract.integer $ toInteger $ Text.length s)
         (Just (AST.Builtin "LONG"), [Just (AST.Integer x)]) -> literalSynthesis (Abstract.integer x)
         (Just (AST.Builtin "LONG"), [Just (AST.Real x)]) -> literalSynthesis (Abstract.real x)
         (Just (AST.Builtin "SHORT"), [Just (AST.Integer x)]) -> literalSynthesis (Abstract.integer x)
         (Just (AST.Builtin "SHORT"), [Just (AST.Real x)]) -> literalSynthesis (Abstract.real x)
         (Just (AST.Builtin "ODD"), [Just (AST.Integer x)]) ->
            literalSynthesis (if x `mod` 2 == 1 then Abstract.true else Abstract.false)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "INTEGER")]) -> literalSynthesis (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "LONGINT")]) -> literalSynthesis (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "CARDINAL")]) -> literalSynthesis (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "REAL")]) -> literalSynthesis (Abstract.integer doubleSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "LONGREAL")]) -> literalSynthesis (Abstract.integer doubleSize)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "CHAR")]) -> literalSynthesis (Abstract.charCode 0xff)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "INTEGER")]) -> literalSynthesis (Abstract.integer maxInteger)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "LONGINT")]) -> literalSynthesis (Abstract.integer maxInteger)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "CARDINAL")]) -> literalSynthesis (Abstract.integer maxCardinal)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "BITSET")]) -> literalSynthesis (Abstract.integer maxSet)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "REAL")]) -> literalSynthesis (Abstract.real maxReal)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "LONGREAL")]) -> literalSynthesis (Abstract.real maxReal)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "CHAR")]) -> literalSynthesis (Abstract.charCode 0)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "INTEGER")]) -> literalSynthesis (Abstract.integer minInteger)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "LONGINT")]) -> literalSynthesis (Abstract.integer minInteger)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "CARDINAL")]) -> literalSynthesis (Abstract.integer 0)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "BITSET")]) -> literalSynthesis (Abstract.integer minSet)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "REAL")]) -> literalSynthesis (Abstract.real minReal)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "LONGREAL")]) -> literalSynthesis (Abstract.real minReal)
         _ -> SynCFExp{foldedExp= (pos, AST.FunctionCall (fst <$> folded (syn fn)) (foldedExp . syn <$> args)),
                       foldedValue= Nothing}
      where literalSynthesis value = SynCFExp{foldedExp= (pos, Abstract.literal (pos, value)),
                                              foldedValue= Just value}
   synthesis ConstantFold (pos, _) _ (AST.Literal val) =
      SynCFExp{foldedExp= (pos, AST.Literal (folded $ syn val)),
               foldedValue= Just (snd $ folded $ syn val)}

maxCardinal, maxInteger, minInteger, maxInt32, minInt32, maxSet, minSet :: Integer
maxCardinal = 2 * maxInteger + 1
maxInteger = toInteger (maxBound :: Int)
minInteger = toInteger (minBound :: Int)
maxInt32 = toInteger (maxBound :: Int32)
minInt32 = toInteger (minBound :: Int32)
maxSet = 63
minSet = 0

doubleSize, floatSize, intSize, int32Size :: Integer
doubleSize = toInteger (sizeOf (0 :: Double))
floatSize = toInteger (sizeOf (0 :: Float))
intSize = toInteger (sizeOf (0 :: Int))
int32Size = toInteger (sizeOf (0 :: Int32))

maxReal, minReal :: Double
maxReal = encodeFloat (floatRadix x - 1) (snd (floatRange x) - 1)
   where x = 0 :: Double
minReal = encodeFloat (floatRadix x - 1) (fst (floatRange x))
   where x = 0 :: Double

foldBinaryArithmetic :: forall l f. (f ~ ((,) Int),
                                     Abstract.Expression l ~ AST.Expression l, Abstract.Value l ~ AST.Value l,
                                     Abstract.Wirthy l, Abstract.CoWirthy l) =>
                        Int
                     -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> AST.Expression l l f f)
                     -> (forall n. Num n => n -> n -> n)
                     -> SynCFExp l -> SynCFExp l -> SynCFExp l
foldBinaryArithmetic pos node op l r = case join (foldValues <$> foldedValue l <*> foldedValue r)
                                       of Just v -> SynCFExp{foldedExp= (pos, AST.Literal (pos, v)),
                                                             foldedValue= Just v}
                                          Nothing -> SynCFExp{foldedExp= (pos, node (foldedExp l) (foldedExp r)),
                                                              foldedValue= Nothing}
   where foldValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (AST.Integer l') (AST.Integer r') = Just (AST.Integer $ op l' r')
         foldValues (AST.Real l')    (AST.Real r')    = Just (AST.Real $ op l' r')
         foldValues (AST.Integer l') (AST.Real r')    = Just (AST.Real $ op (fromIntegral l') r')
         foldValues (AST.Real l')    (AST.Integer r') = Just (AST.Real $ op l' (fromIntegral r'))
         foldValues _ _ = Nothing

foldBinaryFractional :: forall l f. (f ~ ((,) Int),
                                     Abstract.Expression l ~ AST.Expression l, Abstract.Value l ~ AST.Value l,
                                     Abstract.Wirthy l, Abstract.CoWirthy l) =>
                        Int
                     -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> AST.Expression l l f f)
                     -> (forall n. Fractional n => n -> n -> n)
                     -> SynCFExp l -> SynCFExp l -> SynCFExp l
foldBinaryFractional pos node op l r = case join (foldValues <$> foldedValue l <*> foldedValue r)
                                       of Just v -> SynCFExp{foldedExp= (pos, AST.Literal (pos, v)),
                                                             foldedValue= Just v}
                                          Nothing -> SynCFExp{foldedExp= (pos, node (foldedExp l) (foldedExp r)),
                                                              foldedValue= Nothing}
   where foldValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (AST.Real l')    (AST.Real r')    = Just (AST.Real $ op l' r')
         foldValues _ _ = Nothing

foldBinaryInteger :: forall l f. (f ~ ((,) Int),
                                  Abstract.Expression l ~ AST.Expression l, Abstract.Value l ~ AST.Value l,
                                  Abstract.Wirthy l, Abstract.CoWirthy l) =>
                        Int
                     -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> AST.Expression l l f f)
                     -> (forall n. Integral n => n -> n -> n)
                     -> SynCFExp l -> SynCFExp l -> SynCFExp l
foldBinaryInteger pos node op l r = case join (foldValues <$> foldedValue l <*> foldedValue r)
                                    of Just v -> SynCFExp{foldedExp= (pos, AST.Literal (pos, v)),
                                                          foldedValue= Just v}
                                       Nothing -> SynCFExp{foldedExp= (pos, node (foldedExp l) (foldedExp r)),
                                                           foldedValue= Nothing}
   where foldValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (AST.Integer l') (AST.Integer r') = Just (AST.Integer $ op l' r')
         foldValues _ _ = Nothing

foldBinaryBoolean :: forall l f. (f ~ ((,) Int),
                                  Abstract.Expression l ~ AST.Expression l, Abstract.Value l ~ AST.Value l,
                                  Abstract.Wirthy l, Abstract.CoWirthy l) =>
                     Int
                  -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> AST.Expression l l f f)
                  -> (Bool -> Bool -> Bool)
                  -> SynCFExp l -> SynCFExp l -> SynCFExp l
foldBinaryBoolean pos node op l r = case join (foldValues <$> foldedValue l <*> foldedValue r)
                                    of Just v -> SynCFExp{foldedExp= (pos, AST.Literal (pos, v)),
                                                          foldedValue= Just v}
                                       Nothing -> SynCFExp{foldedExp= (pos, node (foldedExp l) (foldedExp r)),
                                                           foldedValue= Nothing}
   where foldValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (AST.Boolean l') (AST.Boolean r') = Just (AST.Boolean $ op l' r')
         foldValues _ _ = Nothing

instance (Abstract.CoWirthy l, Abstract.Nameable l, Abstract.Modula2 l, Ord (Abstract.QualIdent l),
          Abstract.Expression l l ((,) Int) ((,) Int) ~ AST.Expression l l ((,) Int) ((,) Int),
          Abstract.Value l l ((,) Int) ((,) Int) ~ AST.Value l l ((,) Int) ((,) Int),
          Atts (Inherited ConstantFold) (Abstract.Expression l l Sem Sem) ~ InhCF l,
          Atts (Inherited ConstantFold) (Abstract.Designator l l Sem Sem) ~ InhCF l,
          Atts (Synthesized ConstantFold) (Abstract.Expression l l Sem Sem) ~ SynCFExp l,
          Atts (Synthesized ConstantFold) (Abstract.Designator l l Sem Sem)
          ~ SynCF (Abstract.Designator l l ((,) Int) ((,) Int), Maybe (Abstract.Value l l ((,) Int) ((,) Int)))) =>
         Attribution ConstantFold (AST.Designator l l) Sem ((,) Int) where
   bequest ConstantFold (pos, d) inheritance _ = AG.passDown (Inherited inheritance) d
   synthesis ConstantFold (pos, AST.Variable q) inheritance _ =
      SynCF{folded= (pos, (AST.Variable q, join (Map.lookup q $ env inheritance)))}
--                                         >>= Abstract.coExpression :: Maybe (AST.Expression l l ((,) Int) ((,) Int))))}
   synthesis ConstantFold (pos, AST.Field _record fieldName) _ (AST.Field record _fieldName) =
      SynCF{folded= (pos, (AST.Field (fmap fst $ folded $ syn record) fieldName, Nothing))}
   synthesis ConstantFold (pos, AST.Index{}) _ (AST.Index array index indexes) =
      SynCF{folded= (pos, (AST.Index (fmap fst $ folded $ syn array)
                                     (foldedExp . syn $ index) (foldedExp . syn <$> indexes), Nothing))}
   synthesis ConstantFold (pos, _) _ (AST.Dereference pointer) =
      SynCF{folded= (pos, (AST.Dereference $ fmap fst $ folded $ syn pointer, Nothing))}

-- * More boring Transformation.Functor instances, TH candidates
instance Ord (Abstract.QualIdent l) => Transformation.At ConstantFold (Modules l Sem Sem) where
   ($) = AG.applyDefault snd

-- * Shortcuts

instance Full.Functor ConstantFold (AST.Value l l) where
   ConstantFold <$> (pos, val) = Rank2.Arrow sem
     where sem _inherited = Synthesized (SynCF (pos, val))

instance Full.Functor (ConstantFoldSyn l) (AST.Declaration full l l) where
  ConstantFoldSyn inheritance <$> sem = moduleFolded (syn $ Rank2.apply sem $ Inherited inheritance)

instance Full.Functor (ConstantFoldSyn l) (AST.Expression l l) where
  ConstantFoldSyn inheritance <$> sem = foldedExp (syn $ Rank2.apply sem $ Inherited inheritance)

instance Full.Functor (ConstantFoldSyn l) (AST.Designator l l) where
  ConstantFoldSyn inheritance <$> sem = fst <$> folded (syn $ Rank2.apply sem $ Inherited inheritance)

-- * Unsafe Rank2 AST instances

type Placed = ((,) Int)

$(do l <- varT  <$> newName "l"
     mconcat <$> mapM (\g-> Transformation.Full.TH.deriveUpFunctor (conT ''ConstantFold) $ conT g `appT` l `appT` l)
        [''AST.Type, ''AST.FieldList,
         ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection,
         ''AST.Expression, ''AST.Element, ''AST.Designator,
         ''AST.Block, ''AST.StatementSequence, ''AST.Statement,
         ''AST.Case, ''AST.CaseLabels, ''AST.ConditionalBranch, ''AST.Variant])

$(do let sem = [t|Semantics ConstantFold|]
     let inst g = [d| instance Attribution ConstantFold ($g l l) Sem ((,) Int) =>
                               Transformation.At ConstantFold ($g l l $sem $sem)
                         where ($) = AG.applyDefault snd |]
     mconcat <$> mapM (inst . conT)
        [''AST.Module, ''AST.Block, ''AST.Expression, ''AST.Designator])

$(do full <- varT  <$> newName "full"
     l <- varT  <$> newName "l"
     Transformation.Full.TH.deriveUpFunctor [t| ConstantFold |] [t| AST.Declaration $full $l $l |])

instance Attribution ConstantFold (AST.Declaration full l l) Sem ((,) Int)
      => Transformation.At ConstantFold (AST.Declaration full l l Sem Sem) where
   ($) = AG.applyDefault snd

$(do let inst g = [d| instance Full.Functor (ConstantFoldSyn l) ($g l l)
                         where ConstantFoldSyn inheritance <$> sem = folded (syn $ Rank2.apply sem $ Inherited inheritance)|]
     mconcat <$> mapM (inst . conT)
        [''AST.Type, ''AST.FieldList, ''AST.FormalParameters, ''AST.FPSection,
         ''AST.StatementSequence, ''AST.Statement,
         ''AST.Case, ''AST.CaseLabels, ''AST.ConditionalBranch, ''AST.Variant])

$(do let sem = [t|Semantics ConstantFold|]
     let inst g = [d| instance Deep.Functor (ConstantFoldSyn l) ($g l l) =>
                               Transformation.At ConstantFold ($g l l $sem $sem)
                         where ConstantFold $ (pos, t) = Rank2.Arrow sem
                                  where sem inherited =
                                           Synthesized (SynCF (pos, ConstantFoldSyn (inh inherited) Deep.<$> t)) |]
     mconcat <$> mapM (inst . conT)
        [''AST.Type, ''AST.FieldList,
         ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection,
         ''AST.StatementSequence, ''AST.Statement,
         ''AST.Case, ''AST.CaseLabels, ''AST.ConditionalBranch, ''AST.Variant,
         ''AST.Element])
