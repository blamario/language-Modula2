{-# LANGUAGE DataKinds, DeriveGeneric, DuplicateRecordFields, FlexibleContexts, FlexibleInstances,
             InstanceSigs,
             MultiParamTypeClasses, OverloadedStrings, RankNTypes,
             ScopedTypeVariables, TypeApplications, TypeFamilies, UndecidableInstances #-}

-- | The main export of this module is the function 'foldConstants' that folds the constants in a Modula-2 AST using
-- an attribute grammar. Other exports are helper functions and attribute types that can be reused for other languages
-- or attribute grammars.

module Language.Modula2.ConstantFolder (foldConstants,
                                        ConstantFold, Sem, Environment, InhCF,
                                        SynCF(..), SynCFDesignator(..), SynCFExp(..), SynCFMod(..), SynCFMod') where

import Control.Applicative (liftA2, ZipList(ZipList, getZipList))
import Control.Arrow (first)
import Control.Monad (join)
import Data.Bits (shift)
import Data.Char (chr, ord, toUpper)
import Data.Coerce (Coercible, coerce)
import Data.Functor.Identity (Identity(..))
import Data.Int (Int32)
import Data.Foldable (fold)
import Data.List.NonEmpty (NonEmpty((:|)), toList)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..))
import qualified Data.Text as Text
import Foreign.Storable (sizeOf)
import GHC.Generics (Generic)
import Data.Text.Prettyprint.Doc (Pretty)

import qualified Rank2
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Full.TH
import qualified Transformation.AG as AG
import Transformation.AG (Attribution(..), Atts, Inherited(..), Synthesized(..), Semantics)
import Transformation.AG.Generics (Bequether(..), Synthesizer(..), SynthesizedField(..), Auto(Auto), Mapped(..))

import qualified Language.Modula2.Abstract as Abstract
import qualified Language.Modula2.AST as AST
import Language.Modula2.Grammar (ParsedLexemes(Trailing), Lexeme(WhiteSpace))
import qualified Language.Oberon.Abstract as Oberon.Abstract
import qualified Language.Oberon.AST as Oberon.AST
import qualified Language.Oberon.ConstantFolder as Oberon
import Language.Oberon.ConstantFolder (ConstantFold(ConstantFold), Sem, Environment,
                                       InhCF(..), InhCFRoot(..), SynCF(..), SynCF',
                                       SynCFRoot(..), SynCFMod(..), SynCFDesignator(..), SynCFMod', SynCFExp(..),
                                       anyWhitespace, folded', foldedExp, foldedExp')

-- | Fold the constants in the given collection of Modula-2 modules (a 'Map' of modules keyed by module name). It uses
-- the constant declarations from the modules as well as the given 'Environment' of predefined constants and
-- functions.
--
-- Note that the Modula-2 'AST.Language' satisfies all constraints in the function's type signature.
foldConstants :: forall l. (Abstract.Modula2 l, Abstract.Nameable l,
                            Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
                            Atts (Inherited (Auto ConstantFold)) (Abstract.Block l l Sem Sem) ~ InhCF l,
                            Atts (Inherited (Auto ConstantFold)) (Abstract.Definition l l Sem Sem) ~ InhCF l,
                            Atts (Inherited (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ InhCF l,
                            Atts (Synthesized (Auto ConstantFold)) (Abstract.Block l l Sem Sem)
                            ~ SynCFMod' l (Abstract.Block l l),
                            Atts (Synthesized (Auto ConstantFold)) (Abstract.Block l l Placed Placed)
                            ~ SynCFMod' l (Abstract.Block l l),
                            Atts (Synthesized (Auto ConstantFold)) (Abstract.Definition l l Sem Sem)
                            ~ SynCFMod' l (Abstract.Definition l l),
                            Atts (Synthesized (Auto ConstantFold)) (Abstract.Definition l l Placed Placed)
                            ~ SynCFMod' l (Abstract.Definition l l),
                            Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp l l,
                            Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Placed Placed)
                            ~ SynCFExp l l,
                            Full.Functor (Auto ConstantFold) (Abstract.Block l l),
                            Full.Functor (Auto ConstantFold) (Abstract.Definition l l),
                            Full.Functor (Auto ConstantFold) (Abstract.Expression l l))
              => Environment l -> AST.Module l l Placed Placed -> AST.Module l l Placed Placed
foldConstants predef aModule =
   snd $ getMapped
   $ folded (syn (Transformation.apply (Auto ConstantFold) ((0, Trailing [], 0), Auto ConstantFold Deep.<$> aModule)
                  `Rank2.apply`
                  Inherited (InhCF predef undefined))
             :: SynCFMod' l (AST.Module l l))

newtype Modules l f' f = Modules {getModules :: Map AST.Ident (f (AST.Module l l f' f'))}

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
type instance Atts (Synthesized (Auto ConstantFold)) (Modules l _ _) = SynCFRoot (Modules l Placed Identity)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Module λ l _ _) = SynCFMod' l (AST.Module λ l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Declaration full λ l _ _) = SynCFMod' l (AST.Declaration full λ l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.ProcedureHeading λ l _ _) = SynCF' (AST.ProcedureHeading λ l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Type λ l _ _) = SynCF' (AST.Type λ l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.FieldList λ l _ _) = SynCF' (AST.FieldList λ l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Expression λ l _ _) = SynCFExp λ l
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Designator λ l _ _) = SynCFDesignator l
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Statement λ l _ _) = SynCF' (AST.Statement λ l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Variant λ l _ _) = SynCF' (AST.Variant λ l)

type instance Atts (Inherited (Auto ConstantFold)) (Modules l _ _) = InhCFRoot l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Module λ l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Declaration full λ l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.ProcedureHeading λ l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Type λ l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.FieldList λ l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Expression λ l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Designator λ l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Statement λ l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Variant λ l _ _) = InhCF l

type Placed = (,) (Int, ParsedLexemes, Int)

-- * Rules

instance Ord (Abstract.QualIdent l) => Attribution (Auto ConstantFold) (Modules l) Sem Placed where
   attribution _ (_, Modules self) (Inherited inheritance, Modules ms) =
     (Synthesized SynCFRoot{modulesFolded= Modules (pure . snd . getMapped . foldedModule . syn <$> ms)},
      Modules (Map.mapWithKey moduleInheritance self))
     where moduleInheritance name mod = Inherited InhCF{env= rootEnv inheritance <> foldMap (moduleEnv . syn) ms,
                                                        currentModule= name}
           foldedModule :: SynCFMod' l (AST.Module l l) -> Mapped Placed (AST.Module l l Placed Placed)
           foldedModule = folded

instance (Abstract.Modula2 l, Abstract.Nameable l, k ~ Abstract.QualIdent l, Ord k, Show k,
          v ~ Abstract.Value l l Placed Placed,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Block l l Sem Sem) ~ SynCFMod' l (Abstract.Block l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Definition l l Sem Sem)
          ~ SynCFMod' l (Abstract.Definition l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Definition l l Placed Placed)
          ~ SynCFMod' l (Abstract.Definition l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp l l) =>
         SynthesizedField "moduleEnv" (Map k (Maybe v)) (Auto ConstantFold) (AST.Module l l) Sem Placed where
   synthesizedField _ _ (_, mod) inheritance mod' =
      case (mod, mod') of
        (AST.DefinitionModule{}, AST.DefinitionModule _ _ _ definitions) -> foldMap (moduleEnv . syn) definitions
        _ -> mempty

instance (Abstract.Modula2 l, Abstract.Nameable l, k ~ Abstract.QualIdent l, Ord k, v ~ Abstract.Value l l Placed Placed,
          Abstract.Export l ~ AST.Export l, Abstract.Value l ~ AST.Value l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Declaration l l Sem Sem)
          ~ SynCFMod' l (Abstract.Declaration l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Type l l Sem Sem) ~ SynCF' (Abstract.Type l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.ProcedureHeading l l Sem Sem)
          ~ SynCF' (Abstract.ProcedureHeading l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.FormalParameters l l Sem Sem)
          ~ SynCF' (Abstract.FormalParameters l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Block l l Sem Sem) ~ SynCFMod' l (Abstract.Block l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.ConstExpression l l Sem Sem) ~ SynCFExp l l) =>
         SynthesizedField "moduleEnv" (Map k (Maybe v)) (Auto ConstantFold) (AST.Declaration full l l) Sem Placed where
   synthesizedField _ _ (_, AST.ConstantDeclaration namedef _) _ (AST.ConstantDeclaration _ expression) =
      Map.singleton (Abstract.nonQualIdent $ Abstract.getIdentDefName namedef)
                    ((snd <$>) . foldedValue $ syn expression)
   synthesizedField _ _ (pos, AST.ModuleDeclaration moduleName _priority imports exports _body)
                    _ (AST.ModuleDeclaration _name priority _imports _exports body) =
      foldMap exportedEnv exports
      where exportedEnv (AST.Export qualified names) =
               Map.mapKeysMonotonic qualify (Map.filterWithKey (const . (`elem` exportList)) (moduleEnv $ syn body))
               where exportList = Abstract.qualIdent [] <$> toList names
                     qualify qname
                        | qualified,
                          Just name <- Abstract.getNonQualIdentName qname = Abstract.qualIdent [moduleName] name
                        | otherwise = qname
   synthesizedField _ _ _ _ _ = mempty

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Abstract.Expression λ ~ AST.Expression AST.Language, Abstract.QualIdent λ ~ AST.QualIdent AST.Language,
          Abstract.QualIdent l ~ AST.QualIdent l,
          Abstract.Element l l ~ AST.Element l l,
          Abstract.Value l l ~ AST.Value l l,
          λ ~ AST.Language,
          Pretty (AST.Value l l Identity Identity),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp l l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Element l l Sem Sem) ~ SynCF' (AST.Element l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ SynCFDesignator l) =>
         Synthesizer (Auto ConstantFold) (AST.Expression λ l) Sem Placed where
   synthesis _ (pos, AST.Set t _elements) _ (AST.Set _t elements) =
      SynCFExp{folded= Mapped (pos, Abstract.set t (getMapped . folded' . syn <$> getZipList elements)),
               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Read des) =
      case (designatorValue (syn des), getMapped $ folded (syn des :: SynCFDesignator l))
      of (Just val, _) -> Oberon.literalSynthesis val
         (Nothing, (pos', des')) -> SynCFExp{folded= Mapped (pos, Abstract.read (pos', des')),
                                             foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.FunctionCall fn args)
      | Just (AST.Builtin "TRUNC") <- functionValue,
        [Just (AST.Real x)] <- argValues = fromValue (Abstract.integer $ floor x)
      | Just (AST.Builtin "FLOAT") <- functionValue,
        [Just (AST.Integer x)] <- argValues = fromValue (Abstract.real $ fromIntegral x)
      | Just (AST.Builtin "SIZE") <- functionValue,
        [Just (AST.Builtin "CARDINAL")] <- argValues = fromValue (Abstract.integer $ toInteger $ sizeOf (0 :: Int))
      | Just (AST.Builtin "MAX") <- functionValue,
        [Just (AST.Builtin "CARDINAL")] <- argValues = fromValue (Abstract.integer maxCardinal)
      | Just (AST.Builtin "MAX") <- functionValue,
        [Just (AST.Builtin "BISET")] <- argValues = fromValue (Abstract.integer maxSet)
      | Just (AST.Builtin "MIN") <- functionValue,
        [Just (AST.Builtin "CARDINAL")] <- argValues = fromValue (Abstract.integer 0)
      | Just (AST.Builtin "MIN") <- functionValue,
        [Just (AST.Builtin "BISET")] <- argValues = fromValue (Abstract.integer minSet)
      where fromValue v = Oberon.literalSynthesis (pos, v)
            functionValue = snd <$> designatorValue (syn fn :: SynCFDesignator l)
            argValues = (snd <$>) . foldedValue . syn <$> getZipList args
   synthesis t (pos, self) (InhCF environment currMod) synthesized =
      fromOberon (synthesis t (pos, toOberon self) (InhCF environment currMod) $ toOberon synthesized)
      where fromJust3 :: forall f a (b :: * -> *) (c :: * -> *). Oberon.Abstract.Maybe3 f a b c -> f a b c
            fromJust3 (Oberon.Abstract.Maybe3 Nothing) =
               error ("Modula-2 expression cannot be converted to Oberon at " ++ show pos)
            fromJust3 (Oberon.Abstract.Maybe3 (Just e)) = e
            fromOberon :: SynCFExp Oberon.AST.Language l -> SynCFExp AST.Language l
            fromOberon SynCFExp{folded= Mapped (pos', reportExpression),
                                foldedValue= reportValue} =
               SynCFExp{folded= Mapped (pos', fromJust3
                                              $ Abstract.coExpression @Oberon.AST.Language
                                                @(Abstract.WirthySubsetOf AST.Language) reportExpression),
                        foldedValue= reportValue}
            toOberon :: Abstract.Expression AST.Language l f1 f2 -> Oberon.AST.Expression Oberon.AST.Language l f1 f2
            toOberon = fromJust3 . Abstract.coExpression @AST.Language @(Abstract.WirthySubsetOf Oberon.AST.Language)

maxCardinal, maxInteger, maxSet, minSet :: Integer
maxCardinal = 2 * maxInteger + 1
maxInteger = toInteger (maxBound :: Int)
maxSet = 63
minSet = 0

instance (Abstract.Modula2 l, Ord (Abstract.QualIdent l), v ~ Abstract.Value l l Placed Placed,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ InhCF l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp λ l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ SynCFDesignator l) =>
         SynthesizedField "designatorValue" (Maybe (Placed v)) (Auto ConstantFold) (AST.Designator l l) Sem Placed where
   synthesizedField _ _ (pos, AST.Variable q) inheritance _ = (,) pos <$> join (Map.lookup q $ env inheritance)
   synthesizedField _ _ _ _ _ = Nothing
