{-# LANGUAGE DataKinds, DuplicateRecordFields, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, OverloadedStrings, RankNTypes,
             ScopedTypeVariables, TemplateHaskell, TypeApplications, TypeFamilies, UndecidableInstances #-}

module Language.Modula2.ISO.ConstantFolder (InhCF, SynCF(..), SynCFDesignator(..), SynCFExp(..), SynCFMod', Environment,
                                            foldConstants) where

import Control.Applicative (liftA2, ZipList(ZipList, getZipList))
import Control.Arrow (first)
import Control.Monad (join)
import Data.Bits (shift)
import Data.Char (chr, ord, toUpper)
import Data.Coerce (Coercible, coerce)
import Data.Functor.Identity (Identity(..))
import Data.Int (Int32)
import Data.Foldable (fold)
import Data.List.NonEmpty (toList)
import Data.Map.Lazy (Map)
import Data.Maybe (fromMaybe)
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
import Transformation.AG.Generics (Bequether(..), Synthesizer(..), SynthesizedField(..), Auto(Auto), Mapped(..))

import qualified Language.Modula2.Abstract as Abstract hiding (Modula2)
import qualified Language.Modula2.ISO.Abstract as Abstract
import qualified Language.Modula2.AST as Report
import qualified Language.Modula2.AST as AST (Ident, QualIdent, Module(..), Export(..),
                                              ProcedureHeading(..), FieldList(..), Designator(..),
                                              Element(..), Value(..))
import qualified Language.Modula2.ISO.AST as AST
import Language.Modula2.Grammar (ParsedLexemes(Trailing))
import Language.Oberon.Abstract (coExpression, coValue)
import qualified Language.Oberon.Abstract as Oberon.Abstract
import qualified Language.Oberon.AST as Oberon.AST
import qualified Language.Oberon.ConstantFolder as Oberon.ConstantFolder
import Language.Oberon.ConstantFolder (ConstantFold(ConstantFold), Sem, Environment,
                                       InhCF(..), InhCFRoot(..), SynCF(..), SynCF',
                                       SynCFRoot(..), SynCFMod(..), SynCFMod', SynCFExp(..),
                                       folded', foldedExp, foldedExp')
import Language.Modula2.ConstantFolder (SynCFDesignator(..), SynCFMod',
                                        foldBinaryArithmetic, foldBinaryBoolean,
                                        foldBinaryFractional, foldBinaryInteger,
                                        maxCardinal, maxInteger, minInteger, maxInt32, minInt32, maxSet, minSet,
                                        doubleSize, floatSize, intSize, int32Size,
                                        maxReal, minReal)

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
   $ folded (syn (Transformation.apply (Auto ConstantFold) ((0, Trailing []), Auto ConstantFold Deep.<$> aModule)
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
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Block λ l _ _) = SynCFMod' l (AST.Block l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Declaration full λ l _ _) = SynCFMod' l (AST.Declaration full l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.AddressedIdent λ l _ _) = SynCF' (AST.AddressedIdent l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Type λ l _ _) = SynCF' (AST.Type l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Expression λ l _ _) = SynCFExp λ l
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Item λ l _ _) = SynCF' (AST.Item l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Statement λ l _ _) = SynCF' (AST.Statement l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Variant λ l _ _) = SynCF' (AST.Variant l l)

type instance Atts (Inherited (Auto ConstantFold)) (Modules l _ _) = InhCFRoot l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Block λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Declaration full λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.AddressedIdent λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Type λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Item λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Expression λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Statement λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Variant λ l _ _) = InhCF λ

wrap :: a -> Mapped Placed a
wrap = Mapped . (,) (0, Trailing [])

-- * Rules

instance Ord (Abstract.QualIdent l) => Attribution (Auto ConstantFold) (Modules l) Sem Placed where
   attribution _ (_, Modules self) (Inherited inheritance, Modules ms) =
     (Synthesized SynCFRoot{modulesFolded= Modules (pure . snd . getMapped . foldedModule . syn <$> ms)},
      Modules (Map.mapWithKey moduleInheritance self))
     where moduleInheritance name mod = Inherited InhCF{env= rootEnv inheritance <> foldMap (moduleEnv . syn) ms,
                                                        currentModule= name}
           foldedModule :: SynCFMod' l (AST.Module l l) -> Mapped Placed (AST.Module l l Placed Placed)
           foldedModule = folded

instance (Abstract.Nameable l, k ~ Abstract.QualIdent l, v ~ Abstract.Value l l Placed Placed, Ord k,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Declaration l l Sem Sem)
          ~ SynCFMod' l (Abstract.Declaration l l)) =>
         SynthesizedField "moduleEnv" (Map k (Maybe v)) (Auto ConstantFold) (AST.Block l l) Sem Placed where
   synthesizedField _ _ (pos, AST.Block{}) _ (AST.Block decls _stats) = Map.unions (moduleEnv . syn <$> decls)
   synthesizedField _ _ (pos, AST.ExceptionHandlingBlock{}) _ (AST.ExceptionHandlingBlock decls _stats _catch _always) =
      Map.unions (moduleEnv . syn <$> decls)

instance (Abstract.Modula2 l, Abstract.Nameable l, k ~ Abstract.QualIdent l, Ord k,
          v ~ Abstract.Value l l Placed Placed,
          Abstract.Export l ~ AST.Export l, Abstract.Value l ~ AST.Value l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Declaration l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Type l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Block l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.ProcedureHeading l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.FormalParameters l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.ConstExpression l l Sem Sem) ~ InhCF l,
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
   synthesizedField _ _ (pos, AST.ConstantDeclaration namedef _) _ (AST.ConstantDeclaration _ expression) =
      Map.singleton (Abstract.nonQualIdent $ Abstract.getIdentDefName namedef) (foldedValue $ syn expression)
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
          Abstract.QualIdent l ~ AST.QualIdent l, Abstract.Value l ~ AST.Value l,
--          Abstract.QualIdent Report.Language ~ AST.QualIdent l,
          Coercible (Abstract.QualIdent Report.Language) (AST.QualIdent l),
          Coercible (Abstract.Value Report.Language Report.Language) (AST.Value l l),
          InhCF l ~ InhCF λ,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Element l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ InhCF l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp l l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Element l l Sem Sem) ~ SynCF' (Abstract.Element l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Item l l Sem Sem) ~ SynCF' (Abstract.Item l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ SynCFDesignator l) =>
         Synthesizer (Auto ConstantFold) (AST.Expression AST.Language l) Sem Placed where
   synthesis _ (pos, _) _ (AST.Remainder left right) = 
      foldBinaryInteger pos Abstract.remainder div (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Array itemType dimensions) =
      SynCFExp{folded= Mapped (pos, Abstract.array itemType (getMapped . folded' . syn <$> dimensions)),
               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Record recordType fields) =
      SynCFExp{folded= Mapped (pos, Abstract.record recordType (foldedExp' . syn <$> fields)),
               foldedValue= Nothing}
   synthesis _ (pos, AST.Set t _elements) _ (AST.Set _t elements) =
      SynCFExp{folded= Mapped (pos, Abstract.set t (getMapped . folded' . syn <$> getZipList elements)),
               foldedValue= Nothing}
   synthesis t (pos, self) (InhCF environment currMod) synthesized =
      fromReport (synthesis t (pos, toReport self) (InhCF (coerce <$> Map.mapKeysMonotonic coerce environment) currMod)
                  $ toReport synthesized)
      where fromJust :: forall f a (b :: * -> *) (c :: * -> *). Oberon.Abstract.Maybe3 f a b c -> f a b c
            fromJust (Oberon.Abstract.Maybe3 Nothing) =
               error ("Modula-2 expression cannot be converted from ISO to Report at " ++ show pos)
            fromJust (Oberon.Abstract.Maybe3 (Just e)) = e
            fromReport :: SynCFExp Report.Language l -> SynCFExp AST.Language l
            fromReport SynCFExp{folded= Mapped (pos', reportExpression),
                                foldedValue= reportValue} =
               SynCFExp{folded= Mapped (pos', fromJust (coExpression @Report.Language
                                                        @(Abstract.WirthySubsetOf AST.Language) reportExpression)),
                        foldedValue= reportValue}
            toReport :: Abstract.Expression AST.Language l f1 f2
                     -> Report.Expression Report.Language l f1 f2
            toReport s = fromJust (coExpression @AST.Language @(Abstract.WirthySubsetOf Report.Language) s)

-- * More boring Transformation.Functor instances, TH candidates
instance Ord (Abstract.QualIdent l) => Transformation.At (Auto ConstantFold) (Modules l Sem Sem) where
   ($) = AG.applyDefault snd

-- * Unsafe Rank2 AST instances

type Placed = (,) (Int, ParsedLexemes)

$(do l <- varT  <$> newName "l"
     mconcat <$> mapM (\g-> Transformation.Full.TH.deriveUpFunctor (conT ''Auto `appT` conT ''ConstantFold) $ conT g `appT` l `appT` l)
        [''AST.Block, ''AST.AddressedIdent, ''AST.Type, ''AST.Expression, ''AST.Statement, ''AST.Item, ''AST.Variant])

$(do let sem = [t|Semantics (Auto ConstantFold)|]
     let inst g = [d| instance Attribution (Auto ConstantFold) ($g l l) Sem Placed =>
                               Transformation.At (Auto ConstantFold) ($g l l $sem $sem)
                         where ($) = AG.applyDefault snd |]
     mconcat <$> mapM (inst . conT)
        [''AST.Block, ''AST.AddressedIdent, ''AST.Type, ''AST.Statement, ''AST.Expression, ''AST.Item, ''AST.Variant])

$(do full <- varT  <$> newName "full"
     l <- varT  <$> newName "l"
     Transformation.Full.TH.deriveUpFunctor [t| (Auto ConstantFold) |] [t| AST.Declaration $full $l $l |])

instance Attribution (Auto ConstantFold) (AST.Declaration full l l) Sem Placed
      => Transformation.At (Auto ConstantFold) (AST.Declaration full l l Sem Sem) where
   ($) = AG.applyDefault snd
