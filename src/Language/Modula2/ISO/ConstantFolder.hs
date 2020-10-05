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
import Data.Coerce (coerce)
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
                                              ProcedureHeading(..), FieldList(..), Designator(..), Value(..))
import qualified Language.Modula2.ISO.AST as AST
import Language.Modula2.Grammar (ParsedLexemes(Trailing))
import Language.Oberon.Abstract (coExpression, coValue)
import qualified Language.Oberon.Abstract as Oberon.Abstract
import qualified Language.Oberon.AST as Oberon.AST
import qualified Language.Oberon.ConstantFolder as Oberon
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
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Block l l _ _) = SynCFMod' l (AST.Block l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Declaration full l l _ _) = SynCFMod' l (AST.Declaration full l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.AddressedIdent l l _ _) = SynCF' (AST.AddressedIdent l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Type l l _ _) = SynCF' (AST.Type l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Expression λ l _ _) = SynCFExp λ l
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Item l l _ _) = SynCF' (AST.Item l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Statement l l _ _) = SynCF' (AST.Statement l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Variant l l _ _) = SynCF' (AST.Variant l l)

type instance Atts (Inherited (Auto ConstantFold)) (Modules l _ _) = InhCFRoot l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Block l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Declaration full l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.AddressedIdent l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Type l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Item l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Expression l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Statement l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Variant l l _ _) = InhCF l

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

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l), Abstract.Modula2 λ, Abstract.CoWirthy λ,
          Atts (Synthesized (Auto ConstantFold)) (AST.Expression λ l Sem Sem) ~ SynCFExp AST.Language l,
          InhCF l ~ InhCF λ,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Element l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ InhCF l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp l l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Element l l Sem Sem) ~ SynCF' (Abstract.Element l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Item l l Sem Sem) ~ SynCF' (Abstract.Item l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ SynCFDesignator l) =>
         Synthesizer (Auto ConstantFold) (AST.Expression λ l) Sem Placed where
   synthesis _ (pos, _) _ (AST.Remainder left right) = 
      foldBinaryInteger pos Abstract.remainder div (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Array itemType dimensions) =
      SynCFExp{folded= Mapped (pos, Abstract.array itemType (getMapped . folded' . syn <$> dimensions)),
               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Record recordType fields) =
      SynCFExp{folded= Mapped (pos, Abstract.record recordType (foldedExp' . syn <$> fields)),
               foldedValue= Nothing}
   synthesis _ (pos, AST.Relation op _ _) _ (AST.Relation _op left right) =
      case join (compareValues <$> foldedValue (syn left) <*> foldedValue (syn right))
      of Just value -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, value)),
                                foldedValue= Just value}
         Nothing -> SynCFExp{folded= Mapped (pos,
                                             Abstract.relation op (foldedExp' $ syn left) (foldedExp' $ syn right)),
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
   synthesis _ (pos, _) _ (AST.Positive expr) =
      case foldedValue (syn expr)
      of Just (AST.Integer n) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, AST.Integer n)),
                                          foldedValue= Just (AST.Integer n)}
         Just (AST.Real n) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, AST.Real n)),
                                       foldedValue= Just (AST.Real n)}
         _ -> SynCFExp{folded= Mapped (pos, Abstract.positive $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Negative expr) =
      case foldedValue (syn expr)
      of Just (AST.Integer n) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, AST.Integer $ negate n)),
                                          foldedValue= Just (AST.Integer $ negate n)}
         Just (AST.Real n) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, AST.Real $ negate n)),
                                       foldedValue= Just (AST.Real $ negate n)}
         _ -> SynCFExp{folded= Mapped (pos, Abstract.negative $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Add left right) =
      foldBinaryArithmetic pos Abstract.add (+) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Subtract left right) =
      foldBinaryArithmetic pos Abstract.subtract (-) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Or left right) =
      foldBinaryBoolean pos Abstract.or (||) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Multiply left right) =
      foldBinaryArithmetic pos Abstract.multiply (*) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Divide left right) =
      foldBinaryFractional pos Abstract.divide (/) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.IntegerDivide left right) =
      foldBinaryInteger pos Abstract.integerDivide div (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Modulo left right) =
      foldBinaryInteger pos Abstract.modulo mod (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.And left right) =
      foldBinaryBoolean pos Abstract.and (&&) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Not expr) =
      case foldedValue (syn expr)
      of Just (AST.Boolean True) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, Abstract.false)),
                                             foldedValue= Just Abstract.false}
         Just (AST.Boolean False) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, Abstract.true)),
                                              foldedValue= Just Abstract.true}
         _ -> SynCFExp{folded= Mapped (pos, Abstract.not $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos, AST.Set t _elements) _ (AST.Set _t elements) =
      SynCFExp{folded= Mapped (pos, Abstract.set t (getMapped . folded' . syn <$> getZipList elements)),
               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Read des) =
      case (designatorValue (syn des), getMapped $ folded (syn des :: SynCFDesignator l))
      of (Just val, (pos', _)) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos', val)),
                                           foldedValue= Just val}
         (Nothing, (pos', des')) -> SynCFExp{folded= Mapped (pos, Abstract.read (pos', des')),
                                             foldedValue= Nothing}
   synthesis _ (pos, AST.FunctionCall fn1 args1) inheritance (AST.FunctionCall fn args) =
      case (designatorValue (syn fn), foldedValue . syn <$> getZipList args)
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
         _ -> SynCFExp{folded= Mapped (pos, Abstract.functionCall (getMapped $ folded (syn fn :: SynCFDesignator l))
                                                                  (foldedExp' . syn <$> getZipList args)),
                       foldedValue= Nothing}
      where literalSynthesis value = SynCFExp{folded= Mapped (pos, Abstract.literal (pos, value)),
                                              foldedValue= Just value}
   synthesis _ (pos, _) _ (AST.Literal val) =
      SynCFExp{folded= Mapped (pos, Abstract.literal $ getMapped $ folded' $ syn val),
               foldedValue= Just $ snd $ getMapped $ folded' $ syn val}

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
