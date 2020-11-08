{-# LANGUAGE DataKinds, DeriveGeneric, DuplicateRecordFields, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, OverloadedStrings, RankNTypes,
             ScopedTypeVariables, TemplateHaskell, TypeFamilies, UndecidableInstances #-}

-- | The main export of this module is the function 'foldConstants' that folds the constants in a Modula-2 AST using
-- an attribute grammar. Other exports are helper functions and attribute types that can be reused for other languages
-- or attribute grammars.

module Language.Modula2.ConstantFolder (foldConstants,
                                        ConstantFold, Sem, Environment,
                                        InhCF, SynCF(..), SynCFDesignator(..), SynCFExp(..), SynCFMod(..), SynCFMod',
                                        foldBinaryArithmetic, foldBinaryBoolean,
                                        foldBinaryFractional, foldBinaryInteger,
                                        maxCardinal, maxInteger, minInteger, maxInt32, minInt32, maxSet, minSet,
                                        doubleSize, floatSize, intSize, int32Size,
                                        maxReal, minReal) where

import Control.Applicative (liftA2, ZipList(ZipList, getZipList))
import Control.Arrow (first)
import Control.Monad (join)
import Data.Bits (shift)
import Data.Char (chr, ord, toUpper)
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
import Language.Haskell.TH (appT, conT, varT, varE, newName)
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
type instance Atts (Inherited (Auto ConstantFold)) (AST.Module λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Declaration full λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.ProcedureHeading λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Type λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.FieldList λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Expression λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Designator λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Statement λ l _ _) = InhCF λ
type instance Atts (Inherited (Auto ConstantFold)) (AST.Variant λ l _ _) = InhCF λ

type Placed = (,) (Int, ParsedLexemes, Int)

wrap :: a -> Mapped Placed a
wrap = Mapped . (,) (0, Trailing [], 0)

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

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l), Abstract.Modula2 λ,
          Abstract.Value l ~ AST.Value l, Abstract.QualIdent l ~ AST.QualIdent l,
          Pretty (AST.Value l l Identity Identity),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp l l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Element l l Sem Sem) ~ SynCF' (Abstract.Element l l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ SynCFDesignator l) =>
         Synthesizer (Auto ConstantFold) (AST.Expression λ l) Sem Placed where
   synthesis _ (pos@(start, ls, end), AST.Relation op _ _) _ (AST.Relation _op left right) =
      case join (compareValues <$> foldedValue (syn left) <*> foldedValue (syn right))
      of Just value -> Oberon.literalSynthesis value
         Nothing -> SynCFExp{folded= Mapped (pos,
                                             Abstract.relation op (foldedExp' $ syn left) (foldedExp' $ syn right)),
                             foldedValue= Nothing}
      where compareValues (_, AST.Boolean l) (ls, AST.Boolean r)   = repos ls <$> relate op (compare l r)
            compareValues (_, AST.Integer l) (ls, AST.Integer r)   = repos ls <$> relate op (compare l r)
            compareValues (_, AST.Real l) (ls, AST.Real r)         = repos ls <$> relate op (compare l r)
            compareValues (_, AST.Integer l) (ls, AST.Real r)      = repos ls <$> relate op (compare (fromIntegral l) r)
            compareValues (_, AST.Real l) (ls, AST.Integer r)      = repos ls <$> relate op (compare l (fromIntegral r))
            compareValues (_, AST.CharCode l) (ls, AST.CharCode r) = repos ls <$> relate op (compare l r)
            compareValues (_, AST.String l) (ls, AST.String r)     = repos ls <$> relate op (compare l r)
            compareValues (_, AST.CharCode l) (ls, AST.String r) = repos ls
                                                                   <$> relate op (compare (Text.singleton $ chr l) r)
            compareValues (_, AST.String l) (ls, AST.CharCode r) = repos ls
                                                                   <$> relate op (compare l (Text.singleton $ chr r))
            compareValues _ _                               = Nothing
            repos (_, ls', _) v = ((start, anyWhitespace ls ls', end), v)
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
   synthesis _ (pos@(start, ls, end), _) _ (AST.Positive expr) =
      case foldedValue (syn expr)
      of Just ((_, ls', _), AST.Integer n) -> Oberon.literalSynthesis ((start, anyWhitespace ls ls', end),
                                                                       AST.Integer n)
         Just ((_, ls', _), AST.Real n) -> Oberon.literalSynthesis ((start, anyWhitespace ls ls', end), AST.Real n)
         _ -> SynCFExp{folded= Mapped (pos, Abstract.positive $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos@(start, ls, end), _) _ (AST.Negative expr) =
      case foldedValue (syn expr)
      of Just ((_, ls', _), AST.Integer n) -> Oberon.literalSynthesis ((start, anyWhitespace ls ls', end),
                                                                       AST.Integer $ negate n)
         Just ((_, ls', _), AST.Real n) -> Oberon.literalSynthesis ((start, anyWhitespace ls ls', end),
                                                                    AST.Real $ negate n)
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
   synthesis _ (pos@(start, ls, end), _) _ (AST.Not expr) =
      case foldedValue (syn expr)
      of Just ((_, ls', _), AST.Boolean b) -> Oberon.literalSynthesis ((start, anyWhitespace ls ls', end),
                                                                       if b then Abstract.false else Abstract.true)
         _ -> SynCFExp{folded= Mapped (pos, Abstract.not $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos, AST.Set t _elements) _ (AST.Set _t elements) =
      SynCFExp{folded= Mapped (pos, Abstract.set t (getMapped . folded' . syn <$> getZipList elements)),
               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Read des) =
      case (designatorValue (syn des), getMapped $ folded (syn des :: SynCFDesignator l))
      of (Just val, _) -> Oberon.literalSynthesis val
         (Nothing, (pos', des')) -> SynCFExp{folded= Mapped (pos, Abstract.read (pos', des')),
                                             foldedValue= Nothing}
   synthesis _ (pos, AST.FunctionCall fn1 args1) inheritance (AST.FunctionCall fn args) =
      case (snd <$> designatorValue (syn fn :: SynCFDesignator l), (snd <$>) . foldedValue . syn <$> getZipList args)
      of (Just (AST.Builtin "CAP"), [Just (AST.String s)])
            | Text.length s == 1, capital <- Text.toUpper s -> fromValue (Abstract.string capital)
         (Just (AST.Builtin "CAP"), [Just (AST.CharCode c)])
            | capital <- ord (toUpper $ chr c) -> fromValue (Abstract.charCode capital)
         (Just (AST.Builtin "CHR"), [Just (AST.Integer code)]) -> fromValue (Abstract.charCode $ fromIntegral code)
         (Just (AST.Builtin "ORD"), [Just (AST.String s)])
            | Text.length s == 1, code <- ord (Text.head s) -> fromValue (Abstract.integer $ toInteger code)
         (Just (AST.Builtin "ORD"), [Just (AST.CharCode code)]) -> fromValue (Abstract.integer $ toInteger code)
         (Just (AST.Builtin "ABS"), [Just (AST.Integer i)]) -> fromValue (Abstract.integer $ abs i)
         (Just (AST.Builtin "ABS"), [Just (AST.Real r)]) -> fromValue (Abstract.real $ abs r)
         (Just (AST.Builtin "ASH"), [Just (AST.Integer i), Just (AST.Integer j)])
            | shifted <- shift i (fromIntegral j) -> fromValue (Abstract.integer shifted)
         (Just (AST.Builtin "TRUNC"), [Just (AST.Real x)]) -> fromValue (Abstract.integer $ floor x)
         (Just (AST.Builtin "FLOAT"), [Just (AST.Integer x)]) -> fromValue (Abstract.real $ fromIntegral x)
         (Just (AST.Builtin "FLOAT"), [Just (AST.Real x)]) -> fromValue (Abstract.real x)
         (Just (AST.Builtin "LEN"), [Just (AST.String s)]) -> fromValue (Abstract.integer $ toInteger $ Text.length s)
         (Just (AST.Builtin "LONG"), [Just (AST.Integer x)]) -> fromValue (Abstract.integer x)
         (Just (AST.Builtin "LONG"), [Just (AST.Real x)]) -> fromValue (Abstract.real x)
         (Just (AST.Builtin "SHORT"), [Just (AST.Integer x)]) -> fromValue (Abstract.integer x)
         (Just (AST.Builtin "SHORT"), [Just (AST.Real x)]) -> fromValue (Abstract.real x)
         (Just (AST.Builtin "ODD"), [Just (AST.Integer x)]) ->
            fromValue (if x `mod` 2 == 1 then Abstract.true else Abstract.false)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "INTEGER")]) -> fromValue (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "LONGINT")]) -> fromValue (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "CARDINAL")]) -> fromValue (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "REAL")]) -> fromValue (Abstract.integer doubleSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "LONGREAL")]) -> fromValue (Abstract.integer doubleSize)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "CHAR")]) -> fromValue (Abstract.charCode 0xff)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "INTEGER")]) -> fromValue (Abstract.integer maxInteger)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "LONGINT")]) -> fromValue (Abstract.integer maxInteger)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "CARDINAL")]) -> fromValue (Abstract.integer maxCardinal)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "BITSET")]) -> fromValue (Abstract.integer maxSet)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "REAL")]) -> fromValue (Abstract.real maxReal)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "LONGREAL")]) -> fromValue (Abstract.real maxReal)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "CHAR")]) -> fromValue (Abstract.charCode 0)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "INTEGER")]) -> fromValue (Abstract.integer minInteger)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "LONGINT")]) -> fromValue (Abstract.integer minInteger)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "CARDINAL")]) -> fromValue (Abstract.integer 0)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "BITSET")]) -> fromValue (Abstract.integer minSet)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "REAL")]) -> fromValue (Abstract.real minReal)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "LONGREAL")]) -> fromValue (Abstract.real minReal)
         _ -> SynCFExp{folded= Mapped (pos, Abstract.functionCall (getMapped $ folded (syn fn :: SynCFDesignator l))
                                                                  (foldedExp' . syn <$> getZipList args)),
                       foldedValue= Nothing}
      where fromValue v = Oberon.literalSynthesis (pos, v)
   synthesis _ (pos, _) _ (AST.Literal val) =
      SynCFExp{folded= Mapped (pos, Abstract.literal $ getMapped $ folded' $ syn val),
               foldedValue= Just (getMapped $ folded' $ syn val)}

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

foldBinaryArithmetic :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ,
                                  Pretty (Abstract.Value l l Identity Identity)) =>
                        (Int, ParsedLexemes, Int)
                     -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> Abstract.Expression λ l f f)
                     -> (forall n. Num n => n -> n -> n)
                     -> SynCFExp l l -> SynCFExp l l -> SynCFExp λ l
foldBinaryArithmetic pos@(start, ls, end) node op l r =
   case join (foldValues <$> foldedValue l <*> foldedValue r)
   of Just v -> Oberon.literalSynthesis v
      Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                          foldedValue= Nothing}
   where foldValues :: Placed (AST.Value l l f f) -> Placed (AST.Value l l f f) -> Maybe (Placed (AST.Value l l f f))
         foldBareValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (_, l') ((_, ls', _), r') = (,) (start, anyWhitespace ls ls', end) <$> foldBareValues l' r'
         foldBareValues (AST.Integer l') (AST.Integer r') = Just (AST.Integer $ op l' r')
         foldBareValues (AST.Real l')    (AST.Real r')    = Just (AST.Real $ op l' r')
         foldBareValues (AST.Integer l') (AST.Real r')    = Just (AST.Real $ op (fromIntegral l') r')
         foldBareValues (AST.Real l')    (AST.Integer r') = Just (AST.Real $ op l' (fromIntegral r'))
         foldBareValues _ _ = Nothing

foldBinaryFractional :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ,
                                  Pretty (Abstract.Value l l Identity Identity)) =>
                        (Int, ParsedLexemes, Int)
                     -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> Abstract.Expression λ l f f)
                     -> (forall n. Fractional n => n -> n -> n)
                     -> SynCFExp l l -> SynCFExp l l -> SynCFExp λ l
foldBinaryFractional pos@(start, ls, end) node op l r =
   case join (foldValues <$> foldedValue l <*> foldedValue r)
   of Just v -> Oberon.literalSynthesis v
      Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                          foldedValue= Nothing}
   where foldValues :: Placed (AST.Value l l f f) -> Placed (AST.Value l l f f) -> Maybe (Placed (AST.Value l l f f))
         foldValues (_, AST.Real l') ((_, ls', _), AST.Real r') = Just ((start, anyWhitespace ls ls', end),
                                                                        AST.Real $ op l' r')
         foldValues _ _ = Nothing

foldBinaryInteger :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ,
                               Pretty (Abstract.Value l l Identity Identity)) =>
                        (Int, ParsedLexemes, Int)
                     -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> Abstract.Expression λ l f f)
                     -> (forall n. Integral n => n -> n -> n)
                     -> SynCFExp l l -> SynCFExp l l -> SynCFExp λ l
foldBinaryInteger pos@(start, ls, end) node op l r =
   case join (foldValues <$> foldedValue l <*> foldedValue r)
   of Just v -> Oberon.literalSynthesis v
      Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                          foldedValue= Nothing}
   where foldValues :: Placed (AST.Value l l f f) -> Placed (AST.Value l l f f) -> Maybe (Placed (AST.Value l l f f))
         foldValues (_, AST.Integer l') ((_, ls', _), AST.Integer r') = Just ((start, anyWhitespace ls ls', end),
                                                                              AST.Integer $ op l' r')
         foldValues _ _ = Nothing

foldBinaryBoolean :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ,
                               Pretty (Abstract.Value l l Identity Identity)) =>
                     (Int, ParsedLexemes, Int)
                  -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> Abstract.Expression λ l f f)
                  -> (Bool -> Bool -> Bool)
                  -> SynCFExp l l -> SynCFExp l l -> SynCFExp λ l
foldBinaryBoolean pos@(start, ls, end) node op l r =
   case join (foldValues <$> foldedValue l <*> foldedValue r)
   of Just v -> Oberon.literalSynthesis v
      Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                          foldedValue= Nothing}
   where foldValues :: Placed (AST.Value l l f f) -> Placed (AST.Value l l f f) -> Maybe (Placed (AST.Value l l f f))
         foldValues (_, AST.Boolean l') ((_, ls', _), AST.Boolean r') = Just ((start, anyWhitespace ls ls', end),
                                                                              AST.Boolean $ op l' r')
         foldValues _ _ = Nothing

instance (Abstract.Modula2 l, Ord (Abstract.QualIdent l), v ~ Abstract.Value l l Placed Placed,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ InhCF l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp λ l,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ SynCFDesignator l) =>
         SynthesizedField "designatorValue" (Maybe (Placed v)) (Auto ConstantFold) (AST.Designator l l) Sem Placed where
   synthesizedField _ _ (pos, AST.Variable q) inheritance _ = (,) pos <$> join (Map.lookup q $ env inheritance)
   synthesizedField _ _ _ _ _ = Nothing

-- * More boring Transformation.Functor instances, TH candidates
instance Ord (Abstract.QualIdent l) => Transformation.At (Auto ConstantFold) (Modules l Sem Sem) where
   ($) = AG.applyDefault snd

-- * Unsafe Rank2 AST instances

$(do l <- varT  <$> newName "l"
     mconcat <$> mapM (\g-> Transformation.Full.TH.deriveUpFunctor (conT ''Auto `appT` conT ''ConstantFold) $ conT g `appT` l `appT` l)
        [''AST.Type, ''AST.FieldList,
         ''AST.ProcedureHeading,
         ''AST.Expression, ''AST.Designator,
         ''AST.Statement, ''AST.Variant])

$(do let sem = [t|Semantics (Auto ConstantFold)|]
     let inst g = [d| instance Attribution (Auto ConstantFold) ($g l l) Sem Placed =>
                               Transformation.At (Auto ConstantFold) ($g l l $sem $sem)
                         where ($) = AG.applyDefault snd |]
     mconcat <$> mapM (inst . conT)
        [''AST.Module, ''AST.ProcedureHeading, ''AST.Type, ''AST.FieldList,
         ''AST.Statement, ''AST.Expression, ''AST.Designator, ''AST.Variant])

$(do full <- varT  <$> newName "full"
     l <- varT  <$> newName "l"
     Transformation.Full.TH.deriveUpFunctor [t| (Auto ConstantFold) |] [t| AST.Declaration $full $l $l |])

instance Attribution (Auto ConstantFold) (AST.Declaration full l l) Sem Placed
      => Transformation.At (Auto ConstantFold) (AST.Declaration full l l Sem Sem) where
   ($) = AG.applyDefault snd
