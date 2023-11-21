{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module Translation
  ( TranslateError (..), Params (..)
  , translateWithParams, translate, translateWithSimplify
  , translateLTL, translateLTLWithSimplify
  )
where

import Prelude hiding (partition)
import Control.DeepSeq
import Control.Exception
import Data.Foldable
import qualified Data.List as List
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import BooleanCombination
import FOMLO
import TL
import Separation
import Util

--------------------------------------------------------------------------------
data Params
  = Params { pSimplify :: forall p x. (Ord p, Ord x) => FOMLO p x -> FOMLO p x
           , pCNF :: forall p x. (Ord p, Ord x)
                  => FOMLO p x -> Set (Set (Literal (SimpleFOMLO p x)))
           , pDNF :: forall p x. (Ord p, Ord x)
                  => FOMLO p x -> Set (Set (Literal (SimpleFOMLO p x)))
           , pSep :: forall p. Ord p => TL p -> TL p
           }

--------------------------------------------------------------------------------
pullout :: (Ord p, Ord x) => Params -> FOMLO p x -> FOMLO p x
pullout params@(Params {..}) =
  pSimplify . bcJoin . bcMap (simplePullout params) -- cases 0,1,2,3

simplePullout :: (Ord p, Ord x) => Params -> SimpleFOMLO p x -> FOMLO p x
simplePullout params@(Params {..}) = \case
  φ@(Predicate _ _) -> Prim φ -- case 0
  φ@(Equal _ _) -> Prim φ -- case 0
  φ@(LessThan _ _) -> Prim φ -- case 0
  φ@(Existential x α) -> -- case 4
    Or $ flip Set.map (pDNF (pullout params α)) $ \conj ->
      let (δs, γs) = Set.partition ((x `Set.member`) . freeVars)
                   . Set.map fromLiteral
                   $ conj
      in pSimplify $ And $ γs <> [Exists x (And δs)]
  φ@(Universal x α) -> -- case 5
    And $ flip Set.map (pCNF (pullout params α)) $ \disj ->
      let (δs, γs) = Set.partition ((x `Set.member`) . freeVars)
                   . Set.map fromLiteral
                   $ disj
      in pSimplify $ Or $ γs <> [Forall x (Or δs)]

--------------------------------------------------------------------------------
data Extended p
  = Before
  | Now
  | After
  | Base p
  deriving
    (Eq, Ord, Show)

simpleTrivialExtend :: (Ord p, Ord x) => SimpleFOMLO p x -> SimpleFOMLO (Extended p) x
simpleTrivialExtend (Predicate p x) = Predicate (Base p) x
simpleTrivialExtend (Equal x y) = Equal x y
simpleTrivialExtend (LessThan x y) = LessThan x y
simpleTrivialExtend (Existential x α) = Existential x (trivialExtend α)
simpleTrivialExtend (Universal x α) = Universal x (trivialExtend α)

trivialExtend :: (Ord p, Ord x) => FOMLO p x -> FOMLO (Extended p) x
trivialExtend = bcMap simpleTrivialExtend

simpleExtend :: (Ord p, Ord x) => x -> SimpleFOMLO p x -> FOMLO (Extended p) x
simpleExtend _ (Predicate p x) = Pred (Base p) x
simpleExtend t (Equal x y) | (x == t) && (y == t) = top
                           | x == t = Pred Now y
                           | y == t = Pred Now x
                           | otherwise = Eq x y
simpleExtend t (LessThan x y) | (x == t) && (y == t) = bot
                              | x == t = Pred After y
                              | y == t = Pred Before x 
                              | otherwise = Less x y
simpleExtend t (Existential x α) | x == t = Exists x (trivialExtend α)
                                 | otherwise = Exists x (extend t α)
simpleExtend t (Universal x α) | x == t = Forall x (trivialExtend α)
                               | otherwise = Forall x (extend t α)

extend :: (Ord p, Ord x) => x -> FOMLO p x -> FOMLO (Extended p) x
extend t = bcJoin . bcMap (simpleExtend t)

----------------------------------------
simpleUnextend :: (Ord p) => SimpleTL (Extended p) -> TL p
simpleUnextend (Variable Before) = bot
simpleUnextend (Variable Now) = top
simpleUnextend (Variable After) = bot
simpleUnextend (Variable (Base p)) = Var p
simpleUnextend a@(Since _ _) = simpleUnextendBefore a
  where
    simpleUnextendBefore (Variable Before) = top
    simpleUnextendBefore (Variable Now) = bot
    simpleUnextendBefore (Variable After) = bot
    simpleUnextendBefore (Variable (Base p)) = Var p
    simpleUnextendBefore (Since a b) = S (unextendBefore a) (unextendBefore b)
    simpleUnextendBefore (Until _ _) = error "simpleUnextendBefore: not separated"
    unextendBefore = bcJoin . bcMap simpleUnextendBefore
simpleUnextend a@(Until _ _) = simpleUnextendAfter a
  where
    simpleUnextendAfter (Variable Before) = bot
    simpleUnextendAfter (Variable Now) = bot
    simpleUnextendAfter (Variable After) = top
    simpleUnextendAfter (Variable (Base p)) = Var p
    simpleUnextendAfter (Since _ _) = error "simpleUnextendAfter: not separated"
    simpleUnextendAfter (Until a b) = U (unextendAfter a) (unextendAfter b)
    unextendAfter = bcJoin . bcMap simpleUnextendAfter

unextend :: Ord p => TL (Extended p) -> TL p
unextend = bcJoin . bcMap simpleUnextend

--------------------------------------------------------------------------------
data TranslateError
  = TooManyFreeVariables
  deriving
    (Eq, Show, Typeable)

instance Exception TranslateError

findFreeVariable :: (Inhabited x, Ord p, Ord x) => FOMLO p x -> x
findFreeVariable φ =
  if | n == 0 -> inhabitant -- arbitrary variable
     | n == 1 -> Set.elemAt 0 xs
     | otherwise -> throw TooManyFreeVariables
  where
    xs = freeVars φ
    n = Set.size xs

----------------------------------------
translateWithParams :: (Inhabited x, NFData x, Ord p, Ord x) => Params -> FOMLO p x -> TL p
translateWithParams params@(Params {..}) φ =
  let t = findFreeVariable φ
  in deepseq t (translate_ params t . pullout params . fomloSimplify $ φ)

translate :: (Inhabited x, NFData x, Ord p, Ord x) => FOMLO p x -> TL p
translate = translateWithParams $ Params id cnf dnf sep

translateWithSimplify :: (Inhabited x, NFData x, Ord p, Ord x) => FOMLO p x -> TL p
translateWithSimplify = translateWithParams $ Params fomloSimplify
                                                     fomloCNFWithSimplify
                                                     fomloDNFWithSimplify
                                                     sepWithSimplify

--------------------
translate_ :: (Ord p, Ord x) => Params -> x -> FOMLO p x -> TL p
translate_ params@(Params {..}) t =
  tlSimplify . bcJoin . bcMap (simpleTranslate_ params t) -- cases 0,1,5,6,7

simpleTranslate_ :: (Ord p, Ord x) => Params -> x -> SimpleFOMLO p x -> TL p
simpleTranslate_ params@(Params {..}) t = \case
  Predicate p _ -> Var p -- case 2
  Equal _ _ -> top -- case 3
  LessThan _ _ -> bot -- case 4
  φ@(Existential s α) -> -- case 8
    let a = translate_ params s . pSimplify . extend t $ α
    in tlSimplify . unextend . pSep $ eventuallyPast a ∨ a ∨ eventually a
  φ@(Universal s α) -> -- case 9
    let a = translate_ params s . pSimplify . extend t $ α
    in tlSimplify . unextend . pSep $ foreverPast a ∧ a ∧ forever a

--------------------------------------------------------------------------------
-- Converts a separated TL formula into LTL, equivalent at the minimum point
toLTL :: Ord p => TL p -> TL p
toLTL = bcJoin . bcMap simpleToLTL
  where
    simpleToLTL (Variable p) = Var p
    simpleToLTL (Since _ _) = bot
    simpleToLTL (Until a b) = U (toLTL a) (toLTL b)

translateLTL :: (Inhabited x, NFData x, Ord p, Ord x) => FOMLO p x -> TL p
translateLTL = toLTL . translate

translateLTLWithSimplify :: (Inhabited x, NFData x, Ord p, Ord x) => FOMLO p x -> TL p
translateLTLWithSimplify = toLTL . translateWithSimplify
