{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module FOMLO
  ( SimpleFOMLO (..), FOMLO
  , pattern Pred, pattern Eq, pattern Less, pattern Exists, pattern Forall
  , simpleFreeVars, freeVars
  , sfomloImplies, fomloImplies, sfomloSimplify, fomloSimplify
  , fomloCNFWithSimplify, fomloDNFWithSimplify
  )
where

import Data.Set (Set)
import qualified Data.Set as Set
import BooleanCombination

--------------------------------------------------------------------------------
data SimpleFOMLO p x
  = Predicate p x
  | Equal x x
  | LessThan x x
  | Existential x (FOMLO p x)
  | Universal x (FOMLO p x)
  deriving
    (Eq, Ord, Show)

type FOMLO p x = BC (SimpleFOMLO p x)

pattern Pred :: p -> x -> FOMLO p x
pattern Pred p x = Prim (Predicate p x)

pattern Eq :: x -> x -> FOMLO p x
pattern Eq x y = Prim (Equal x y)

pattern Less :: x -> x -> FOMLO p x
pattern Less x y = Prim (LessThan x y)

pattern Exists :: x -> FOMLO p x -> FOMLO p x
pattern Exists x φ = Prim (Existential x φ)

pattern Forall :: x -> FOMLO p x -> FOMLO p x
pattern Forall x φ = Prim (Universal x φ)

simpleFreeVars :: Ord x => SimpleFOMLO p x -> Set x
simpleFreeVars (Predicate _ x) = [x]
simpleFreeVars (Equal x y) = [x,y]
simpleFreeVars (LessThan x y) = [x,y]
simpleFreeVars (Existential x α) = Set.delete x (freeVars α)
simpleFreeVars (Universal x α) = Set.delete x (freeVars α)

freeVars :: Ord x => FOMLO p x -> Set x
freeVars = foldMap simpleFreeVars

--------------------------------------------------------------------------------
-- These detect some cases where x implies y

sfomloImplies :: (Ord p, Ord x) => SimpleFOMLO p x -> SimpleFOMLO p x -> Bool
sfomloImplies φ χ = case (φ,χ) of
  (Predicate p x, Predicate p' x') -> (p == p') && (x == x')
  (Equal x y, Equal x' y') -> ((x == x') && (y == y')) || ((x == y') && (y == x'))
  (LessThan x y, LessThan x' y') -> (x == x') && (y == y')
  -- These next two could do more by variable renaming
  (Existential x α, Existential y β) -> (x == y) && fomloImplies α β
  (Universal x α, Universal y β) -> (x == y) && fomloImplies α β
  _ -> False

fomloImplies :: (Ord p, Ord x) => FOMLO p x -> FOMLO p x -> Bool
fomloImplies = bcImplies sfomloImplies

----------------------------------------
sfomloSimplify :: (Ord p, Ord x) => SimpleFOMLO p x -> FOMLO p x
sfomloSimplify = final . recursive
  where
    recursive (Existential x α) = Existential x (fomloSimplify α)
    recursive (Universal x α) = Universal x (fomloSimplify α)
    recursive α = α
    final = \case
      Predicate p x -> Pred p x
      Equal x y | (x == y) -> top
                | otherwise -> Eq x y
      LessThan x y | (x == y) -> bot
                   | otherwise -> Less x y
      Existential x α | x `Set.member` freeVars α -> Exists x α
                      | otherwise -> α
      Universal x α | x `Set.member` freeVars α -> Forall x α
                    | otherwise -> α

fomloSimplify :: (Ord p, Ord x) => FOMLO p x -> FOMLO p x
fomloSimplify = bcSimplify sfomloImplies sfomloSimplify

--------------------------------------------------------------------------------
fomloCNFWithSimplify :: (Ord p, Ord x) => FOMLO p x -> Set (Set (Literal (SimpleFOMLO p x)))
fomloCNFWithSimplify = cnfWithSimplify sfomloImplies sfomloSimplify

fomloDNFWithSimplify :: (Ord p, Ord x) => FOMLO p x -> Set (Set (Literal (SimpleFOMLO p x)))
fomloDNFWithSimplify = dnfWithSimplify sfomloImplies sfomloSimplify
