{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE UnicodeSyntax #-}

module BooleanCombination
  ( BC (..)
  , bot, top, (∨), (∧), (-->), (<-->), disjList, conjList, impl, biimpl
  , bcFlip
  , bcMap, bcTraverse, bcJoin
  , bcImplies, bcSimplify
  , Literal (..), unlit, fromLiteral, complement
  , fromCNF, cnf, cnfWithSimplify
  , fromDNF, dnf, dnfWithSimplify
  )
where

import Control.DeepSeq
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics
import Util

--------------------------------------------------------------------------------
data BC a
  = Prim a
  | Not (BC a)
  | Or (Set (BC a))
  | And (Set (BC a))
  deriving
    (Eq, Generic, Ord, Show)

instance Foldable BC where
  foldMap f (Prim x) = f x
  foldMap f (Not α) = foldMap f α
  foldMap f (Or αs) = foldMap (foldMap f) αs
  foldMap f (And αs) = foldMap (foldMap f) αs

instance NFData a ⇒ NFData (BC a)

bot ∷ Ord a ⇒ BC a
bot = Or []

top ∷ Ord a ⇒ BC a
top = And []

(∨) ∷ Ord a ⇒ BC a → BC a → BC a
(Or αs) ∨ (Or βs) = Or (αs <> βs)
(Or αs) ∨ β = Or (Set.insert β αs)
α ∨ (Or βs) = Or (Set.insert α βs)
α ∨ β = Or [α,β]

(∧) ∷ Ord a ⇒ BC a → BC a → BC a
(And αs) ∧ (And βs) = And (αs <> βs)
(And αs) ∧ β = And (Set.insert β αs)
α ∧ (And βs) = And (Set.insert α βs)
α ∧ β = And [α,β]

(-->) ∷ Ord a ⇒ BC a → BC a → BC a
a --> b = impl [a, b]

(<-->) ∷ Ord a ⇒ BC a → BC a → BC a
a <--> b = (a --> b) ∧ (b --> a)

disjList ∷ Ord a ⇒ [BC a] → BC a
disjList = Or . Set.fromList

conjList ∷ Ord a ⇒ [BC a] → BC a
conjList = And . Set.fromList

impl ∷ Ord a ⇒ [BC a] → BC a
impl [] = error "impl: empty list"
impl as = disjList $ last as : map Not (init as)

biimpl ∷ Ord a ⇒ [BC a] → BC a
biimpl [] = error "biimpl: empty list"
biimpl as = conjList $ zipWith (<-->) as (tail as)

infixr 6 <-->
infixr 7 -->
infixl 8 ∨
infixl 8 ∧

bcFlip ∷ BC a → BC a
bcFlip (Not α) = α
bcFlip α = Not α

bcMap ∷ Ord b ⇒ (a → b) → BC a → BC b
bcMap f (Prim x) = Prim (f x)
bcMap f (Not α) = Not (bcMap f α)
bcMap f (Or αs) = Or (Set.map (bcMap f) αs)
bcMap f (And αs) = And (Set.map (bcMap f) αs)

bcTraverse ∷ (Applicative f, Ord b) ⇒ (a → f b) → BC a → f (BC b)
bcTraverse f (Prim x) = Prim <$> f x
bcTraverse f (Not α) = Not <$> bcTraverse f α
bcTraverse f (Or αs) = Or . Set.fromList
                    <$> traverse (bcTraverse f) (Set.toList αs)
bcTraverse f (And αs) = And . Set.fromList
                     <$> traverse (bcTraverse f) (Set.toList αs)

bcJoin ∷ Ord a ⇒ BC (BC a) → BC a
bcJoin (Prim α) = α
bcJoin (Not α) = Not (bcJoin α)
bcJoin (Or αs) = Or (Set.map bcJoin αs)
bcJoin (And αs) = And (Set.map bcJoin αs)

--------------------------------------------------------------------------------
-- | Detects some cases where x implies y
bcImplies ∷ Ord a ⇒ (a → a → Bool) → BC a → BC a → Bool
bcImplies primImplies x y = case (x,y) of
  (Prim a, Prim b) → a `primImplies` b
  (Not a, Not b) → b `implies` a
  (Or as, b) | flip all as (\a → a `implies` b) → True
  (a, Or bs) | flip any bs (\b → a `implies` b) → True
  (And as, b) | flip any as (\a → a `implies` b) → True
  (a, And bs) | flip all bs (\b → a `implies` b) → True
  _ → False
  where
    implies = bcImplies primImplies

--------------------
-- | Simplification
bcSimplify ∷ Ord a ⇒ (a → a → Bool) → (a → BC a) → BC a → BC a
bcSimplify primImplies primSimplify = final . fusion . recursive
  where
    simplify = bcSimplify primImplies primSimplify
    implies = bcImplies primImplies
    recursive (Prim x) = primSimplify x
    recursive (Not α) = Not (simplify α)
    recursive (Or αs) = Or (Set.map (simplify) αs)
    recursive (And αs) = And (Set.map (simplify) αs)
    fusion = \case
      Or αs → Or $ foldMap (\case {Or βs → βs ; β → [β]}) αs
      And αs → And $ foldMap (\case {And βs → βs ; β → [β]}) αs
      α → α
    final = \case
      Not α | (α == bot) → top
            | (α == top) → bot
      Not (Not α) → α
      Or αs → let validates β | (β == top) = True
                              | otherwise = bcFlip β `Set.member` αs
              in if any validates αs
                 then top
                 else let isRemovable β =
                            flip any αs (\α → α /= β && β `implies` α)
                          αs' = Set.filter (not . isRemovable) αs
                      in if | Set.null αs' → bot
                            | Set.size αs' == 1 → Set.elemAt 0 αs'
                            | otherwise → Or αs'
      And αs → let falsifies β | (β == bot) = True
                               | otherwise = bcFlip β `Set.member` αs
               in if any falsifies αs
                  then bot
                  else let isRemovable β =
                             flip any αs (\α → α /= β && α `implies` β)
                           αs' = Set.filter (not . isRemovable) αs
                       in if | Set.null αs' → top
                             | Set.size αs' == 1 → Set.elemAt 0 αs'
                             | otherwise → And αs'
      α → α

--------------------------------------------------------------------------------
data Literal a
  = Neg a
  | Pos a
  deriving
    (Eq, Ord, Show)

unlit ∷ Literal a → a
unlit (Neg x) = x
unlit (Pos x) = x

fromLiteral ∷ Literal a → BC a
fromLiteral (Neg x) = Not (Prim x)
fromLiteral (Pos x) = Prim x

complement ∷ Literal a → Literal a
complement (Neg x) = Pos x
complement (Pos x) = Neg x

--------------------
fromCNF ∷ Ord a ⇒ Set (Set (Literal a)) → BC a
fromCNF = And . Set.map (Or . Set.map fromLiteral)

fromDNF ∷ Ord a ⇒ Set (Set (Literal a)) → BC a
fromDNF = Or . Set.map (And . Set.map fromLiteral)

cnf ∷ (Ord a) ⇒ BC a → Set (Set (Literal a))
cnf = cnf_

dnf ∷ (Ord a) ⇒ BC a → Set (Set (Literal a))
dnf = dnf_

cnfWithSimplify ∷ Ord a ⇒ (a → a → Bool) → (a → BC a) → BC a → Set (Set (Literal a))
cnfWithSimplify primImplies primSimplify α = go (cnf_ α)
  where
    go cs = let cs' = cnf_ . bcSimplify primImplies primSimplify . fromCNF $ cs
            in if cs == cs'
               then cs'
               else go cs'

dnfWithSimplify ∷ Ord a ⇒ (a → a → Bool) → (a → BC a) → BC a → Set (Set (Literal a))
dnfWithSimplify primImplies primSimplify α = go (dnf_ α)
  where
    go cs = let cs' = dnf_ . bcSimplify primImplies primSimplify . fromDNF $ cs
            in if cs == cs'
               then cs'
               else go cs'

--------------------
cnf_ ∷ (Ord a) ⇒ BC a → Set (Set (Literal a))
cnf_ (Prim x) = [[Pos x]]
cnf_ (Not (Prim x)) = [[Neg x]]
cnf_ (Not (Not α)) = cnf_ α
cnf_ (Not (Or αs)) = cnf_ (And (Set.map Not αs))
cnf_ (Not (And αs)) = cnf_ (Or (Set.map Not αs))
cnf_ (Or αs) = Set.map mconcat . setCartesianProduct . map cnf_ . Set.toList $ αs
cnf_ (And αs) = foldMap cnf_ αs

dnf_ ∷ (Ord a) ⇒ BC a → Set (Set (Literal a))
dnf_ (Prim x) = [[Pos x]]
dnf_ (Not (Prim x)) = [[Neg x]]
dnf_ (Not (Not α)) = dnf_ α
dnf_ (Not (Or αs)) = dnf_ (And (Set.map Not αs))
dnf_ (Not (And αs)) = dnf_ (Or (Set.map Not αs))
dnf_ (Or αs) = foldMap dnf_ αs
dnf_ (And αs) = Set.map mconcat . setCartesianProduct . map dnf_ . Set.toList $ αs
