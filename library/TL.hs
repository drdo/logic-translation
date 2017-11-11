{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnicodeSyntax #-}

module TL
  ( SimpleTL (..), TL, pattern Var, pattern S, pattern U
  , nextPast, next, eventuallyPast, eventually, foreverPast, forever
  , simpleDual, dual
  , stlImplies, tlImplies, stlSimplify, tlSimplify
  , tlCNFWithSimplify , tlDNFWithSimplify
  )
where

import Control.DeepSeq
import Data.Set (Set)
import Data.String
import GHC.Generics
import BooleanCombination

--------------------------------------------------------------------------------
data SimpleTL p
  = Variable p
  | Since (TL p) (TL p)
  | Until (TL p) (TL p)
  deriving
    (Eq, Generic, Ord, Show)

instance NFData p ⇒ NFData (SimpleTL p)

type TL p = BC (SimpleTL p)

instance IsString (TL String) where
  fromString = Prim . Variable

pattern Var p = Prim (Variable p)
pattern S a b = Prim (Since a b)
pattern U a b = Prim (Until a b)

infix 9 `Since`
infix 9 `Until`
infix 9 `S`
infix 9 `U`

nextPast ∷ Ord p ⇒ TL p → TL p
nextPast a = S bot a

next ∷ Ord p ⇒ TL p → TL p
next a = U bot a

eventuallyPast ∷ Ord p ⇒ TL p → TL p
eventuallyPast a = S top a

eventually ∷ Ord p ⇒ TL p → TL p
eventually a = U top a

foreverPast ∷ Ord p ⇒ TL p → TL p
foreverPast = Not . eventuallyPast . Not

forever ∷ Ord p ⇒ TL p → TL p
forever = Not . eventually . Not

simpleDual ∷ Ord p ⇒ SimpleTL p → SimpleTL p
simpleDual (Variable p) = Variable p
simpleDual (Since a b) = Until (dual a) (dual b)
simpleDual (Until a b) = Since (dual a) (dual b)

dual ∷ Ord p ⇒ TL p → TL p
dual = bcMap simpleDual

--------------------------------------------------------------------------------
-- These detect some cases where x implies y

stlImplies ∷ Ord p ⇒ SimpleTL p → SimpleTL p → Bool
stlImplies x y = case (x,y) of
  (Variable p, Variable p') → p == p'
  (Since a b, Since c d) → (a ∧ Not b) `tlImplies` c && b `tlImplies` d
  (Until a b, Until c d) → (a ∧ Not b) `tlImplies` c && b `tlImplies` d
  _ → False

tlImplies ∷ Ord p ⇒ TL p → TL p → Bool
tlImplies = bcImplies stlImplies

----------------------------------------
-- Simplification

stlSimplify ∷ Ord p ⇒ SimpleTL p → TL p
stlSimplify = final . recursive
  where
    recursive (Variable p) = Variable p
    recursive (Since a b) = Since (tlSimplify a) (tlSimplify b)
    recursive (Until a b) = Until (tlSimplify a) (tlSimplify b)
    final = \case
      Since a b | (b == bot) → bot
                | (b == top) → S bot top
                | (tlImplies (a ∧ Not b) b) → S bot b
                | otherwise → S a b
      Until a b | (b == bot) → bot
                | (b == top) → U bot top
                | (tlImplies (a ∧ Not b) b) → U bot b
                | otherwise → U a b
      a → Prim a

tlSimplify ∷ Ord p ⇒ TL p → TL p
tlSimplify = bcSimplify stlImplies stlSimplify

--------------------------------------------------------------------------------
tlCNFWithSimplify ∷ Ord p ⇒ TL p → Set (Set (Literal (SimpleTL p)))
tlCNFWithSimplify = cnfWithSimplify stlImplies stlSimplify

tlDNFWithSimplify ∷ Ord p ⇒ TL p → Set (Set (Literal (SimpleTL p)))
tlDNFWithSimplify = dnfWithSimplify stlImplies stlSimplify
