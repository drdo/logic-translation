{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}

module Separation
  ( sep, sepWithSimplify
  , t1, t2, t3, t4, t5, t6, t7, t8
  )
where

import Data.Foldable
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import Numeric.Natural
import qualified Data.Set as Set
import BooleanCombination
import TL

--------------------------------------------------------------------------------
simpleTDepth :: SimpleTL p -> Natural
simpleTDepth (Variable _) = 0
simpleTDepth (Since a b) = succ (max (tDepth a) (tDepth b))
simpleTDepth (Until a b) = succ (max (tDepth a) (tDepth b))

tDepth :: TL p -> Natural
tDepth a = let l = toList (bcMap simpleTDepth a)
           in if null l then 0 else maximum l

simpleIsPast0, simpleIsFut0, simpleIsFut, simpleIsSep :: SimpleTL p -> Bool
simpleIsPast0 (Variable _) = True
simpleIsPast0 (Since a b) = isPast0 a && isPast0 b
simpleIsPast0 _ = False
simpleIsFut0 (Variable _) = True
simpleIsFut0 (Until a b) = isFut0 a && isFut0 b
simpleIsFut0 _ = False
simpleIsFut (Variable _) = False
simpleIsFut (Until a b) = isFut0 a && isFut0 b
simpleIsFut _ = False
simpleIsSep (Variable _) = True
simpleIsSep (Since a b) = isPast0 a && isPast0 b
simpleIsSep (Until a b) = isFut0 a && isFut0 b

isPast0, isFut0, isSep :: TL p -> Bool
isPast0 = all simpleIsPast0
isFut0 = all simpleIsFut0
isSep = all simpleIsSep

--------------------------------------------------------------------------------
data Params p
  = Params { pSimplify :: TL p -> TL p
           , pCNF :: TL p -> Set (Set (Literal (SimpleTL p)))
           , pDNF :: TL p -> Set (Set (Literal (SimpleTL p)))
           }

sep :: Ord p => TL p -> TL p
sep = sep_ (Params id cnf dnf)

sepWithSimplify :: Ord p => TL p -> TL p
sepWithSimplify = sep_ (Params tlSimplify tlCNFWithSimplify tlDNFWithSimplify) . tlSimplify

--------------------
sep_ :: Ord p => Params p -> TL p -> TL p
sep_ params@(Params {..}) = pSimplify . bcJoin . bcMap (simpleSep params) -- cases 1,2,3

simpleSep :: Ord p => Params p -> SimpleTL p -> TL p
simpleSep params@(Params {..}) x
  | simpleIsSep x = Prim x -- case 0
  | otherwise = case x of
      Since a b | isSep a && isSep b -> sep5 params (pCNF a) (pDNF b) -- cases 4,5
                | otherwise -> let a' = sep_ params a
                                   b' = sep_ params b
                              in sep_ params (pSimplify $ S a' b') -- case 6
      Until a b -> pSimplify . dual . sep_ params . dual $ Prim x -- case 7

-- | Case 5
sep5 :: Ord p
     => Params p
     -> Set (Set (Literal (SimpleTL p)))
     -> Set (Set (Literal (SimpleTL p)))
     -> TL p
sep5 params@(Params {..}) as bs
  | Set.null bs = bot
  | Set.null as = pSimplify $ Or $ Set.map (sep4TopLeft params) bs
  | otherwise =
      pSimplify $ And (Set.map (\a -> Or (Set.map (sep4 params a) bs)) as)

-- | Case 4 (Special case where the left side is ⊤)
sep4TopLeft :: Ord p
            => Params p
            -> Set (Literal (SimpleTL p))
            -> TL p
sep4TopLeft params@(Params {..}) bs =
  let (_d_, _b_) = Set.partition (simpleIsFut . unlit) bs
  in if Set.null _d_
     then S top (And (Set.map fromLiteral bs)) -- Already separated
     else let e@(Until f g) = case4Pick [] _d_
              b' = And . Set.map fromLiteral
                 $ _b_ <> (_d_ `Set.difference` [Pos e, Neg e])
          in if | Pos e `Set.member` _d_ -> sep_ params (pSimplify $ t2 top b' f g)
                | Neg e `Set.member` _d_ -> sep_ params (pSimplify $ t5 top b' f g)

-- | Case 4
sep4 :: Ord p
     => Params p
     -> Set (Literal (SimpleTL p))
     -> Set (Literal (SimpleTL p))
     -> TL p
sep4 params@(Params {..}) as bs =
  let (_c_, _a_) = Set.partition (simpleIsFut . unlit) as
      (_d_, _b_) = Set.partition (simpleIsFut . unlit) bs
  in if Set.null _c_ && Set.null _d_
     then S (Or (Set.map fromLiteral as))
            (And (Set.map fromLiteral bs)) -- Already separated
     else let e@(Until f g) = case4Pick _c_ _d_
              a' = Or . Set.map fromLiteral
                 $ _a_ <> (_c_ `Set.difference` [Pos e, Neg e])
              b' = And . Set.map fromLiteral
                 $ _b_ <> (_d_ `Set.difference` [Pos e, Neg e])
              test s = if | (Pos e `Set.member` s) -> Just True
                          | (Neg e `Set.member` s) -> Just False
                          | otherwise -> Nothing
              transformation = case (test _c_, test _d_) of
                (Just True, Nothing) -> t1
                (Nothing, Just True) -> t2
                (Just True, Just True) -> t3
                (Just False, Nothing) -> t4
                (Nothing, Just False) -> t5
                (Just True, Just False) -> t6
                (Just False, Just False) -> t7
                (Just False, Just True) -> t8
          in sep_ params (pSimplify $ transformation a' b' f g)

-- | This picks the (F U G) in case 4
case4Pick :: Ord p
          => Set (Literal (SimpleTL p))
          -> Set (Literal (SimpleTL p))
          -> SimpleTL p
case4Pick _c_ _d_ =
  let sorted = sortBy (\a b -> compare (simpleTDepth b)
                                      (simpleTDepth a))
             . map unlit
             $ Set.toList (_c_ <> _d_)
      candidates = takeWhile (\a -> simpleTDepth a == simpleTDepth (head sorted))
                             sorted
      test c s = if | (Pos c `Set.member` s) -> Just True
                    | (Neg c `Set.member` s) -> Just False
                    | otherwise -> Nothing
      score c = let order = [ (Just False, Just True) -- t8
                            , (Just False, Just False) -- t7
                            , (Just True, Just False) -- t6
                            , (Just True, Just True) -- t3
                            , (Nothing, Just False) -- t5
                            , (Nothing, Just True) -- t2
                            , (Just False, Nothing) -- t4
                            , (Just True, Nothing) -- t1
                            ] -- The order we choose appears to affect runtime
                in fromJust $ elemIndex (test c _c_, test c _d_) order
  in head . sortOn score $ candidates

--------------------------------------------------------------------------------
t1, t2, t3, t4, t5, t6, t7, t8 :: Ord p => TL p -> TL p -> TL p -> TL p -> TL p

t1 a b f g = p ∧ (p' `S` b)
  where
    n = (Not g ∧ Not b) `S` (Not a ∧ Not b)
    p' = n --> g ∨ f
    p = n --> g ∨ (f ∧ f`U`g)

t2 a b f g = hB ∨ hNA
  where
    hB = a `S` (g ∧ a ∧ (a ∧ f)`S`b)
    hNA = (a ∧ f)`S`b ∧ (g ∨ (f ∧ f`U`g))

t3 a b f g = hB ∨ hNA
  where
    n = Not g `S` Not a
    p' = n --> g ∨ f
    p = n --> g ∨ (f ∧ f`U`g)
    hB = p ∧ p'`S`(g ∧ f`S`b)
    hNA = f`S`b ∧ (g ∨ (f ∧ f`U`g))

t4 a b f g = Not (t2 (Not b) (Not a ∧ Not b) f g) ∨ eventuallyPast b

t5 a b f g = (a`S`(Not f ∧ Not g ∧ a ∧ (a ∧ Not g)`S`b))
           ∨ ((a ∧ Not g)`S`b ∧ Not g ∧ (Not f ∨ Not (f`U`g)))

t6 a b f g = t1 a ((a ∧ Not g)`S`b ∧ Not g ∧ Not f ∧ a) f g
           ∨ t3 a ((a ∧ Not g)`S`b ∧ Not g ∧ Not f) f g
           ∨ ((a ∧ Not g)`S`b ∧ Not g ∧ (Not f ∨ Not (f`U`g)))

t7 a b f g = Not (t3 (Not b) (Not a) f g) ∧ t5 top b f g

t8 a b f g = t4 a ((a ∧ f)`S`b ∧ g ∧ a) f g
           ∨ t7 a ((a ∧ f)`S`b ∧ g) f g
           ∨ ((a ∧ f)`S`b ∧ (g ∨ (f ∧ f`U`g)))
