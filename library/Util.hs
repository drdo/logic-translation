{-# LANGUAGE OverloadedLists #-}

module Util
  ( foldl1', setCartesianProduct, Inhabited (..)
  )
where

import Data.Foldable
import Data.Set (Set)
import qualified Data.List as List
import qualified Data.Set as Set

--------------------------------------------------------------------------------
foldl1' :: Foldable t => (a -> a -> a) -> t a -> a
foldl1' f = List.foldl1' f . toList

--------------------------------------------------------------------------------
setCartesianProduct :: Ord a => [Set a] -> Set [a]
setCartesianProduct = foldr (\s -> foldMap (\ l -> Set.map (: l) s)) [[]]

--------------------------------------------------------------------------------
class Inhabited a where
  inhabitant :: a

instance Inhabited [a] where
  inhabitant = []
