{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

module Pretty
  ( tl, ppTL
  )
where

import Prelude hiding ((<>))
import Numeric.Natural
import Text.PrettyPrint
import qualified Data.Set as Set
import BooleanCombination
import TL

--------------------------------------------------------------------------------
tlDepth :: TL a -> Natural
tlDepth (Var _) = 1
tlDepth (S a b) = succ (max (tlDepth a) (tlDepth b))
tlDepth (U a b) = succ (max (tlDepth a) (tlDepth b))
tlDepth (Not a) = succ (tlDepth a)
tlDepth (Or as) = if Set.null as then 1 else succ (maximum (Set.map tlDepth as))
tlDepth (And as) = if Set.null as then 1 else succ (maximum (Set.map tlDepth as))

tlVertexCount :: TL a -> Natural
tlVertexCount (Var _) = 1
tlVertexCount (S a b) = succ (tlVertexCount a + tlVertexCount b)
tlVertexCount (U a b) = succ (tlVertexCount a + tlVertexCount b)
tlVertexCount (Not a) = succ (tlVertexCount a)
tlVertexCount (Or as) = succ (sum . map tlVertexCount . Set.toList $ as)
tlVertexCount (And as) = succ (sum . map tlVertexCount . Set.toList $ as)

belowIndentationThreshold :: TL a -> Bool
belowIndentationThreshold a = (tlDepth a <= 3) && (tlVertexCount a <= 10)

tl :: TL String -> Doc
tl = \case
  Var p -> text p
  a@(S b c) | (b == bot) ->
                "(● " <> nest 3 (tl c) <> ")"
            | (b == top) ->
                "(⧫ " <> nest 3 (tl c) <> ")"
            | belowIndentationThreshold a ->
                "(S " <> tl b <+> tl c <> ")"
            | otherwise ->
                "(S " <> nest 3 (tl b) $$ nest 3 (tl c) <> ")"
  a@(U b c) | (b == bot) ->
                "(○ " <> nest 3 (tl c) <> ")"
            | (b == top) ->
                "(◊ " <> nest 3 (tl c) <> ")"
            | belowIndentationThreshold a ->
                "(U " <> tl b <+> tl c <> ")"
            | otherwise ->
                "(U " <> nest 3 (tl b) $$ nest 3 (tl c) <> ")"
  Not a -> "(¬ " <> nest 3 (tl a) <> ")"
  a@(Or bs) ->
    let n = Set.size bs
    in if | n == 0 -> "⊥"
          | n == 1 -> tl (Set.elemAt 0 bs)
          | belowIndentationThreshold a ->
              "(∨ " <> (hsep . map tl . Set.toList $ bs) <> ")"
          | otherwise ->
              "(∨ " <> nest 3 (vcat . map tl . Set.toList $ bs) <> ")"
  a@(And bs) ->
    let n = Set.size bs
    in if | n == 0 -> "⊤"
          | n == 1 -> tl (Set.elemAt 0 bs)
          | belowIndentationThreshold a ->
              "(∧ " <> (hsep . map tl . Set.toList $ bs) <> ")"
          | otherwise ->
              "(∧ " <> nest 3 (vcat . map tl . Set.toList $ bs) <> ")"

----------------------------------------
ppTL :: TL String -> String
ppTL = render . tl
