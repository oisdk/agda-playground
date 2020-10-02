{-# OPTIONS --cubical --safe #-}

module Data.Bits.Strict where

open import Data.Bits
open import Prelude

infixr 8 0∷!_ 1∷!_
0∷!_ : Bits → Bits
0∷!_ = λ! xs →! 0∷ xs
{-# INLINE 0∷!_ #-}

1∷!_ : Bits → Bits
1∷!_ = λ! xs →! 1∷ xs
{-# INLINE 1∷!_ #-}

0∷!≡0∷ : ∀ xs → 0∷! xs ≡ 0∷ xs
0∷!≡0∷ = $!-≡ 0∷_

1∷!≡1∷ : ∀ xs → 1∷! xs ≡ 1∷ xs
1∷!≡1∷ = $!-≡ 1∷_
