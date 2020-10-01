{-# OPTIONS --cubical --safe #-}

module Data.Bits.Fold where

open import Data.Bits
open import Strict
open import Prelude

module _ {a} {A : Type a} (zer : A → A) (one : A → A) (base : A) where
  foldr-bits : Bits → A
  foldr-bits [] = base
  foldr-bits (0∷ xs) = zer (foldr-bits xs)
  foldr-bits (1∷ xs) = one (foldr-bits xs)

foldr-universal : ∀ (h : Bits → A) z o e →
                    (h [] ≡ e) →
                    (∀ xs → h (0∷ xs) ≡ z (h xs)) →
                    (∀ xs → h (1∷ xs) ≡ o (h xs)) →
                    ∀ xs → h xs ≡ foldr-bits z o e xs
foldr-universal h z o e base zer one [] = base
foldr-universal h z o e base zer one (0∷ xs) = zer xs ; cong z (foldr-universal h z o e base zer one xs)
foldr-universal h z o e base zer one (1∷ xs) = one xs ; cong o (foldr-universal h z o e base zer one xs)

module _ {a} {A : Type a} (zer : A → A) (one : A → A) where
  foldl-go : Bits → A → A
  foldl-go []      base = base
  foldl-go (0∷ xs) base = foldl-go xs $! zer base
  foldl-go (1∷ xs) base = foldl-go xs $! one base

  foldl-bits : A → Bits → A
  foldl-bits = λ base xs → foldl-go xs $! base
  {-# INLINE foldl-bits #-}

foldl-universal : ∀ (h : Bits → A → A) z o e →
                  (∀ xs bs → h (0∷ xs) bs ≡ h xs (z bs)) →
                  (∀ xs bs → h (1∷ xs) bs ≡ h xs (o bs)) →
                  (∀ bs → h [] bs ≡ bs) →
                  ∀ xs → h xs e ≡ foldl-bits z o e xs
foldl-universal h z o e zer one bs [] = bs e ; sym ($!-≡ (foldl-go z o []) e)
foldl-universal h z o e zer one bs (0∷ xs) = zer xs e ; foldl-universal h z o (z e) zer one bs xs ; sym ($!-≡ (foldl-go z o (0∷ xs)) e)
foldl-universal h z o e zer one bs (1∷ xs) = one xs e ; foldl-universal h z o (o e) zer one bs xs ; sym ($!-≡ (foldl-go z o (1∷ xs)) e)
