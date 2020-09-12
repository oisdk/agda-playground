{-# OPTIONS --cubical --safe #-}

module Container.List.Isomorphism where

open import Prelude
open import Container
open import Container.List
open import Data.Fin
open import Data.List using (tabulate; length ; _!_) renaming (_∷_ to _L∷_; [] to L[]; List to 𝕃)
open import Data.List.Properties

ℒ→𝕃 : List A → 𝕃 A
ℒ→𝕃 = uncurry tabulate

𝕃→ℒ : 𝕃 A → List A
𝕃→ℒ xs .fst = length xs
𝕃→ℒ xs .snd i = xs ! i

ℒ→𝕃→ℒ : ∀ n (xs : Fin n → A) → 𝕃→ℒ (ℒ→𝕃 (n , xs)) ≡ (n , xs)
ℒ→𝕃→ℒ n xs i .fst = tab-length n xs i
ℒ→𝕃→ℒ n xs i .snd = tab-id n xs i

𝕃→ℒ→𝕃 : ∀ (xs : 𝕃 A) → ℒ→𝕃 (𝕃→ℒ xs) ≡ xs
𝕃→ℒ→𝕃 L[] _ = L[]
𝕃→ℒ→𝕃 (x L∷ xs) i = x L∷ 𝕃→ℒ→𝕃 xs i

𝕃⇔ℒ : 𝕃 A ⇔ List A
𝕃⇔ℒ .fun = 𝕃→ℒ
𝕃⇔ℒ .inv = ℒ→𝕃
𝕃⇔ℒ .rightInv  = uncurry ℒ→𝕃→ℒ
𝕃⇔ℒ .leftInv = 𝕃→ℒ→𝕃
