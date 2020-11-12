{-# OPTIONS --cubical --safe #-}

module TreeFold where

open import Prelude
open import Data.Binary
import Data.Nat as ℕ

private
  variable
    n m : ℕ
    t : Level
    N : ℕ → Type t
    ns : 𝔹

infixr 5 _1∷_ _2∷_
data Array (T : ℕ → Type a) : 𝔹 → Type a where
  []  : Array T 0ᵇ
  _1∷_ : T 0 → Array (T ∘ suc) ns → Array T (1ᵇ ns)
  _2∷_ : T 1 → Array (T ∘ suc) ns → Array T (2ᵇ ns)

cons : (∀ n → N n → N n → N (suc n)) → N 0 → Array N ns → Array N (inc ns)
cons branch x [] = x 1∷ []
cons branch x (y 1∷ ys) = branch 0 x y 2∷ ys
cons branch x (y 2∷ ys) = x 1∷ cons (branch ∘ suc) y ys

2^_*_ : ℕ → ℕ → ℕ
2^ zero  * n = n
2^ suc m * n = (2^ m * n) ℕ.* 2

array-foldr : (B : ℕ → Type b)
            → (∀ n m → N n → B (2^ n * m) → B (2^ n * suc m))
            → B 0 → Array N ns → B ⟦ ns ⇓⟧
array-foldr {ns = 0ᵇ} B c b []        = b
array-foldr {ns = 1ᵇ ns} B c b (x 1∷ xs) = c 0 (⟦ ns ⇓⟧ ℕ.* 2) x (array-foldr (B ∘ (ℕ._* 2)) (c ∘ suc) b xs)
array-foldr {ns = 2ᵇ ns} B c b (x 2∷ xs) = c 1 ⟦ ns ⇓⟧         x (array-foldr (B ∘ (ℕ._* 2)) (c ∘ suc) b xs)

-- treeFold : (N n → N m → N (n + m)) → N 0 → Vec A n → N n
