{-# OPTIONS --cubical --safe #-}

module TreeFold where

open import Prelude
open import Data.Binary using (𝔹; 0ᵇ; 1ᵇ_; 2ᵇ_; ⟦_⇓⟧; ⟦_⇑⟧; inc)
open import Data.Binary.Isomorphism
open import Data.Nat


private
  variable
    n m : ℕ
    t : Level
    N : ℕ → Type t
    ns : 𝔹

double : ℕ → ℕ
double n = n * 2

2^_*_ : ℕ → ℕ → ℕ
2^ zero  * m = m
2^ suc n * m = double (2^ n * m)

infixr 5 _1∷_ _2∷_
data Array (T : ℕ → Type a) : 𝔹 → Type a where
  []  : Array T 0ᵇ
  _1∷_ : T 1 → Array (T ∘ double) ns → Array T (1ᵇ ns)
  _2∷_ : T 2 → Array (T ∘ double) ns → Array T (2ᵇ ns)

cons : (∀ n → N n → N n → N (double n)) → N 1 → Array N ns → Array N (inc ns)
cons branch x [] = x 1∷ []
cons branch x (y 1∷ ys) = branch 1 x y 2∷ ys
cons branch x (y 2∷ ys) = x 1∷ cons (branch ∘ double) y ys

array-foldr : (N : ℕ → Type t) → (∀ n m → N (2^ n * 1) → N (2^ n * m) → N (2^ n * suc m)) → N 0 → Array N ns → N ⟦ ns ⇓⟧
array-foldr {ns = 0ᵇ}    N c b []        = b
array-foldr {ns = 2ᵇ ns} N c b (x 2∷ xs) = c 1 ⟦ ns ⇓⟧       x (array-foldr (N ∘ double) (c ∘ suc) b xs)
array-foldr {ns = 1ᵇ ns} N c b (x 1∷ xs) = c 0 (⟦ ns ⇓⟧ * 2) x (array-foldr (N ∘ double) (c ∘ suc) b xs)

open import Data.Vec
import Data.Nat.Properties as ℕ

double≡*2 : ∀ n → n + n ≡ n * 2
double≡*2 zero    = refl
double≡*2 (suc n) = cong suc (ℕ.+-suc n n ; cong suc (double≡*2 n))

module _ {t} (N : ℕ → Type t) (f : ∀ p n m → N (2^ p * n) → N (2^ p * m) → N (2^ p * (n + m))) (z : N 0) where
  spine : Vec (N 1) n → Array (N ) ⟦ n ⇑⟧
  spine [] = []
  spine (x ∷ xs) = cons (λ n x y → subst N (double≡*2 n) (f 0 n n x y)) x (spine xs)

  unspine : Array N ns → N ⟦ ns ⇓⟧
  unspine = array-foldr N (λ n → f n 1) z

  treeFold : Vec (N 1) n → N n
  treeFold xs = subst N (𝔹-rightInv _) (unspine (spine xs))
