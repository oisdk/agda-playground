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
2^ suc m * n = (2^ m * n) * 2

array-foldr : (B : ℕ → Type b)
            → (∀ n m → N n → B (2^ n * m) → B (2^ n * suc m))
            → B 0 → Array N ns → B ⟦ ns ⇓⟧
array-foldr {ns = 0ᵇ} B c b []        = b
array-foldr {ns = 1ᵇ ns} B c b (x 1∷ xs) = c 0 (⟦ ns ⇓⟧ * 2) x (array-foldr (B ∘ (_* 2)) (c ∘ suc) b xs)
array-foldr {ns = 2ᵇ ns} B c b (x 2∷ xs) = c 1 ⟦ ns ⇓⟧         x (array-foldr (B ∘ (_* 2)) (c ∘ suc) b xs)

open import Data.Vec
import Data.Nat.Properties as ℕ

module _ {r} (R : ℕ → Type r) (f : ∀ {x y} → R x → R y → R (x + y)) (nl : R 0) where
  double : ℕ → ℕ
  double n = n + n

  double≡*2 : ∀ n → n + n ≡ n * 2
  double≡*2 zero    = refl
  double≡*2 (suc n) = cong suc (ℕ.+-suc n n ; cong suc (double≡*2 n))

  d : ℕ → ℕ
  d zero    = 1
  d (suc n) = d n + d n

  spine : Vec (R 1) n → Array (R ∘ d) ⟦ n ⇑⟧
  spine [] = []
  spine (x ∷ xs) = cons (λ _ → f) x (spine xs)

  open import Path.Reasoning

  lemma : ∀ n m → d n + (2^ n * m) ≡ 2^ n * suc m
  lemma zero    m = refl
  lemma (suc n) m =
    d n + d n + (2^ n * m) * 2 ≡⟨ cong (_+ (2^ n * m) * 2) (double≡*2 (d n)) ⟩
    d n * 2 + (2^ n * m) * 2 ≡˘⟨ ℕ.+-*-distrib (d n) (2^ n * m) 2 ⟩
    (d n + 2^ n * m) * 2 ≡⟨ cong (_* 2) (lemma n m) ⟩
    (2^ n * suc m) * 2 ∎

  unspine : Array (R ∘ d) ns → R ⟦ ns ⇓⟧
  unspine = array-foldr R (λ n m x xs → subst R (lemma n m) (f x xs)) nl

  treeFold : Vec (R 1) n → R n
  treeFold xs = subst R (𝔹-rightInv _) (unspine (spine xs))
