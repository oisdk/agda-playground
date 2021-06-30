{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Algebra
open import Container

module Control.Monad.ListT
  {ℓ}
  (𝔽 : Container ℓ ℓ)
  (is-mon : IsMonad {ℓ} ⟦ 𝔽 ⟧ )
  where

open IsMonad is-mon

infixr 5 _∷_
mutual
  List : Type ℓ → Type _
  List A = ⟦ 𝔽 ⟧ (Cons A)

  data Cons (A : Type ℓ) : Type ℓ where
    []  : Cons A
    _∷_ : (x : A) → (xs : List A) → Cons A

data ℭ𝔬𝔫𝔰 (A : Type ℓ) (B : Type ℓ) : Type ℓ where
  [] : ℭ𝔬𝔫𝔰 A B
  _∷_ : (x : A) → (xs : B) → ℭ𝔬𝔫𝔰 A B

cata : (⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A B) → B) → List A → B
cata ϕ (s , p) = ϕ (s , λ i → case p i of λ { [] → [] ; (x ∷ xs) → x ∷ cata ϕ xs })

infixr 5 _++_
_++_ : List A → List A → List A
_++_ {A = A} xs ys = cata ϕ xs
  where
  ϕ : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A (List A)) → List A
  ϕ xs = xs >>= λ { [] → ys ; (x ∷ xs) → return (x ∷ xs) }

_>>=′_ : List A → (A → List B) → List B
_>>=′_ {A = A} {B = B} xs k = cata ϕ xs
  where
  ϕ : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A (List B)) → List B
  ϕ xs = xs >>= λ { [] → return [] ; (x ∷ xs) → k x ++ xs }
