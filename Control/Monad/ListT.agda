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

data ℭ𝔬𝔫𝔰 (A : Type ℓ) (P : List A → Type ℓ) : Type ℓ where
  [] : ℭ𝔬𝔫𝔰 A P
  _∷_⟨_⟩ : (x : A) → (xs : List A) → (P⟨xs⟩ : P xs) → ℭ𝔬𝔫𝔰 A P

module _ (P : List A → Type ℓ) where
  wrapc : ℭ𝔬𝔫𝔰 A P → Cons A
  wrapc [] = []
  wrapc (x ∷ xs ⟨ P⟨xs⟩ ⟩) = x ∷ xs

  wrap : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A P) → List A
  wrap = cmap wrapc

  module _ (ψ : (x : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A P)) → P (wrap x)) where
    elim : (x : List A) → P x
    elimc : Cons A → ℭ𝔬𝔫𝔰 A P
    wrapc-elimc : (c : Cons A) → wrapc (elimc c) ≡ c

    wrapc-elimc []       i = []
    wrapc-elimc (x ∷ xs) i = x ∷ xs

    elimc [] = []
    elimc (x ∷ xs) = x ∷ xs ⟨ elim xs ⟩

    elim xs =
      subst
        P
        (cong (xs .fst ,_) (funExt (λ x → wrapc-elimc (xs .snd x))))
        (ψ (cmap elimc xs))

para : (⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A (const B)) → B) → List A → B
para = elim (const _)

infixr 5 _++_
_++_ : List A → List A → List A
_++_ {A = A} xs ys = para ϕ xs
  where
  ϕ : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A (const (List A))) → List A
  ϕ xs = xs >>= λ { [] → ys ; (x ∷ _ ⟨ xs ⟩) → return (x ∷ xs) }

-- open import Cubical.Data.Sigma.Properties

-- ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
-- ++-assoc {A = A} xs ys zs = elim P ψ xs
--   where
--   P : List A → Type ℓ
--   P xs′ = (xs′ ++ ys) ++ zs ≡ xs′ ++ (ys ++ zs)
--   {-# INLINE P #-}

--   ψ : (x : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A P)) → P (wrap P x)
--   ψ xs = ΣPathTransport→PathΣ _ _ ({!refl!} , {!!})

-- _>>=′_ : List A → (A → List B) → List B
-- _>>=′_ {A = A} {B = B} xs k = cata ϕ xs
--   where
--   ϕ : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A (List B)) → List B
--   ϕ xs = xs >>= λ { [] → return [] ; (x ∷ xs) → k x ++ xs }
