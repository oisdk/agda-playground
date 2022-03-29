{-# OPTIONS --cubical --postfix-projections #-}

open import Prelude
open import Algebra
open import Container

module Control.Monad.ListT
  {ℓ}
  (𝔽 : Container ℓ ℓ)
  (is-mon : Monad {ℓ} ⟦ 𝔽 ⟧ )
  where

open Monad is-mon

postulate
  cmap-return : (f : A → B) (x : ⟦ 𝔽 ⟧ A) →
                (cmap f x ≡ (x >>= return ∘ f))


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
  {-# INLINE wrap #-}

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

module _  (ϕ : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A (const B)) → B) where
  para : List A → B
  parac : Cons A → ℭ𝔬𝔫𝔰 A (const B)


  para xs = ϕ (cmap parac xs)

  parac [] = []
  parac (x ∷ xs) = x ∷ xs ⟨ para xs ⟩

++-ϕ : List A → ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A (const (List A))) → List A
++-ϕ ys xs = xs >>= λ { [] → ys ; (x ∷ _ ⟨ xs ⟩) → return (x ∷ xs) }

infixr 5 _++_
_++_ : List A → List A → List A
xs ++ ys = para (++-ϕ ys) xs

cmap-comp : (f : B → C) (g : A → B) (x : ⟦ 𝔽 ⟧ A) → cmap f (cmap g x) ≡ cmap (f ∘ g) x
cmap-comp f g x = refl

cmap-id : (x : ⟦ 𝔽 ⟧ A) → cmap id x ≡ x
cmap-id x = refl

open import Path.Reasoning

++-id : (xs : List A) → xs ++ return [] ≡ xs
++-id {A = A} = elim P ψ
  where
  P : List A → Type ℓ
  P xs = xs ++ return [] ≡ xs

  ϕ : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A (const (List A))) → List A
  ϕ = ++-ϕ (return [])

  ϕ′ : ℭ𝔬𝔫𝔰 A (const (List A)) → Cons A
  ϕ′ [] = []
  ϕ′ (x ∷ xs ⟨ P⟨xs⟩ ⟩) = x ∷ P⟨xs⟩

  ϕ≡ : ∀ xs → ϕ xs ≡ (xs >>= return ∘′ ϕ′)
  ϕ≡ xs = cong (xs >>=_) (funExt (λ { [] → refl ; (x ∷ xs ⟨ P⟨xs⟩ ⟩) → refl }))

  lemma : (xs : ℭ𝔬𝔫𝔰 A P) → ϕ′ (parac ϕ (wrapc P xs)) ≡ wrapc P xs
  lemma [] = refl
  lemma (x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (x ∷_) P⟨xs⟩

  ψ : (xs : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A P)) → P (wrap P xs)
  ψ xs =
    wrap P xs ++ return [] ≡⟨⟩
    para ϕ (wrap P xs) ≡⟨⟩
    ϕ (cmap (parac ϕ) (wrap P xs)) ≡⟨ ϕ≡ _ ⟩
    (cmap (parac ϕ) (wrap P xs) >>= return ∘′ ϕ′) ≡˘⟨ cmap-return ϕ′ _ ⟩
    cmap ϕ′ (cmap (parac ϕ) (wrap P xs)) ≡⟨⟩
    cmap (ϕ′ ∘ parac ϕ) (wrap P xs) ≡⟨⟩
    cmap (ϕ′ ∘ parac ϕ) (cmap (wrapc P) xs) ≡⟨⟩
    cmap (ϕ′ ∘ parac ϕ ∘ wrapc P) xs ≡⟨ cong (flip cmap xs) (funExt lemma) ⟩
    wrap P xs ∎


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
-- _>>=′_ {A = A} {B = B} xs k = para ϕ xs
--   where
--   ϕ : ⟦ 𝔽 ⟧ (ℭ𝔬𝔫𝔰 A (List B)) → List B
--   ϕ xs = xs >>= λ { [] → return [] ; (x ∷ xs) → k x ++ xs }
