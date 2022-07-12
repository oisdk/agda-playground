{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra

module Control.Monad.Weighted.Depth {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import HLevels
open import Prelude

open import Control.Monad.Weighted rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Functor rng hiding (⟪_⟫)

fmap : (A → B) → Weighted A → Weighted B
fmap f xs = xs >>= (pure ∘ f)

infixr 4.5 _◁_
record _◁_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  coinductive; no-eta-equality
  constructor _◀_
  field
    root : A
    rest : B
open _◁_ public

map-rest : (B → C) → A ◁ B → A ◁ C
map-rest f xs .root = xs .root
map-rest f xs .rest = f (xs .rest)

mutual

  data Depth (A : Type a) : Type (ℓ ℓ⊔ a) where
    ⟪_⟫ : Weighted (A ◁ (Depth A)) → Depth A
    flat : (xs : Weighted (A ◁ Weighted (A ◁ Depth A))) → ⟪ flat-lhs xs ⟫  ≡ ⟪ flat-rhs xs ⟫
    ⟪trunc⟫ : isSet (Depth A)

  flat-lhs : Weighted (A ◁ Weighted (A ◁ Depth A)) → Weighted (A ◁ Depth A)
  flat-lhs xs = xs >>= (λ x◀xs → 1# ◃ root x◀xs ◀ ⟪ [] ⟫ ∷ rest x◀xs)

  flat-rhs : Weighted (A ◁ Weighted (A ◁ Depth A)) → Weighted (A ◁ Depth A)
  flat-rhs = fmap (map-rest ⟪_⟫)

record Proven {p} {A : Type a} (P : Depth A → Type p) : Type (a ℓ⊔ ℓ ℓ⊔ p) where
  no-eta-equality; constructor proven
  field
    vals : Depth A
    proof : P vals
open Proven

Depth-Alg : (A : Type a) → (Depth A → Type b) → Type _
Depth-Alg A P = (fs : Weighted (A ◁ Proven P)) → P ⟪ fmap (map-rest vals) fs ⟫

private
  variable
    p q : Level
    P : Depth A → Type p
    Q : Depth A → Type q



module _ {A : Type a} {P : Depth A → Type p} where
  
  deep′ : A ◁ Proven P → A ◁ Depth A
  deep′ = map-rest vals

-- Goal: P ⟪ flat-lhs (fmap (map-rest (fmap (map-rest fst))) xs) ⟫

--         ⟪
--         fmap (map-rest fst)
--         (xs >>= (λ { xxs → 1# ◃ root xxs ◀ (⟪ [] ⟫ , ψ []) ∷ rest xxs }))
--         ⟫

  -- lemma : (xs : Weighted (A × Weighted (A × Proven P))) →
  --         ⟪ xs >>= (λ { (x , xs) → 1# ◃ (x ◀ ⟪ [] ⟫) ∷ fmap deep′ xs }) ⟫ ≡ ⟪ fmap (map-rest (⟪_⟫ ∘  fmap deep′)) xs ⟫
  -- lemma = {!!}

  module _ (ψ : Depth-Alg A P) where

    lemma-lhs : (xs : Weighted (A ◁ (Weighted (A ◁ Proven P))))
              → ⟪ fmap deep′ (xs >>= (λ xxs → 1# ◃ root xxs ◀ (proven ⟪ [] ⟫ (ψ [])) ∷ rest xxs)) ⟫
              ≡ ⟪ flat-lhs (fmap (map-rest (fmap deep′)) xs) ⟫
    lemma-lhs = {!!}

    lemma-rhs : (xs : Weighted (A ◁ (Weighted (A ◁ Proven P))))
              → ⟪ fmap deep′ (fmap (map-rest (λ ys → proven ⟪ fmap deep′ ys ⟫ (ψ ys))) xs) ⟫
              ≡ ⟪ flat-rhs (fmap (map-rest (fmap deep′)) xs) ⟫
    lemma-rhs = {!!}

    lemma-flat : (xs : Weighted (A ◁ (Weighted (A ◁ Proven P))))
              → ⟪ fmap deep′ (xs >>= (λ xxs → 1# ◃ root xxs ◀ (proven ⟪ [] ⟫ (ψ [])) ∷ rest xxs)) ⟫
              ≡ ⟪ fmap deep′ (fmap (map-rest (λ xs₁ → proven ⟪ fmap deep′ xs₁ ⟫ (ψ xs₁))) xs) ⟫
    lemma-flat xs = lemma-lhs xs ; flat (fmap (map-rest (fmap deep′)) xs) ; sym (lemma-rhs xs)

    lhs-flat : (xs : Weighted (A ◁ (Weighted (A ◁ Proven P))))
             → P ⟪ fmap deep′ (xs >>= (λ xxs → 1# ◃ root xxs ◀ (proven ⟪ [] ⟫ (ψ [])) ∷ rest xxs)) ⟫
    lhs-flat xs = ψ (xs >>= (λ xxs → 1# ◃ root xxs ◀ (proven ⟪ [] ⟫ (ψ [])) ∷ rest xxs))

    rhs-flat : (xs : Weighted (A ◁ (Weighted (A ◁ Proven P))))
             → P ⟪ fmap (map-rest (vals {P = P})) (fmap (map-rest (λ ys → proven ⟪ fmap deep′ ys ⟫ (ψ ys))) xs) ⟫
    rhs-flat xs = ψ (fmap (map-rest (λ xs → proven ⟪ fmap deep′ xs ⟫ (ψ xs))) xs)

    record Depth-Coh : Type (p ℓ⊔ a ℓ⊔ ℓ) where
      field
        d-set  : ∀ xs → isSet (P xs)
        d-flat : (xs : Weighted (A ◁ (Weighted (A ◁ Proven P))))
              → let lhs = ψ (xs >>= (λ xxs → (1# ⦂ 𝑅) ◃ root xxs ◀ (proven ⟪ [] ⟫ (ψ [])) ∷ rest xxs))
                    rhs = ψ (fmap (map-rest (λ xs → proven ⟪ fmap deep′ xs ⟫ (ψ xs))) xs)
                in PathP (λ i → P (lemma-flat xs i)) lhs rhs

open Depth-Coh

Ψ-Depth : (A : Type a) (P : Depth A → Type p) → Type _
Ψ-Depth A P = Σ (Depth-Alg A P) Depth-Coh

module _ {A : Type a} {P : Depth A → Type p} where
  {-# TERMINATING #-}
  ⟦_⟧D : Ψ-Depth A P → (xs : Depth A) → P xs
  ⟦ ψ ⟧D ⟪ xs ⟫ = subst P {!!} (ψ .fst (fmap (map-rest (λ x → proven x (⟦ ψ ⟧D x) )) xs))
  ⟦ ψ ⟧D (flat xs i) = let q = ψ .snd .d-flat (fmap (map-rest (fmap (map-rest (λ x → proven x (⟦ ψ ⟧D x))))) xs) in {!!}
  ⟦ ψ ⟧D (⟪trunc⟫ xs ys p q i j) =

    isOfHLevel→isOfHLevelDep 2
      (ψ .snd .d-set)
      (⟦ ψ ⟧D xs) (⟦ ψ ⟧D ys)
      (cong ⟦ ψ ⟧D p) (cong ⟦ ψ ⟧D q)
      (⟪trunc⟫ xs ys p q)
      i j

  -- Φ-depth : Type a → Type b → Type (a ℓ⊔ b ℓ⊔ ℓ)
  -- Φ-depth A B = Φ (A × B) B


  -- rec-depth : (ϕ : Φ-depth A B)
  --           → isSet B
  --           → 
  --           → Depth A → B
  -- rec-depth ϕ set f ⟪ x ⟫ = ⟦ {!!} ⟧ x
  -- rec-depth ϕ set f (flat xs i) = {!!}
  -- rec-depth ϕ set f (⟪trunc⟫ xs ys p q i j) =
  --   isOfHLevel→isOfHLevelDep 2
  --     (λ _ → set)
  --     (rec-depth ϕ set f xs) (rec-depth ϕ set f ys)
  --     (cong (rec-depth ϕ set f) p) (cong (rec-depth ϕ set f) q)
  --     (⟪trunc⟫ xs ys p q)
  --     i j
