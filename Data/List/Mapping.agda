{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Relation.Binary

module Data.List.Mapping {kℓ} {K : Type kℓ} {r₁ r₂} (totalOrder : TotalOrder K r₁ r₂) where

open import Relation.Binary.Construct.Decision totalOrder
open import Relation.Binary.Construct.LowerBound dec-ord
open import Data.Nat using (_+_)
open TotalOrder lb-ord using (<-trans) renaming (refl to <-refl)
import Data.Unit.UniversePolymorphic as Poly
open import Data.Maybe.Properties using (IsJust)
open TotalOrder dec-ord using (_<?_; _<_; total⇒isSet; irrefl; compare)

instance
  top-inst : Poly.⊤ {ℓzero}
  top-inst = Poly.tt

private
  variable
    n m : ℕ
    v : Level
    Val : K → Type v

infixr 5 _︓_,_
data MapFrom (lb : ⌊∙⌋) {v} (Val : K → Type v) : Type (kℓ ℓ⊔ r₁ ℓ⊔ v) where
  ∅ : MapFrom lb Val
  _︓_,_ : (k : K) → ⦃ inBounds : lb <⌊ k ⌋ ⦄ → (v : Val k) → MapFrom ⌊ k ⌋ Val → MapFrom lb Val

private
  variable
    lb : ⌊∙⌋

weaken : ∀ {x} → ⦃ _ : lb <⌊ x ⌋ ⦄ → MapFrom ⌊ x ⌋ Val → MapFrom lb Val
weaken ∅ = ∅
weaken {lb = lb} {x = x} (k ︓ val , xs) = k ︓ val , xs
  where
    instance
      _ : lb <⌊ k ⌋
      _ = <-trans {x = lb} {y = ⌊ x ⌋} {z = ⌊ k ⌋} it it

-- module _ {v} {Val : K → Type v} where
--   _[_]? : MapFrom lb Val → (k : K) ⦃ inBounds : lb <⌊ k ⌋ ⦄ → Maybe (Val k)
--   ∅ [ k ]? = nothing
--   k₂ ︓ v , xs [ k₁ ]? = case compare k₁ k₂ of
--     λ { (lt _) → nothing ;
--         (eq _) → just (subst Val (sym it) v) ;
--         (gt _) → xs [ k₁ ]? }
--   infixl 4 _[_]?

-- --   _[_]︓_ : MapFrom lb Val → (k : K) ⦃ inBounds : lb <⌊ k ⌋ ⦄ → (val : Val k) → MapFrom lb Val
-- --   ∅ [ k₁ ]︓ v₁ = k₁ ︓ v₁ , ∅
-- --   (k₂ ︓ v₂ , xs) [ k₁ ]︓ v₁ =
-- --     comparing k₁ ∙ k₂
-- --       |< k₁ ︓ v₁ , k₂ ︓ v₂ , xs
-- --       |≡ k₂ ︓ subst Val it v₁ , xs
-- --       |> k₂ ︓ v₂ , (xs [ k₁ ]︓ v₁)
-- --   infixl 4 _[_]︓_

-- --   _[_]︓∅ : MapFrom lb Val → (k : K) ⦃ inBounds : lb <⌊ k ⌋ ⦄ → MapFrom lb Val
-- --   ∅ [ k₁ ]︓∅ = ∅
-- --   (k₂ ︓ v₂ , xs) [ k₁ ]︓∅ = comparing k₁ ∙ k₂
-- --       |< k₂ ︓ v₂ , xs
-- --       |≡ weaken xs
-- --       |> k₂ ︓ v₂ , (xs [ k₁ ]︓∅)
-- --   infixl 4 _[_]︓∅

-- -- infixr 0 Map
-- -- Map : ∀ {v} (Val : K → Type v) → Type _
-- -- Map = MapFrom ⌊⊥⌋

-- -- syntax Map (λ s → e) = s ↦ e

-- -- Map′ : ∀ {v} (Val : Type v) → Type _
-- -- Map′ V = Map (const V)

-- -- infixr 5 _≔_,_
-- -- data RecordFrom (lb : ⌊∙⌋) : MapFrom lb (const Type) → Type (kℓ ℓ⊔ r₁ ℓ⊔ ℓsuc ℓzero) where
-- --   ∅ : RecordFrom lb ∅
-- --   _≔_,_ : (k : K) → ⦃ inBounds : lb <⌊ k ⌋ ⦄ → {xs : MapFrom ⌊ k ⌋ (const Type)} {t : Type} → (v : t) → RecordFrom ⌊ k ⌋ xs → RecordFrom lb (k ︓ t , xs)

-- -- Record : Map′ Type → Type _
-- -- Record = RecordFrom ⌊⊥⌋

-- -- infixr 5 _∈_
-- -- _∈_ : (k : K) → ⦃ inBounds : lb <⌊ k ⌋ ⦄ → MapFrom lb Val → Type
-- -- k ∈ xs = IsJust (xs [ k ]?)

-- -- _[_]! : (xs : MapFrom lb Val) → (k : K) → ⦃ inBounds : lb <⌊ k ⌋ ⦄ → ⦃ k∈xs : k ∈ xs ⦄ → Val k
-- -- xs [ k ]! with xs [ k ]? | inspect (_[_]? xs) k
-- -- xs [ k ]! | just x  | _ = x
-- -- xs [ k ]! | nothing | _ = ⊥-elim it

-- -- infixl 4 _[_]
-- -- _[_] : {xs : MapFrom lb (const Type)} → RecordFrom lb xs → (k : K) ⦃ inBounds : lb <⌊ k ⌋ ⦄ ⦃ k∈xs : k ∈ xs ⦄ → xs [ k ]!
-- -- _[_] {xs = xs} (k₂ ≔ v , r) k₁ with xs [ k₁ ]? | compare′ k₁ k₂
-- -- (k₂ ≔ v , r) [ k₁ ] | _ | lt′ = ⊥-elim it
-- -- (k₂ ≔ v , r) [ k₁ ] | _ | eq′ = v
-- -- (k₂ ≔ v , r) [ k₁ ] | _ | gt′ = r [ k₁ ]

-- -- infixl 4 _[_]≔_
-- -- _[_]≔_ : {xs : MapFrom lb (const Type)} → RecordFrom lb xs → (k : K) ⦃ inBounds : lb <⌊ k ⌋ ⦄ → A → RecordFrom lb (xs [ k ]︓ A)
-- -- ∅ [ k ]≔ x = k ≔ x , ∅
-- -- (k₂ ≔ v₁ , rs) [ k₁ ]≔ x with compare′ k₁ k₂
-- -- (k₂ ≔ v₁ , rs) [ k₁ ]≔ x | lt′ = k₁ ≔ x , k₂ ≔ v₁ , rs
-- -- (k₂ ≔ v₁ , rs) [ k₁ ]≔ x | eq′ = k₂ ≔ x , rs
-- -- (k₂ ≔ v₁ , rs) [ k₁ ]≔ x | gt′ = k₂ ≔ v₁ , (rs [ k₁ ]≔ x)
