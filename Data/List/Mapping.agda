{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Relation.Binary

module Data.List.Mapping {k} {K : Type k} {r₁ r₂} (totalOrder : TotalOrder K r₁ r₂) where

open import Relation.Binary.Construct.LowerBound totalOrder
open import Data.Nat using (_+_)
open TotalOrder totalOrder using (_<?_; compare; InstOrdering; lt′; eq′; gt′; _<_; compare′; total⇒isSet; irrefl; toInstOrd)
open TotalOrder lb-ord using (<-trans) renaming (refl to <-refl)
-- import Data.Empty.UniversePolymorphic as Poly

private
  variable
    n m : ℕ
    v : Level
    Val : K → Type v

infixr 5 _≔_,_
data MapFrom (lb : ⌊∙⌋) {v} (Val : K → Type v) : Type (k ℓ⊔ r₁ ℓ⊔ v) where
  ∅ : MapFrom lb Val
  _≔_,_ : (key : K) → ⦃ inBounds : lb <⌊ key ⌋ ⦄ → (val : Val key) → MapFrom ⌊ key ⌋ Val → MapFrom lb Val

private
  variable
    lb : ⌊∙⌋

weaken : ∀ {x} → ⦃ _ : lb <⌊ x ⌋ ⦄ → MapFrom ⌊ x ⌋ Val → MapFrom lb Val
weaken ∅ = ∅
weaken {lb = lb} {x = x} (key ≔ val , xs) = key ≔ val , xs
  where
    instance
      p : lb <⌊ key ⌋
      p = <-trans {x = lb} {y = ⌊ x ⌋} {z = ⌊ key ⌋} it it



module _ {v} {Val : K → Type v} where
  lookup : (key : K) ⦃ inBounds : lb <⌊ key ⌋ ⦄ → MapFrom lb Val → Maybe (Val key)
  lookup key ∅ = nothing
  lookup k₁ (k₂ ≔ v , xs) with compare′ k₁ k₂
  ... | lt′ = nothing
  ... | eq′ = just (subst Val (sym it) v)
  ... | gt′ = lookup k₁ xs

  insert : (key : K) ⦃ inBounds : lb <⌊ key ⌋ ⦄ → (val : Val key) → MapFrom lb Val → MapFrom lb Val
  insert k₁ v₁ ∅ = k₁ ≔ v₁ , ∅
  insert k₁ v₁ (k₂ ≔ v₂ , xs) with compare′ k₁ k₂
  ... | lt′ = k₁ ≔ v₁ , k₂ ≔ v₂ , xs
  ... | eq′ = k₂ ≔ subst Val it v₁ , xs
  ... | gt′ = k₂ ≔ v₂ , insert k₁ v₁ xs

  delete : (key : K) ⦃ inBounds : lb <⌊ key ⌋ ⦄ → MapFrom lb Val → MapFrom lb Val
  delete k₁ ∅ = ∅
  delete k₁ (k₂ ≔ v₂ , xs) with compare′ k₁ k₂
  ... | lt′ = k₂ ≔ v₂ , xs
  ... | eq′ = weaken xs
  ... | gt′ = k₂ ≔ v₂ , delete k₁ xs


  open import Lens
  open import Lens.Operators

--   lookup-delete : (key : K) ⦃ inBounds : lb <⌊ key ⌋ ⦄ → (xs : MapFrom lb Val) → lookup key (delete key xs) ≡ nothing
--   lookup-delete _ ∅ = refl
--   lookup-delete k₁ (k₂ ≔ v , xs) with compare′ k₁ k₂ | inspect (compare′ k₁) k₂
--   lookup-delete k₁ (k₂ ≔ v , xs) | lt′ | 〖 p 〗 = {!!}
--   lookup-delete k₁ (k₂ ≔ v , xs) | eq′ | p = {!!}
--   lookup-delete k₁ (k₂ ≔ v , xs) | gt′ | p = {!!}


--   ! : (key : K) → ⦃ inBounds : lb <⌊ key ⌋ ⦄ → Lens (MapFrom lb Val) (Maybe (Val key))
--   ! key .into xs .get = lookup key xs
--   ! key .into xs .set (just v) = insert key v xs
--   ! key .into xs .set nothing  = delete key xs
--   ! key .get-set s nothing  = {!!}
--   ! key .get-set s (just x) = {!!}
--   ! key .set-get s = {!!}
--   ! key .set-set s v₁ v₂ = {!!}


-- -- module _ {v} {Val : K → Type v} where
-- --  mutual
-- --   viewSing : (k₁ k₂ : K) ⦃ inBounds₁ : lb <⌊ k₁ ⌋ ⦄ ⦃ inBounds₂ : lb <⌊ k₂ ⌋ ⦄ →
-- --             (val : Val k₂) →
-- --             (xs : MapFrom ⌊ k₂ ⌋ Val) →
-- --             InstOrdering k₁ k₂ →
-- --             LensPart (MapFrom lb Val) (Maybe (Val k₁))
-- --   viewSing k₁ k₂ val xs lt′ .get = nothing
-- --   viewSing k₁ k₂ val xs lt′ .set nothing = k₂ ≔ val , xs
-- --   viewSing k₁ k₂ val xs lt′ .set (just x) = k₁ ≔ x , k₂ ≔ val , xs
-- --   viewSing k₁ k₂ val xs eq′ .get = just (subst Val (sym it) val)
-- --   viewSing k₁ k₂ val xs eq′ .set nothing = weaken xs
-- --   viewSing k₁ k₂ val xs eq′ .set (just x) = k₂ ≔ (subst Val it x) , xs
-- --   viewSing k₁ k₂ val xs gt′ = map-lens-part (view k₁ xs) (k₂ ≔ val ,_)

-- --   view : (key : K) → ⦃ inBounds : lb <⌊ key ⌋ ⦄ → MapFrom lb Val → LensPart (MapFrom lb Val) (Maybe (Val key))
-- --   view k₁ ∅ .get = nothing
-- --   view k₁ ∅ .set nothing = ∅
-- --   view k₁ ∅ .set (just x) = k₁ ≔ x , ∅
-- --   view k₁ (k₂ ≔ v , xs) = viewSing k₁ k₂ v xs (compare′ k₁ k₂)

-- -- open import Cubical.Foundations.Prelude using (substRefl)
-- -- open import Path.Reasoning


-- -- -- module _ {v} {Val : K → Type v} where
-- -- --   view-get-set : (key : K) (s : MapFrom lb Val) (v : Maybe (Val key)) → ⦃ _ : lb <⌊ key ⌋ ⦄ → view key (view key s .set v) .get ≡ v
-- -- --   view-get-set k₁ ∅ nothing = refl
-- -- --   view-get-set k₁ ∅ (just x) with compare k₁ k₁
-- -- --   view-get-set k₁ ∅ (just x) | lt p = ⊥-elim (irrefl p refl)
-- -- --   view-get-set k₁ ∅ (just x) | eq _ = cong just (cong (λ p → subst Val p x) (total⇒isSet  _ _ _ _) ; substRefl {B = Val} x)
-- -- --   view-get-set k₁ ∅ (just x) | gt p = ⊥-elim (irrefl p refl)

-- --   -- view-get-set k₁ (k₂ ≔ val , s) v with compare′ k₁ k₂ | inspect (compare′ k₁) k₂
-- --   -- view-get-set k₁ (k₂ ≔ val , s) nothing  | lt′ | 〖 q 〗 = cong (get ∘ viewSing k₁ k₂ val s) q
-- --   -- view-get-set k₁ (k₂ ≔ val , s) (just v) | lt′ | _ = {!!}
-- --   -- view-get-set k₁ (k₂ ≔ val , s) nothing  | eq′ | _ = {!!}
-- --   -- view-get-set k₁ (k₂ ≔ val , s) (just v) | eq′ | _ = {!!}
-- --   -- view-get-set k₁ (k₂ ≔ val , s) nothing  | gt′ | _ = {!!}
-- --   -- view-get-set k₁ (k₂ ≔ val , s) (just v) | gt′ | 〖 q 〗 =
-- --   --   viewSing k₁ k₂ val (set (view k₁ s) (just v)) (compare′ k₁ k₂) .get ≡⟨ cong (get ∘ viewSing k₁ k₂ val (set (view k₁ s) (just v))) q ⟩
-- --   --   viewSing k₁ k₂ val (set (view k₁ s) (just v)) gt′  .get ≡⟨ {!!} ⟩
-- --   --   just v ∎


