{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Relation.Binary

module Data.List.Mapping {kℓ} {K : Type kℓ} {r₁ r₂} (totalOrder : TotalOrder K r₁ r₂) where

open import Relation.Binary.Construct.LowerBound totalOrder
open import Data.Nat using (_+_)
open TotalOrder totalOrder using (_<?_; compare; _<_; total⇒isSet; irrefl; comparing_∙_|<_|≡_|>_; compare′; compared)
open TotalOrder lb-ord using (<-trans) renaming (refl to <-refl)
-- import Data.Empty.UniversePolymorphic as Poly

private
  variable
    n m : ℕ
    v : Level
    Val : K → Type v

infixr 5 _≔_,_
data MapFrom (lb : ⌊∙⌋) {v} (Val : K → Type v) : Type (kℓ ℓ⊔ r₁ ℓ⊔ v) where
  ∅ : MapFrom lb Val
  _≔_,_ : (k : K) → ⦃ inBounds : lb <⌊ k ⌋ ⦄ → (v : Val k) → MapFrom ⌊ k ⌋ Val → MapFrom lb Val

private
  variable
    lb : ⌊∙⌋

weaken : ∀ {x} → ⦃ _ : lb <⌊ x ⌋ ⦄ → MapFrom ⌊ x ⌋ Val → MapFrom lb Val
weaken ∅ = ∅
weaken {lb = lb} {x = x} (k ≔ val , xs) = k ≔ val , xs
  where
    instance
      p : lb <⌊ k ⌋
      p = <-trans {x = lb} {y = ⌊ x ⌋} {z = ⌊ k ⌋} it it

module _ {v} {Val : K → Type v} where
  lookup : (k : K) ⦃ inBounds : lb <⌊ k ⌋ ⦄ → MapFrom lb Val → Maybe (Val k)
  lookup k ∅ = nothing
  lookup k₁ (k₂ ≔ v , xs) = comparing k₁ ∙ k₂
     |< nothing
     |≡ just (subst Val (sym it) v)
     |> lookup k₁ xs

  infixl 4 lookup
  syntax lookup k xs = xs [ k ]

  insert : (k : K) ⦃ inBounds : lb <⌊ k ⌋ ⦄ → (val : Val k) → MapFrom lb Val → MapFrom lb Val
  insert k₁ v₁ ∅ = k₁ ≔ v₁ , ∅
  insert k₁ v₁ (k₂ ≔ v₂ , xs) =
    comparing k₁ ∙ k₂
      |< k₁ ≔ v₁ , k₂ ≔ v₂ , xs
      |≡ k₂ ≔ subst Val it v₁ , xs
      |> k₂ ≔ v₂ , insert k₁ v₁ xs

  infixl 4 insert
  syntax insert k v xs = xs [ k ]≔ v

  delete : (k : K) ⦃ inBounds : lb <⌊ k ⌋ ⦄ → MapFrom lb Val → MapFrom lb Val
  delete k₁ ∅ = ∅
  delete k₁ (k₂ ≔ v₂ , xs) = comparing k₁ ∙ k₂
      |< k₂ ≔ v₂ , xs
      |≡ weaken xs
      |> k₂ ≔ v₂ , delete k₁ xs

  infixl 4 delete
  syntax delete k xs = xs [ k ]∅

  -- open import Lens
  -- open import Lens.Operators

--   lookup-delete : (k : K) ⦃ inBounds : lb <⌊ k ⌋ ⦄ → (xs : MapFrom lb Val) → lookup k (delete k xs) ≡ nothing
--   lookup-delete _ ∅ = refl
--   lookup-delete k₁ (k₂ ≔ v , xs) with compare′ k₁ k₂ | inspect (compare′ k₁) k₂
--   lookup-delete k₁ (k₂ ≔ v , xs) | lt′ | 〖 p 〗 = {!!}
--   lookup-delete k₁ (k₂ ≔ v , xs) | eq′ | p = {!!}
--   lookup-delete k₁ (k₂ ≔ v , xs) | gt′ | p = {!!}

--   delete-delete : (k : K) → ⦃ inBounds : lb <⌊ k ⌋ ⦄ → (xs : MapFrom lb Val) → delete k (delete k xs) ≡ delete k xs
--   delete-delete k₁ ∅ = refl
--   delete-delete k₁ (k₂ ≔ v , xs) with compare k₁ k₂ | inspect (compare k₁) k₂
--   delete-delete k₁ (k₂ ≔ v , xs) | lt q | 〖 p 〗 = {!!}
--   delete-delete k₁ (k₂ ≔ v , xs) | eq q | 〖 p 〗 = {!!}
--   delete-delete k₁ (k₂ ≔ v , xs) | gt q | 〖 p 〗 = {!!}


--   ! : (k : K) → ⦃ inBounds : lb <⌊ k ⌋ ⦄ → Lens (MapFrom lb Val) (Maybe (Val k))
--   ! k .into xs .get = lookup k xs
--   ! k .into xs .set (just v) = insert k v xs
--   ! k .into xs .set nothing  = delete k xs
--   ! k .get-set s nothing  = {!!}
--   ! k .get-set s (just x) = {!!}
--   ! k .set-get s = {!!}
--   ! k .set-set s nothing nothing = {!!}
--   ! k .set-set s nothing (just x) = {!!}
--   ! k .set-set s (just x) nothing = {!!}
--   ! k .set-set s (just x) (just y) = {!!}


-- -- -- module _ {v} {Val : K → Type v} where
-- -- --  mutual
-- -- --   viewSing : (k₁ k₂ : K) ⦃ inBounds₁ : lb <⌊ k₁ ⌋ ⦄ ⦃ inBounds₂ : lb <⌊ k₂ ⌋ ⦄ →
-- -- --             (val : Val k₂) →
-- -- --             (xs : MapFrom ⌊ k₂ ⌋ Val) →
-- -- --             InstOrdering k₁ k₂ →
-- -- --             LensPart (MapFrom lb Val) (Maybe (Val k₁))
-- -- --   viewSing k₁ k₂ val xs lt′ .get = nothing
-- -- --   viewSing k₁ k₂ val xs lt′ .set nothing = k₂ ≔ val , xs
-- -- --   viewSing k₁ k₂ val xs lt′ .set (just x) = k₁ ≔ x , k₂ ≔ val , xs
-- -- --   viewSing k₁ k₂ val xs eq′ .get = just (subst Val (sym it) val)
-- -- --   viewSing k₁ k₂ val xs eq′ .set nothing = weaken xs
-- -- --   viewSing k₁ k₂ val xs eq′ .set (just x) = k₂ ≔ (subst Val it x) , xs
-- -- --   viewSing k₁ k₂ val xs gt′ = map-lens-part (view k₁ xs) (k₂ ≔ val ,_)

-- -- --   view : (k : K) → ⦃ inBounds : lb <⌊ k ⌋ ⦄ → MapFrom lb Val → LensPart (MapFrom lb Val) (Maybe (Val k))
-- -- --   view k₁ ∅ .get = nothing
-- -- --   view k₁ ∅ .set nothing = ∅
-- -- --   view k₁ ∅ .set (just x) = k₁ ≔ x , ∅
-- -- --   view k₁ (k₂ ≔ v , xs) = viewSing k₁ k₂ v xs (compare′ k₁ k₂)

-- -- -- open import Cubical.Foundations.Prelude using (substRefl)
-- -- -- open import Path.Reasoning


-- -- -- -- module _ {v} {Val : K → Type v} where
-- -- -- --   view-get-set : (k : K) (s : MapFrom lb Val) (v : Maybe (Val k)) → ⦃ _ : lb <⌊ k ⌋ ⦄ → view k (view k s .set v) .get ≡ v
-- -- -- --   view-get-set k₁ ∅ nothing = refl
-- -- -- --   view-get-set k₁ ∅ (just x) with compare k₁ k₁
-- -- -- --   view-get-set k₁ ∅ (just x) | lt p = ⊥-elim (irrefl p refl)
-- -- -- --   view-get-set k₁ ∅ (just x) | eq _ = cong just (cong (λ p → subst Val p x) (total⇒isSet  _ _ _ _) ; substRefl {B = Val} x)
-- -- -- --   view-get-set k₁ ∅ (just x) | gt p = ⊥-elim (irrefl p refl)

-- -- --   -- view-get-set k₁ (k₂ ≔ val , s) v with compare′ k₁ k₂ | inspect (compare′ k₁) k₂
-- -- --   -- view-get-set k₁ (k₂ ≔ val , s) nothing  | lt′ | 〖 q 〗 = cong (get ∘ viewSing k₁ k₂ val s) q
-- -- --   -- view-get-set k₁ (k₂ ≔ val , s) (just v) | lt′ | _ = {!!}
-- -- --   -- view-get-set k₁ (k₂ ≔ val , s) nothing  | eq′ | _ = {!!}
-- -- --   -- view-get-set k₁ (k₂ ≔ val , s) (just v) | eq′ | _ = {!!}
-- -- --   -- view-get-set k₁ (k₂ ≔ val , s) nothing  | gt′ | _ = {!!}
-- -- --   -- view-get-set k₁ (k₂ ≔ val , s) (just v) | gt′ | 〖 q 〗 =
-- -- --   --   viewSing k₁ k₂ val (set (view k₁ s) (just v)) (compare′ k₁ k₂) .get ≡⟨ cong (get ∘ viewSing k₁ k₂ val (set (view k₁ s) (just v))) q ⟩
-- -- --   --   viewSing k₁ k₂ val (set (view k₁ s) (just v)) gt′  .get ≡⟨ {!!} ⟩
-- -- --   --   just v ∎


