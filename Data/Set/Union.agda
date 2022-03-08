module Data.Set.Union where

open import Data.Set.Definition
open import Data.Set.Eliminators
open import Prelude
open import Cubical.Foundations.Everything using (isSetΠ; isPropΠ)
open import Path.Reasoning

union-alg : ψ A (𝒦 A → 𝒦 A)
union-alg .fst ∅                  ys = ys
union-alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩)  ys = x ∷ P⟨xs⟩ ys
union-alg .snd .c-trunc _ = isSetΠ λ _ → trunc
union-alg .snd .c-com x y xs P⟨xs⟩ i ys = com x y (P⟨xs⟩ ys) i
union-alg .snd .c-dup x xs P⟨xs⟩ i ys = dup x (P⟨xs⟩ ys) i

infixr 5 _∪_
_∪_ : 𝒦 A → 𝒦 A → 𝒦 A
_∪_ = ⟦ union-alg ⟧

∷-distrib : ∀ (x : A) xs ys → x ∷ (xs ∪ ys) ≡ xs ∪ (x ∷ ys)
∷-distrib x = ⟦ alg x ⟧
  where
  alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys → x ∷ (xs ∪ ys) ≡ xs ∪ (x ∷ ys))
  alg x .fst ∅ ys = refl
  alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) ys = com x y (xs ∪ ys) ; cong (y ∷_) (P⟨xs⟩ ys)
  alg x .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _ 

∪-idem : (xs : 𝒦 A) → xs ∪ xs ≡ xs
∪-idem = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ ((xs ∪ xs) ≡ xs)
  alg .fst ∅ = refl
  alg .snd = eq-coh
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (x ∷ xs) ∪ (x ∷ xs) ≡˘⟨ ∷-distrib x (x ∷ xs) xs ⟩
    x ∷ x ∷ xs ∪ xs ≡⟨ dup x (xs ∪ xs) ⟩
    x ∷ xs ∪ xs ≡⟨ cong (x ∷_) P⟨xs⟩ ⟩
    x ∷ xs ∎

∪-idʳ : (xs : 𝒦 A) → (xs ∪ ∅ ≡ xs)
∪-idʳ = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (xs ∪ ∅ ≡ xs)
  alg .fst ∅ = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (x ∷_) P⟨xs⟩
  alg .snd = eq-coh

∪-com : (xs ys : 𝒦 A) → (xs ∪ ys ≡ ys ∪ xs)
∪-com = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys → xs ∪ ys ≡ ys ∪ xs)
  alg .fst ∅ ys = sym (∪-idʳ ys)
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) ys = cong (x ∷_) (P⟨xs⟩ ys) ; ∷-distrib x ys xs
  alg .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _

∪-assoc : (xs ys zs : 𝒦 A) → ((xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs))
∪-assoc = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys zs → (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs))
  alg .fst ∅ ys zs = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) ys zs = cong (x ∷_) (P⟨xs⟩ ys zs)
  alg .snd = prop-coh λ _ → isPropΠ λ _ → isPropΠ λ _ → trunc _ _


infixr 5 _∈_ _∉_
_∈_ : A → 𝒦 A → Type _
x ∈ xs = x ∷ xs ≡ xs

_∉_ : A → 𝒦 A → Type _
x ∉ xs = ¬ (x ∈ xs)


-- null : 𝒦 A → Bool
-- null = ⟦ alg ⟧
--   where
--   open import Data.Bool.Properties using (isSetBool)

--   alg : ψ A Bool
--   alg .fst ∅ = true
--   alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = false
--   alg .snd .c-trunc xs = isSetBool
--   alg .snd .c-com x y xs P⟨xs⟩ = refl
--   alg .snd .c-dup x xs P⟨xs⟩ = refl

-- open import Data.Bool.Properties

-- ∅≢∷ : ∀ (x : A) xs → x ∷ xs ≢ ∅
-- ∅≢∷ x xs = false≢true ∘′ cong null

-- x∉∅ : ∀ (x : A) → x ∉ ∅
-- x∉∅ x = ∅≢∷ x ∅

-- ∈-∷ : ∀ (x y : A) xs → x ∈ xs → x ∈ y ∷ xs
-- ∈-∷ x y xs p = com x y xs ; cong (y ∷_) p

-- open import Relation.Nullary.Discrete
-- open import Relation.Nullary.Decidable
-- open import Relation.Nullary.Decidable.Properties

-- open import HLevels
-- open import Cubical.HITs.PropositionalTruncation

-- open import Cubical.Foundations.HLevels

-- open import Cubical.Foundations.Everything using (isPropΣ)
-- open import Cubical.Data.Sigma using (ΣPathP)

-- open import Data.Set.Syntax

-- -- Single : 𝒦 A → Type _
-- -- Single {A = A} xs = Σ[ x ⦂ A ] × (xs ≡ ⟅ x ⟆)

-- -- ¬Sing[] : ¬ Single {A = A} ∅
-- -- ¬Sing[] = true≢false ∘ cong null ∘ snd

-- -- -- _∈′_ : {A : Type a} → A → 𝒦 A → Type a
-- -- -- _∈′_ x = fst ∘ ⟦ alg x ⟧
-- -- --   where
-- -- --   import Data.Empty.UniversePolymorphic as Poly
-- -- --   open import Cubical.Data.Sigma

-- -- --   alg : {A : Type a} (x : A) → Ψ[ xs ⦂ 𝒦 A ] ↦ hProp a
-- -- --   alg x .fst ∅ = Poly.⊥ , λ ()
-- -- --   alg x .fst (y ∷ xs ⟨ x∈xs ⟩) = ∥ (x ≡ y) ⊎ fst x∈xs ∥ , squash
-- -- --   alg x .snd .c-trunc _ = isSetHProp
-- -- --   alg x .snd .c-com y z xs (x∈xs , _) = Σ≡Prop (λ _ → isPropIsProp) {!!}
-- -- --   alg x .snd .c-dup y xs (x∈xs , _) = Σ≡Prop (λ _ → isPropIsProp) {!!}


-- -- -- from-trunc : ∀ (x : A) xs → x ∈′ xs → x ∈ xs
-- -- -- from-trunc x = ⟦ alg x ⟧
-- -- --   where
-- -- --   alg : (x : A) → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈′ xs → x ∈ xs)
-- -- --   alg x .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _
-- -- --   alg x .fst (y ∷ xs ⟨ x∈xs ⟩) = rec (trunc _ _) (either (λ x≡y → cong (_∷ y ∷ xs) x≡y ; dup y xs) (∈-∷ x y xs ∘ x∈xs))


-- -- open import Data.Nat

-- -- module _ {A : Type a} (_≟_ : Discrete A) where
-- --   -- to-trunc : ∀ (x : A) xs → x ∈ xs → x ∈′ xs
-- --   -- to-trunc x = ⟦ alg x ⟧
-- --   --   where
-- --   --   alg : (x : A) → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → x ∈′ xs)
-- --   --   alg x .snd = prop-coh λ _ → isPropΠ {!λ _ → squash _ _!}
-- --   --   alg x .fst ∅ x∈∅ = ⊥-elim (x∉∅ x x∈∅)
-- --   --   alg x .fst (y ∷ xs ⟨ x∈xs ⟩) x∈y∷xs with x ≟ y
-- --   --   alg x .fst (y ∷ xs ⟨ x∈xs ⟩) x∈y∷xs | yes x≡y = ∣ inl x≡y ∣
-- --   --   alg x .fst (y ∷ xs ⟨ x∈xs ⟩) x∈y∷xs | no  x≢y = ∣ inr (x∈xs {!!}) ∣

-- --   _∈ᴮ_ : A → 𝒦 A → Bool
-- --   x ∈ᴮ xs = ⟦ alg x ⟧ xs
-- --     where
-- --     alg : A → ψ A Bool
-- --     alg x .fst ∅ = false
-- --     alg x .fst (y ∷ _ ⟨ r ⟩) = does (x ≟ y) or r
-- --     alg x .snd .c-trunc _ = isSetBool
-- --     alg x .snd .c-com y z _ _ with does (x ≟ y) | does (x ≟ z)
-- --     ... | true  | true  = refl
-- --     ... | true  | false = refl
-- --     ... | false | true  = refl
-- --     ... | false | false = refl
-- --     alg x .snd .c-dup y _ _ with does (x ≟ y)
-- --     ... | true  = refl
-- --     ... | false = refl

-- --   ∈-yes : ∀ (x : A) xs → T (x ∈ᴮ xs) → x ∈ xs
-- --   ∈-yes x = ⟦ alg x ⟧
-- --     where
-- --     alg : (x : A) → Ψ[ xs ⦂ 𝒦 A ] ↦ (T (x ∈ᴮ xs) → x ∈ xs)
-- --     alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) p with x ≟ y
-- --     ... | yes x≡y = cong (_∷ y ∷ xs) x≡y ; dup y xs
-- --     ... | no  _   = com x y xs ; cong (y ∷_) (P⟨xs⟩ p)
-- --     alg x .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _

-- --   -- step : ∀ (x y : A) xs → x ∈ y ∷ xs → x ≢ y → x ∈ xs
-- --   -- step x y xs p x≢y = {!!}
  
-- --   -- ∈-no : ∀ (x : A) xs → T (not (x ∈ᴮ xs)) → ¬ (x ∈ xs)
-- --   -- ∈-no x = ⟦ alg x ⟧
-- --   --   where
-- --   --   alg : (x : A) → Ψ[ xs ⦂ 𝒦 A ] ↦ (T (not (x ∈ᴮ xs)) → ¬ (x ∈ xs))
-- --   --   alg x .snd = prop-coh λ _ → isPropΠ λ _ → isPropΠ λ _ → λ ()
-- --   --   alg x .fst ∅ p = x∉∅ x
-- --   --   alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) p x∈y∷xs with x ≟ y
-- --   --   alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) p x∈y∷xs | yes x≡y = p
-- --   --   alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) p x∈y∷xs | no  x≢y = P⟨xs⟩ p (step x y xs x∈y∷xs x≢y)
