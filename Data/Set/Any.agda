open import Prelude hiding (⊥)

module Data.Set.Any {a} {A : Type a} {p} (P : A → Type p) where

open import Data.Set.Definition
open import Data.Set.Eliminators
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Properties
open import Data.Sigma.Properties
open import HITs.PropositionalTruncation.Sugar
open import Data.Set.Pred

open import Data.Empty.UniversePolymorphic {p}

◇-alg-compute : Alg {A = A} λ _ → hProp p
◇-alg-compute ∅                     = ⊥ , λ ()
◇-alg-compute (x ∷ xs ⟨ x◇xs , _ ⟩) = ∥ (P x) ⊎ x◇xs ∥ , squash

◇-alg : ψ A (hProp p)
◇-alg .fst = ◇-alg-compute
◇-alg .snd .c-trunc _ = isSetHProp
◇-alg .snd .c-com y z xs (x◇xs , _) = Σ≡Prop (λ _ → isPropIsProp) (isoToPath (memb-com (P y) (P z) x◇xs))
◇-alg .snd .c-dup y   xs (x◇xs , _) = Σ≡Prop (λ _ → isPropIsProp) (isoToPath (memb-dup (P y) x◇xs))


infixr 5 _◇_
_◇_ : 𝒦 A → Type p
_◇_ = fst ∘ ⟦ ◇-alg ⟧

◇-isProp : ∀ xs → isProp (_◇_ xs)
◇-isProp = snd ∘ ⟦ ◇-alg ⟧

open import Cubical.Foundations.Everything using (isPropΠ)


open import Data.Set.Union


◇-∪-alg : ∀ ys → Ψ[ xs ⦂ 𝒦 A ] ↦ (_◇_ xs → _◇_ (xs ∪ ys))
◇-∪-alg ys .fst (_ ∷ _ ⟨ k ⟩) ◇xs = mapʳ k ∥$∥ ◇xs
◇-∪-alg ys .snd = prop-coh λ xs → isPropΠ λ _ → ◇-isProp (xs ∪ ys)

◇-∪ : ∀ xs ys → _◇_ xs → _◇_ (xs ∪ ys)
◇-∪ xs ys = ⟦ ◇-∪-alg ys ⟧ xs

¬◇-tail : ∀ x xs → (¬ (_◇_ (x ∷ xs)) → ¬ (_◇_ xs))
¬◇-tail x xs ¬◇x∷xs ◇xs = ¬◇x∷xs ∣ inr ◇xs ∣

◇⁻-∪-alg : ∀ ys → Ψ[ xs ⦂ 𝒦 A ] ↦ (¬ (_◇_ xs) → _◇_ (xs ∪ ys) → _◇_ ys) 
◇⁻-∪-alg ys .fst ∅ ¬◇xs = id
◇⁻-∪-alg ys .fst (x ∷ xs ⟨ k ⟩) ¬◇xs = rec (◇-isProp ys) (either (⊥-elim ∘ ¬◇xs ∘ ∣_∣ ∘ inl) (k (¬◇-tail x xs ¬◇xs)))
◇⁻-∪-alg ys .snd = prop-coh λ _ → isPropΠ λ _ → isPropΠ λ _ → ◇-isProp ys 

◇⁻-∪ : ∀ xs ys → ¬ (_◇_ xs) → _◇_ (xs ∪ ys) → _◇_ ys
◇⁻-∪ xs ys = ⟦ ◇⁻-∪-alg ys ⟧ xs

◇⁻-∪ˡ : ∀ xs ys → ¬ (_◇_ xs) → _◇_ (ys ∪ xs) → _◇_ ys
◇⁻-∪ˡ xs ys ¬p p = ◇⁻-∪ xs ys ¬p (subst _◇_ (∪-com ys xs) p)

module _ (P? : ∀ x → Dec (P x)) where

  open import Relation.Nullary.Decidable.Logic
  open import Relation.Nullary.Decidable.Properties

  ◇?-alg : Ψ[ xs ⦂ 𝒦 A ] ↦ Dec (_◇_ xs)
  ◇?-alg .fst ∅ = no λ ()
  ◇?-alg .fst (x ∷ xs ⟨ x◇?xs ⟩) = disj (∣_∣ ∘ inl) (∣_∣ ∘ inr) (λ x≢y x∉xs → rec (λ ()) (either x≢y x∉xs)) (P? x) x◇?xs
  ◇?-alg .snd = prop-coh λ xs → isPropDec (◇-isProp xs)

  ◇? : ∀ xs → Dec (_◇_ xs)
  ◇? = ⟦ ◇?-alg ⟧

  remove-alg : ψ A (𝒦 A)
  remove-alg .fst ∅ = ∅
  remove-alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = if does (P? x) then P⟨xs⟩ else x ∷ P⟨xs⟩
  remove-alg .snd .c-trunc _ = trunc
  remove-alg .snd .c-com x y xs P⟨xs⟩ with does (P? x) | does (P? y)
  remove-alg .snd .c-com x y xs P⟨xs⟩ | false | false = com x y P⟨xs⟩
  remove-alg .snd .c-com x y xs P⟨xs⟩ | false | true  = refl
  remove-alg .snd .c-com x y xs P⟨xs⟩ | true  | false = refl
  remove-alg .snd .c-com x y xs P⟨xs⟩ | true  | true  = refl
  remove-alg .snd .c-dup x xs P⟨xs⟩ with does (P? x)
  remove-alg .snd .c-dup x xs P⟨xs⟩ | false = dup x P⟨xs⟩
  remove-alg .snd .c-dup x xs P⟨xs⟩ | true  = refl

  remove : 𝒦 A → 𝒦 A
  remove = ⟦ remove-alg ⟧

  ¬◇-remove-alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (¬ (_◇_ (remove xs)))
  ¬◇-remove-alg .fst (x ∷ xs ⟨ ¬◇xs ⟩) ◇xs with P? x
  ... | yes Px = ¬◇xs ◇xs
  ... | no ¬Px = rec (λ ()) (either ¬Px ¬◇xs) ◇xs
  ¬◇-remove-alg .snd = prop-coh λ _ → isPropΠ λ _ ()

  ¬◇-remove : ∀ xs → ¬ (_◇_ (remove xs))
  ¬◇-remove = ⟦ ¬◇-remove-alg ⟧
