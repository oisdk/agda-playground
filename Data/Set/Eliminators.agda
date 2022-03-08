module Data.Set.Eliminators where

open import Prelude
open import Data.Set.Definition
open import HLevels

data 𝔎 {p} (A : Type a) (P : 𝒦 A → Type p) : Type (a ℓ⊔ p) where
  ∅ : 𝔎 A P
  _∷_⟨_⟩ : A → (xs : 𝒦 A) → (P⟨xs⟩ : P xs) → 𝔎 A P

private
  variable
    p : Level
    P : 𝒦 A → Type p

embed : 𝔎 A P → 𝒦 A
embed ∅ = ∅
embed (x ∷ xs ⟨ P⟨xs⟩ ⟩) = x ∷ xs

Alg : (P : 𝒦 A → Type p) → Type _
Alg P = (xs : 𝔎 _ P) → P (embed xs)

record Coherent {A : Type a} {P : 𝒦 A → Type p} (ϕ : Alg P) : Type (a ℓ⊔ p) where
  field
    c-trunc : ∀ xs → isSet (P xs)

    c-com : ∀ x y xs P⟨xs⟩ →
            ϕ (x ∷ (y ∷ xs) ⟨ ϕ (y ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩)
               ≡[ i ≔ P (com x y xs i) ]≡
            ϕ (y ∷ (x ∷ xs) ⟨ ϕ (x ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩ )

    c-dup : ∀ x xs P⟨xs⟩ →
            ϕ (x ∷ (x ∷ xs) ⟨ ϕ (x ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩)
               ≡[ i ≔ P (dup x xs i) ]≡
            ϕ (x ∷ xs ⟨ P⟨xs⟩ ⟩)
open Coherent public

𝒦-foldr : (A → B → B) → B → Alg (const B)
𝒦-foldr f b ∅ = b
𝒦-foldr f b (x ∷ xs ⟨ P⟨xs⟩ ⟩) = f x P⟨xs⟩

Ψ : (𝒦 A → Type p) → Type _
Ψ P = Σ[ ϕ ⦂ Alg P ] × Coherent ϕ

Ψ-syntax : (A : Type a) → (𝒦 A → Type p) → Type _
Ψ-syntax _ = Ψ

syntax Ψ-syntax A (λ x → e) = Ψ[ x ⦂ 𝒦 A ] ↦ e

ψ : Type a → Type b → Type _
ψ A B = Ψ {A = A} (const B)

⟦_⟧ : {P : 𝒦 A → Type p} → Ψ P → (xs : 𝒦 A) → P xs
⟦ alg ⟧ ∅ = alg .fst ∅
⟦ alg ⟧ (x ∷ xs) = alg .fst (x ∷ xs ⟨ ⟦ alg ⟧ xs ⟩)
⟦ alg ⟧ (com x y xs i) = alg .snd .c-com x y xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (dup x xs i) = alg .snd .c-dup x xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (trunc xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-trunc)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc xs ys p q)
    i j

prop-coh : {A : Type a} {P : 𝒦 A → Type p} {alg : Alg P} → (∀ xs → isProp (P xs)) → Coherent alg
prop-coh P-isProp .c-trunc xs = isProp→isSet (P-isProp xs)
prop-coh {P = P} {alg = alg} P-isProp .c-dup x xs ψ⟨xs⟩ =
 toPathP (P-isProp (x ∷ xs) (transp (λ i → P (dup x xs i)) i0 (alg (x ∷ (x ∷ xs) ⟨ alg (x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg (x ∷ xs ⟨ ψ⟨xs⟩ ⟩)))
prop-coh {P = P} {alg = alg} P-isProp .c-com x y xs ψ⟨xs⟩ =
  toPathP (P-isProp (y ∷ x ∷ xs) (transp (λ i → P (com x y xs i)) i0 (alg (x ∷ (y ∷ xs) ⟨ alg (y ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg (y ∷ (x ∷ xs) ⟨ alg (x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩)))

infix 4 _⊜_
record AnEquality (A : Type a) : Type a where
  constructor _⊜_
  field lhs rhs : 𝒦 A
open AnEquality public

EqualityProof-Alg : {B : Type b} (A : Type a) (P : 𝒦 A → AnEquality B) → Type (a ℓ⊔ b)
EqualityProof-Alg A P = Alg (λ xs → let Pxs = P xs in lhs Pxs ≡ rhs Pxs)

eq-coh : {A : Type a} {B : Type b} {P : 𝒦 A → AnEquality B} {alg : EqualityProof-Alg A P} → Coherent alg
eq-coh {P = P} = prop-coh λ xs → let Pxs = P xs in trunc (lhs Pxs) (rhs Pxs)
