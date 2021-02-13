{-# OPTIONS --cubical --safe #-}

module Control.Monad.Levels.Zipping where

open import Prelude
open import Control.Monad.Levels.Definition
open import Control.Monad.Levels.Eliminators
open import Data.Bag
open import Path.Reasoning

open import Cubical.Foundations.HLevels using (isOfHLevelΠ)

zip₂-alg : Levels-ϕ[ A ](⟅ A ⟆ → (Levels A → Levels A) → Levels A)
[ zip₂-alg ]-set = isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → trunc
[ zip₂-alg ] y ∷ ys ⟨ _ ⟩ x xs = (x ∪ y) ∷ xs ys
[ zip₂-alg ][] x xs = x ∷ xs []
[ zip₂-alg ]-trail i x xs = ∪-idʳ x i ∷ xs []

zip₂-alg-id : Levels-ψ[ xs ⦂ A ]≡ ((zip₂-alg ↓ xs) [] id ⊜ xs)
⟦ zip₂-alg-id ⟧≡ x ∷ xs ⟨ Pxs ⟩ = refl
⟦ zip₂-alg-id ⟧≡[] = trail

zip-alg : Levels-ϕ[ A ] (Levels A → Levels A)
[ zip-alg ]-set = isOfHLevelΠ 2 λ _ → trunc
[ zip-alg ] x ∷ _ ⟨ k ⟩ ys = (zip₂-alg ↓ ys) x k
[ zip-alg ][] ys = ys
[ zip-alg ]-trail = funExt (zip₂-alg-id ⇓≡_)

zip : Levels A → Levels A → Levels A
zip xs = zip-alg ↓ xs

zip-idʳ : Levels-ψ[ xs ⦂ A ]≡ zip xs [] ⊜ xs
⟦ zip-idʳ ⟧≡ x ∷ xs ⟨ Pxs ⟩ = cong (x ∷_) Pxs
⟦ zip-idʳ ⟧≡[] = refl

mutual
  zip₂-comm : (x : ⟅ A ⟆) (xs : Levels A) (pxs : ∀ ys → zip xs ys ≡ zip ys xs) → Levels-ψ[ ys ⦂ A ]≡  (zip (x ∷ xs) ys ⊜ zip ys (x ∷ xs))
  ⟦ zip₂-comm x xs pxs ⟧≡[] = zip-idʳ ⇓≡ (x ∷ xs)
  ⟦ zip₂-comm x xs pxs ⟧≡ y ∷ ys ⟨ Pys ⟩ = cong₂ _∷_ (∪-comm x y) (pxs ys)

  zip-comm : Levels-ψ[ xs ⦂ A ] (∀ ys → zip xs ys ≡ zip ys xs)
  ∥ zip-comm ∥-prop = isOfHLevelΠ 1 λ _ → trunc _ _
  ∥ zip-comm ∥[] ys = sym (zip-idʳ ⇓≡ ys)
  ∥ zip-comm ∥ x ∷ xs ⟨ Pxs ⟩ ys = zip₂-comm x xs Pxs ⇓≡ ys


zip₃-assoc : (x : ⟅ A ⟆) (xs : Levels A) (pxs : ∀ ys zs → zip (zip xs ys) zs ≡ zip xs (zip ys zs)) →
             (y : ⟅ A ⟆) (ys : Levels A) →
             Levels-ψ[ zs ⦂ A ]≡ (zip (zip (x ∷ xs) (y ∷ ys)) zs ⊜ zip (x ∷ xs) (zip (y ∷ ys) zs))
⟦ zip₃-assoc x xs pxs y ys ⟧≡[] = (zip-idʳ ⇓≡ (zip (x ∷ xs) (y ∷ ys))) ; cong (zip (x ∷ xs)) (sym (zip-idʳ ⇓≡ (y ∷ ys)))
⟦ zip₃-assoc x xs pxs y ys ⟧≡ z ∷ zs ⟨ _ ⟩ = cong₂ _∷_ (∪-assoc x y z) (pxs ys zs)

zip₂-assoc : (x : ⟅ A ⟆) (xs : Levels A) (pxs : ∀ ys zs → zip (zip xs ys) zs ≡ zip xs (zip ys zs)) →
             Levels-ψ[ ys ⦂ A ] (∀ zs → zip (zip (x ∷ xs) ys) zs ≡ zip (x ∷ xs) (zip ys zs))
∥ zip₂-assoc x xs pxs ∥-prop = isOfHLevelΠ 1 λ _ → trunc _ _
∥ zip₂-assoc x xs pxs ∥[] zs = cong (λ xs → zip xs zs) (zip-idʳ ⇓≡ (x ∷ xs))
∥ zip₂-assoc x xs pxs ∥ y ∷ ys ⟨ _ ⟩ zs = zip₃-assoc x xs pxs y ys ⇓≡ zs

zip-assoc : Levels-ψ[ xs ⦂ A ] (∀ ys zs → zip (zip xs ys) zs ≡ zip xs (zip ys zs))
∥ zip-assoc ∥-prop = isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → trunc _ _
∥ zip-assoc ∥ x ∷ xs ⟨ Pxs ⟩ ys zs = ∥ zip₂-assoc x xs Pxs ∥⇓ ys zs
∥ zip-assoc ∥[] _ _ = refl

open import Algebra

module _ {a} {A : Type a} where
  levels-cmon : CommutativeMonoid a
  Monoid.𝑆 (CommutativeMonoid.monoid levels-cmon) = Levels A
  Monoid._∙_ (CommutativeMonoid.monoid levels-cmon) = zip
  Monoid.ε (CommutativeMonoid.monoid levels-cmon) = []
  Monoid.assoc (CommutativeMonoid.monoid levels-cmon) = ∥ zip-assoc ∥⇓
  Monoid.ε∙ (CommutativeMonoid.monoid levels-cmon) _ = refl
  Monoid.∙ε (CommutativeMonoid.monoid levels-cmon) xs = zip-idʳ ⇓≡ xs
  CommutativeMonoid.comm levels-cmon = ∥ zip-comm ∥⇓
