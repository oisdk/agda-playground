{-# OPTIONS --safe #-}

module Control.Monad.Free where

open import Prelude

data Free (F : Type a → Type a) (A : Type a) : Type (ℓsuc a) where
  lift : F A → Free F A

  return : A → Free F A
  _>>=_ : Free F B → (B → Free F A) → Free F A

  >>=-idˡ : (f : B → Free F A) (x : B) → (return x >>= f) ≡ f x
  >>=-idʳ : (x : Free F A) → (x >>= return) ≡ x
  >>=-assoc : (xs : Free F C) (f : C → Free F B) (g : B → Free F A) → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))

  trunc : isSet (Free F A)

open import Algebra

module _ {ℓ} (mon : Monad ℓ ℓ) where
  module F = Monad mon

  open F using (𝐹)

  module _ {G : Type ℓ → Type ℓ} (FisSet : ∀ {T} → isSet (𝐹 T)) (h : ∀ {T} → G T → 𝐹 T) where
    ⟦_⟧ : Free G A → 𝐹 A
    ⟦ lift x ⟧ = h x
    ⟦ return x ⟧ = F.return x
    ⟦ xs >>= k ⟧ = ⟦ xs ⟧ F.>>= λ x → ⟦ k x ⟧
    ⟦ >>=-idˡ f x i ⟧ = F.>>=-idˡ (⟦_⟧ ∘ f) x i
    ⟦ >>=-idʳ xs i ⟧ = F.>>=-idʳ ⟦ xs ⟧ i
    ⟦ >>=-assoc xs f g i ⟧ = F.>>=-assoc ⟦ xs ⟧ (⟦_⟧ ∘ f) (⟦_⟧ ∘ g) i

    ⟦ trunc xs ys p q i j ⟧ =
      isOfHLevel→isOfHLevelDep 2
        (λ xs → FisSet)
        ⟦ xs ⟧ ⟦ ys ⟧
        (cong ⟦_⟧ p) (cong ⟦_⟧ q)
        (trunc xs ys p q)
        i j

module _ {ℓ} (fun : Functor ℓ ℓ) where
  open Functor fun using (map; 𝐹)
  module _ {B : Type ℓ} (BIsSet : isSet B) where
    cata : (A → B) → (𝐹 B → B) → Free 𝐹 A → B
    cata h ϕ (lift x) = ϕ (map h x)
    cata h ϕ (return x) = h x
    cata h ϕ (xs >>= k) = cata (λ x → cata h ϕ (k x)) ϕ xs
    cata h ϕ (>>=-idˡ f x i) = cata h ϕ (f x)
    cata h ϕ (>>=-idʳ xs i) = cata h ϕ xs
    cata h ϕ (>>=-assoc xs f g i) = cata (λ x → cata (λ x₁ → cata h ϕ (g x₁)) ϕ (f x)) ϕ xs
    cata h ϕ (trunc xs ys p q i j) =
      isOfHLevel→isOfHLevelDep 2
        (λ xs → BIsSet)
        (cata h ϕ xs) (cata h ϕ ys)
        (cong (cata h ϕ) p) (cong (cata h ϕ) q)
        (trunc xs ys p q)
        i j
