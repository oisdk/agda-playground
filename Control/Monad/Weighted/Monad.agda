{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Weighted.Monad {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import HLevels
open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Union rng
open import Control.Monad.Weighted.Cond rng

bind-alg : (A → W B) → W-ϕ[ A ] W B
[ bind-alg f ] p & x ∷ _ ⟨ xs ⟩ = (p ⋊ f x) <|> xs
[ bind-alg f ][] = []
[ bind-alg f ]-set = trunc
[ bind-alg f ]-del x _ xs = cong (_<|> xs) (0⋊ (f x))
[ bind-alg f ]-dup p q x _ xs =
  p ⋊ f x <|> (q ⋊ f x <|> xs) ≡⟨ <|>-assoc (p ⋊ f x) (q ⋊ f x) xs ⟩
  (p ⋊ f x <|> q ⋊ f x) <|> xs ≡⟨ cong (_<|> xs) (⋊-distribʳ p q (f x)) ⟩
  (p + q ⋊ f x) <|> xs ∎
[ bind-alg f ]-com p x q y _ xs =
  p ⋊ f x <|> q ⋊ f y <|> xs   ≡⟨ <|>-assoc (p ⋊ f x) (q ⋊ f y) xs ⟩
  (p ⋊ f x <|> q ⋊ f y) <|> xs ≡⟨ cong (_<|> xs) (<|>-com (p ⋊ f x) (q ⋊ f y)) ⟩
  (q ⋊ f y <|> p ⋊ f x) <|> xs ≡˘⟨ <|>-assoc (q ⋊ f y) (p ⋊ f x) xs ⟩
  q ⋊ f y <|> p ⋊ f x <|> xs ∎

_>>=_ : W A → (A → W B) → W B
xs >>= f = bind-alg f ↓ xs

pure : A → W A
pure x = 1# & x ∷ []

_>>_ : W A → W B → W B
xs >> ys = do
  _ ← xs
  ys

_<*>_ : W (A → B) → W A → W B
fs <*> xs = do
  f ← fs
  x ← xs
  pure (f x)

>>=-distrib : (xs ys : W A) (g : A → W B) → (xs <|> ys) >>= g ≡ (xs >>= g) <|> (ys >>= g)
>>=-distrib xs ys g = >>=-distrib′ ys g ⇓≡ xs
  where
  >>=-distrib′ : (ys : W A) (g : A → W B) → W-ψ[ xs ⦂ A ]≡ ((xs <|> ys) >>= g) ⊜ (xs >>= g) <|> (ys >>= g)
  ⟦ >>=-distrib′ ys g ⟧≡[] = refl
  ⟦ >>=-distrib′ ys g ⟧≡ p & x ∷ xs ⟨ P ⟩ =
    (((p & x ∷ xs) <|> ys) >>= g) ≡⟨⟩
    (p & x ∷ xs <|> ys) >>= g ≡⟨⟩
    p ⋊ g x <|> ((xs <|> ys) >>= g) ≡⟨ cong (p ⋊ g x <|>_) P ⟩
    p ⋊ g x <|> ((xs >>= g) <|> (ys >>= g)) ≡⟨ <|>-assoc (p ⋊ g x) (xs >>= g) (ys >>= g) ⟩
    (p ⋊ g x <|> (xs >>= g)) <|> (ys >>= g) ≡⟨⟩
    ((p & x ∷ xs) >>= g) <|> (ys >>= g) ∎

⋊-assoc->>= : ∀ p (xs : W A) (f : A → W B) → (p ⋊ xs) >>= f ≡ p ⋊ (xs >>= f)
⋊-assoc->>= p xs f = ⋊-assoc->>=′ p f ⇓≡ xs
  where
  ⋊-assoc->>=′ : ∀ p (f : A → W B) → W-ψ[ xs ⦂ A ]≡ (p ⋊ xs) >>= f ⊜ p ⋊ (xs >>= f)
  ⟦ ⋊-assoc->>=′ p f ⟧≡[] = refl
  ⟦ ⋊-assoc->>=′ p f ⟧≡ q & x ∷ xs ⟨ P ⟩ =
    (p ⋊ (q & x ∷ xs)) >>= f ≡⟨⟩
    (p * q & x ∷ p ⋊ xs) >>= f ≡⟨⟩
    ((p * q) ⋊ f x) <|> ((p ⋊ xs) >>= f) ≡⟨ cong (((p * q) ⋊ f x) <|>_) P ⟩
    ((p * q) ⋊ f x) <|> (p ⋊ (xs >>= f)) ≡⟨ cong (_<|> (p ⋊ (xs >>= f))) (*-assoc-⋊ p q (f x)) ⟩
    (p ⋊ (q ⋊ f x)) <|> (p ⋊ (xs >>= f)) ≡⟨ ⋊-distribˡ p (q ⋊ f x) (xs >>= f) ⟩
    p ⋊ ((q & x ∷ xs) >>= f) ∎

>>=-idˡ : (x : A) → (f : A → W B)
      → (pure x >>= f) ≡ f x
>>=-idˡ x f =
  pure x >>= f ≡⟨⟩
  (1# & x ∷ []) >>= f ≡⟨⟩
  1# ⋊ f x <|> [] >>= f ≡⟨⟩
  1# ⋊ f x <|> [] ≡⟨ <|>-idr (1# ⋊ f x) ⟩
  1# ⋊ f x ≡⟨ 1⋊ (f x) ⟩
  f x ∎

>>=-idʳ : (xs : W A) → xs >>= pure ≡ xs
>>=-idʳ = >>=-idʳ′ ⇓≡_
  where
  >>=-idʳ′ : W-ψ[ xs ⦂ A ]≡ xs >>= pure ⊜ xs
  ⟦ >>=-idʳ′ ⟧≡[] = refl
  ⟦ >>=-idʳ′ ⟧≡ p & x ∷ xs ⟨ P ⟩ =
    ((p & x ∷ xs) >>= pure) ≡⟨⟩
    p ⋊ (pure x) <|> (xs >>= pure) ≡⟨⟩
    p ⋊ (1# & x ∷ []) <|> (xs >>= pure) ≡⟨⟩
    p * 1# & x ∷ [] <|> (xs >>= pure) ≡⟨⟩
    p * 1# & x ∷ (xs >>= pure) ≡⟨ cong (_& x ∷ (xs >>= pure)) (*1 p) ⟩
    p & x ∷ xs >>= pure ≡⟨ cong (p & x ∷_) P ⟩
    p & x ∷ xs ∎

>>=-assoc : (xs : W A) → (f : A → W B) → (g : B → W C)
      → ((xs >>= f) >>= g) ≡ xs >>= (λ x → f x >>= g)
>>=-assoc xs f g = >>=-assoc′ f g ⇓≡ xs
  where
  >>=-assoc′ : (f : A → W B) → (g : B → W C) → W-ψ[ xs ⦂ A ]≡ ((xs >>= f) >>= g) ⊜ xs >>= (λ x → f x >>= g)
  ⟦ >>=-assoc′ f g ⟧≡[] = refl
  ⟦ >>=-assoc′ f g ⟧≡ p & x ∷ xs ⟨ P ⟩ =
    (((p & x ∷ xs) >>= f) >>= g) ≡⟨⟩
    ((p ⋊ f x <|> (xs >>= f)) >>= g) ≡⟨ >>=-distrib (p ⋊ f x) (xs >>= f) g ⟩
    ((p ⋊ f x) >>= g) <|> ((xs >>= f) >>= g) ≡⟨ cong ((p ⋊ f x) >>= g <|>_) P ⟩
    ((p ⋊ f x) >>= g) <|> (xs >>= (λ y → f y >>= g)) ≡⟨ cong (_<|> (xs >>= (λ y → f y >>= g))) (⋊-assoc->>= p (f x) g) ⟩
    p ⋊ (f x >>= g) <|> (xs >>= (λ y → f y >>= g)) ≡⟨⟩
    ((p & x ∷ xs) >>= (λ y → f y >>= g)) ∎


  
