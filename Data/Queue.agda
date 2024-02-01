module Data.Queue where

open import Prelude
open import Data.List
open import Data.List.Properties
open import Path.Reasoning

infixl 5 _∷′_
_∷′_ : List A → A → List A
xs ∷′ x = xs ++ x ∷ []

infix 4.5 _+-_
data Q (A : Type a) : Type a where
  _+-_ : List A → List A → Q A
  quot : ∀ x xs ys → xs +- ys ∷′ x ≡ xs ∷′ x +- ys

snoc-fold : ∀ (xs ys : List A) → foldl (flip _∷_) ys xs ≡ foldr (flip _∷′_) [] xs ++ ys
snoc-fold []       ys = refl
snoc-fold (x ∷ xs) ys = snoc-fold xs (x ∷ ys) ; sym (++-assoc (foldr (flip _∷′_) [] xs) (x ∷ []) ys)

reverse-∷′ : ∀ (xs : List A) → reverse xs ≡ foldr (flip _∷′_) [] xs
reverse-∷′ xs = snoc-fold xs [] ; ++-idʳ _ 

reverse-++ : (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ xs ys =
  reverse (xs ++ ys) ≡⟨⟩
  reverse (foldr _∷_ ys xs) ≡⟨ reverse-∷′ (xs ++ ys) ⟩
  foldr (flip _∷′_) [] (foldr _∷_ ys xs) ≡⟨ foldr-fusion (foldr (flip _∷′_) []) ys (λ _ _ → refl) xs ⟩
  foldr (flip _∷′_) (foldr (flip _∷′_) [] ys) xs ≡˘⟨ cong (flip (foldr (flip _∷′_)) xs) (reverse-∷′ ys) ⟩
  foldr (flip _∷′_) (reverse ys) xs ≡˘⟨ cong (flip (foldr (flip _∷′_)) xs) (++-idʳ (reverse ys)) ⟩
  foldr (flip _∷′_) (reverse ys ++ []) xs ≡˘⟨ foldr-fusion (reverse ys ++_) [] (λ z zs → sym (++-assoc (reverse ys) zs (z ∷ []))) xs ⟩
  reverse ys ++ foldr (flip _∷′_) [] xs ≡˘⟨ cong (reverse ys ++_) (reverse-∷′ xs) ⟩
  reverse ys ++ reverse xs ∎

reverse-comm-++ : ∀ (x : A) xs ys → xs ++ reverse (ys ∷′ x) ≡ (xs ∷′ x) ++ reverse ys
reverse-comm-++ x xs ys =
  xs ++ reverse (ys ∷′ x) ≡⟨ cong (xs ++_) (reverse-++ ys (x ∷ [])) ⟩
  xs ++ x ∷ reverse ys ≡˘⟨ ++-assoc xs (x ∷ []) (reverse ys) ⟩
  (xs ∷′ x) ++ reverse ys ∎

toList : Q A → List A
toList (xs +- ys) = xs ++ reverse ys
toList (quot x xs ys i) = reverse-comm-++ x xs ys i

cons : A → Q A → Q A
cons x (ys +- zs) = x ∷ ys +- zs
cons x (quot y xs ys i) = quot y (x ∷ xs) ys i

snoc : Q A → A → Q A
snoc (ys +- zs) x = ys +- x ∷ zs
snoc (quot y xs ys i) x = quot y xs (x ∷ ys) i

rev1 : A → List A → A × List A
rev1 x xs = foldl f (x , []) xs
  where
  f : A × List A → A → A × List A
  f (x , xs) y = y , x ∷ xs

qid : Q A → Q A
qid xs = toList xs +- []

qid-is-id′ : (xs ys : List A) → (xs ++ reverse ys) +- [] ≡ xs +- ys
qid-is-id′ xs []       = cong (_+- []) (++-idʳ _)
qid-is-id′ xs (y ∷ ys) =
  xs ++ reverse (y ∷ ys) +- [] ≡⟨ cong (λ e → xs ++ e +- []) (reverse-++ (y ∷ []) ys) ⟩
  xs ++ (reverse ys ∷′ y) +- [] ≡˘⟨ cong (_+- []) (++-assoc xs (reverse ys) _) ⟩
  (xs ++ reverse ys) ∷′ y +- [] ≡˘⟨ quot y (xs ++ reverse ys) [] ⟩
  xs ++ reverse ys +- y ∷ [] ≡⟨ cong (flip snoc y) (qid-is-id′ xs ys) ⟩
  xs +- y ∷ ys ∎

-- qid-is-id : (xs : Q A) → qid xs ≡ xs
-- qid-is-id (xs +- ys) = qid-is-id′ xs ys
-- qid-is-id (quot x xs ys i) j = {!!}

-- toList-inj : (xs ys : Q A) → toList xs ≡ toList ys → xs ≡ ys
-- toList-inj xs ys p = sym (qid-is-id xs) ; cong (_+- []) p ; qid-is-id ys
