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

reverse : List A → List A
reverse = foldl (flip _∷_) []

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

-- uncons : Q A → Maybe (A × Q A)
-- uncons (x ∷ xs +- ys) = just (x , xs +- ys)
-- uncons ([] +- []) = nothing
-- uncons ([] +- y ∷ ys) = let z , zs = rev1 y ys in just (z , zs +- [])
-- uncons (quot x (y ∷ xs) ys i) = just (y , quot x xs ys i)
-- uncons (quot x [] [] i) = just (x , [] +- [])
-- uncons (quot x [] (y ∷ ys) i) = {!!}
