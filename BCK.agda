{-# OPTIONS --cubical --safe #-}

module BCK where

open import Prelude hiding (B; C)

infixl 4 _$$_
data BCK : Type where
  _$$_ : BCK → BCK → BCK
  B C K : BCK

open import Data.List

stack⊙ : BCK → List BCK → Maybe BCK
stack⊙ (f $$ x) xs = stack⊙ f (x ∷ xs)
stack⊙ B (f ∷ g ∷ x ∷ xs) = just (foldl _$$_ (f $$ (g $$ x)) xs)
stack⊙ C (f ∷ x ∷ y ∷ xs) = just (foldl _$$_ (f $$ y $$ x) xs)
stack⊙ K (x ∷ y ∷ xs) = just (foldl _$$_ x xs)
stack⊙ _ _ = nothing

stack : BCK → Maybe BCK
stack xs = stack⊙ xs []

size⊙ : BCK → ℕ → ℕ
size⊙ (xs $$ ys) = size⊙ xs ∘ size⊙ ys
size⊙ B = suc
size⊙ C = suc
size⊙ K = suc

size : BCK → ℕ
size xs = size⊙ xs zero

open import Data.Nat.Properties

_M<ᴮ_ : Maybe ℕ → ℕ → Bool
n M<ᴮ m = maybe true (_<ᴮ m) n

_M<_ : Maybe ℕ → ℕ → Type
n M< m = T (n M<ᴮ m)

open import Data.Maybe


-- size⊙< : ∀ x xs n → mapMaybe size (stack⊙ x xs) M< foldl (flip size⊙) (size x) xs
-- size⊙< (f $$ x) xs = {!!}
-- size⊙< B (f ∷ g ∷ x ∷ xs) = {!!}
-- size⊙< C (f ∷ x ∷ y ∷ xs) = {!!}
-- size⊙< K (x ∷ y ∷ xs) = {!!}
-- size⊙< _ _ = {!!}

-- size< : ∀ x → mapMaybe size (stack x) M< size x
-- size< x = size⊙< x []
