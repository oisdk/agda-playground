{-# OPTIONS --cubical --safe #-}

module BCK where

open import Prelude hiding (B; C)

infixl 4 _$$_
data BCK : Type where
  _$$_ : BCK → BCK → BCK
  B C K : BCK

open import Data.List

stack : BCK → Maybe BCK
stack xs = go xs []
  where
  go : BCK → List BCK → Maybe BCK
  go (f $$ x) xs = go f (x ∷ xs)
  go B (f ∷ g ∷ x ∷ xs) = just (foldl _$$_ (f $$ (g $$ x)) xs)
  go C (f ∷ x ∷ y ∷ xs) = just (foldl _$$_ (f $$ y $$ x) xs)
  go K (x ∷ y ∷ xs) = just (foldl _$$_ x xs)
  go _ _ = nothing

