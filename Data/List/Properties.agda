{-# OPTIONS --cubical --safe #-}

module Data.List.Properties where

open import Data.List
open import Prelude
open import Data.Fin

map-length : (f : A → B) (xs : List A)
           → length xs ≡ length (map f xs)
map-length f [] _ = zero
map-length f (x ∷ xs) i = suc (map-length f xs i)

map-ind : (f : A → B) (xs : List A)
        → PathP (λ i → Fin (map-length f xs i) → B) (f ∘ (xs !_)) (map f xs !_)
map-ind f [] i ()
map-ind f (x ∷ xs) i f0 = f x
map-ind f (x ∷ xs) i (fs n) = map-ind f xs i n

tab-length : ∀ n (f : Fin n → A) → length (tabulate n f) ≡ n
tab-length zero f _ = zero
tab-length (suc n) f i = suc (tab-length n (f ∘ fs) i)

tab-distrib : ∀ n (f : Fin n → A) m → ∃[ i ] (f i ≡ tabulate n f ! m)
tab-distrib (suc n) f f0 = f0 , refl
tab-distrib (suc n) f (fs m) = let i , p = tab-distrib n (f ∘ fs) m in fs i , p

tab-id : ∀ n (f : Fin n → A) → PathP (λ i → Fin (tab-length n f i) → A) (_!_ (tabulate n f)) f
tab-id zero f _ ()
tab-id (suc n) f i f0 = f f0
tab-id (suc n) f i (fs m) = tab-id n (f ∘ fs) i m
