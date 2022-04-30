{-# OPTIONS --no-positivity-check #-}

module Data.Braun where

open import Prelude hiding (_⟨_⟩_)
open import Data.Binary

record Q (A : Type a) : Type a where
  inductive
  field q : (Q A → Q A) → (Q A → Q A) → A
open Q

data Tree (A : Type a) : Type a where
  ⟨⟩ : Tree A
  ⟨_,_,_⟩ : (x : A) → (s : Tree A) → (t : Tree A) → Tree A


diff : Tree A → 𝔹 → Bool
diff ⟨⟩            _      = false
diff ⟨ _ , _ , _ ⟩ 0ᵇ     = true
diff ⟨ x , s , t ⟩ (1ᵇ k) = diff s k
diff ⟨ x , s , t ⟩ (2ᵇ k) = diff t k

size : Tree A → 𝔹
size ⟨⟩            = 0ᵇ
size ⟨ _ , s , t ⟩ = let m = size t in (if diff s m then 2ᵇ_ else 1ᵇ_) m

module _ {A : Type a} {B : Type b} where
  {-# TERMINATING #-}
  foldr𝔹 : (A → B → B) → B → Tree A → B
  foldr𝔹 c n t = f t r .q id id
    where
    f : Tree A → Q B → Q B
    f ⟨⟩            xs .q ls rs = n
    f ⟨ x , l , r ⟩ xs .q ls rs = c x (xs .q (ls ∘ f l) (rs ∘ f r))

    r : Q B
    r .q ls rs = ls (rs r) .q id id

