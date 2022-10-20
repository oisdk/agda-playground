module Subsets where

open import Prelude

private variable n m k : ℕ

open import Data.List

Ind : ℕ → ℕ → Type
Ind (suc m) (suc k) = Ind m (suc k) ⊎ Ind (suc m) k
Ind _       _       = ⊤

Bin : Type → ℕ → ℕ → Type
Bin A m k = Ind m k → A

cd : Bin A (suc m) k → Bin (List A) m (suc k)
cd             {k = zero}  xs _       = xs tt ∷ []
cd {m = zero}  {k = suc k} xs _       = xs (inl tt) ∷ cd (xs ∘ inr) tt
cd {m = suc m} {k = suc k} xs (inl i) = cd (xs ∘ inl) i
cd {m = suc m} {k = suc k} xs (inr i) = xs (inl i)  ∷ cd (xs ∘ inr) i
