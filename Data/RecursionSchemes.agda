{-# OPTIONS --cubical --safe --postfix-projections --guardedness #-}

module Data.RecursionSchemes where

open import Prelude hiding (C; _⊎_; const; id; _×_)
open import Container
open import Container.Fixpoint
open import Container.Polynomial hiding (_∘_)

private
  variable
    s p : Level
    C : Container s p

cmap : (A → B) → ⟦ C ⟧ A → ⟦ C ⟧ B
cmap f (s , p) = (s , f ∘ p)

cata : (⟦ C ⟧ A → A) → μ C → A
cata alg (sup (s , p)) = alg (s , cata alg ∘ p)

pcata : ∀ {pr} (P : μ C → Type pr) → ((xs : ⟦ C ⟧ (∃ P)) → P (sup (cmap fst xs))) → ∀ x → P x
pcata P alg (sup (s , p)) = alg (s , λ i → let x = p i in x , pcata P alg x)


ana : (A → ⟦ C ⟧ A) → A → ν C
ana alg x =
  let s , p = alg x in
  λ where
    .inf .fst → s
    .inf .snd i → ana alg (p i)

LIST : Type a → Type a
LIST {a} A = μ {s = a} {p = ℓzero} (const ⊤ ⊎ const A × id {s = ℓzero})

open import Data.List

list-to : LIST A → List A
list-to = cata alg
  where
  alg : ⟦ const ⊤ ⊎ const A × id ⟧ (List A) → List A
  alg (inl x , p) = []
  alg (inr (x , _) , p) = x ∷ p (inr _)

list-fro : List A → LIST A
list-fro [] = sup (inl _ , λ ())
list-fro (x ∷ xs) = sup (inr (x , _) , λ _ → list-fro xs)

rinv : (xs : List A) → list-to (list-fro xs) ≡ xs
rinv [] = refl
rinv (x ∷ xs) = cong (x ∷_) (rinv xs)

linv : (xs : LIST A) → list-fro (list-to xs) ≡ xs
linv = pcata (λ xs → list-fro (list-to xs) ≡ xs) λ { (inl tt , p) → cong sup (cong₂ _,_ refl (funExt λ ())) ; (inr x , p) → cong sup (cong₂ _,_ refl let q = p (inr _) .snd in funExt λ { (inr x) → q})}

list-iso : LIST A ⇔ List A
list-iso .fun = list-to
list-iso .inv = list-fro
list-iso .rightInv = rinv
list-iso .leftInv  = linv
