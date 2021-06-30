{-# OPTIONS --cubical --safe #-}

module Data.Tuple.UniverseMonomorphic where

open import Prelude
open import Data.Fin
Tuple : ∀ n → (Fin n → Type) → Type
Tuple zero     f = ⊤
Tuple (suc n)  f = f f0 × Tuple n (f ∘ fs)

private
  variable
    n : ℕ
    U : Fin n → Type

ind : Tuple n U → (i : Fin n) → U i
ind {n = suc n} (x , xs) f0     = x
ind {n = suc n} (x , xs) (fs i) = ind xs i

tab : ((i : Fin n) → U i) → Tuple n U
tab {n = zero}  f = tt
tab {n = suc n} f = f f0 , tab (f ∘ fs)

Π→Tuple→Π : ∀ {n} {U : Fin n → Type} (xs : (i : Fin n) → U i) i → ind (tab xs) i ≡ xs i
Π→Tuple→Π {n = suc n} f f0 = refl
Π→Tuple→Π {n = suc n} f (fs i) = Π→Tuple→Π (f ∘ fs) i

Tuple→Π→Tuple : ∀ {n} {U : Fin n → Type} (xs : Tuple n U) → tab (ind xs) ≡ xs
Tuple→Π→Tuple {n = zero} tt = refl
Tuple→Π→Tuple {n = suc n} (x , xs) i .fst = x
Tuple→Π→Tuple {n = suc n} (x , xs) i .snd = Tuple→Π→Tuple xs i

Tuple⇔ΠFin :
 Tuple n U ⇔ ((i : Fin n) → U i)
Tuple⇔ΠFin .fun = ind
Tuple⇔ΠFin .inv = tab
Tuple⇔ΠFin .leftInv = Tuple→Π→Tuple
Tuple⇔ΠFin .rightInv x = funExt (Π→Tuple→Π x)
