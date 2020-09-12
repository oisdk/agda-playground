{-# OPTIONS --cubical --safe #-}

module Data.Tuple.Base where

open import Prelude hiding (⊤; tt)
open import Data.Unit.UniversePolymorphic
open import Data.Fin

Tuple : ∀ n → (Lift a (Fin n) → Type b) → Type b
Tuple zero    f = ⊤
Tuple {a = a} {b = b} (suc n) f = f (lift f0) × Tuple {a = a} {b = b} n (f ∘ lift ∘ fs ∘ lower)

private
  variable
    n : ℕ
    u : Level
    U : Lift a (Fin n) → Type u

ind : Tuple n U → (i : Lift a (Fin n)) → U i
ind {n = suc n} (x , xs) (lift f0)     = x
ind {n = suc n} (x , xs) (lift (fs i)) = ind xs (lift i)

tab : ((i : Lift a (Fin n)) → U i) → Tuple n U
tab {n = zero}  f = tt
tab {n = suc n} f = f (lift f0) , tab (f ∘ lift ∘ fs ∘ lower)

Π→Tuple→Π : ∀ {a n u} {U : Lift a (Fin n) → Type u} (xs : (i : Lift a (Fin n)) → U i) i → ind (tab xs) i ≡ xs i
Π→Tuple→Π {n = suc n} f (lift f0) = refl
Π→Tuple→Π {n = suc n} f (lift (fs i)) = Π→Tuple→Π (f ∘ lift ∘ fs ∘ lower) (lift i)

Tuple→Π→Tuple : ∀ {n} {U : Lift a (Fin n) → Type u} (xs : Tuple n U) → tab (ind xs) ≡ xs
Tuple→Π→Tuple {n = zero} tt = refl
Tuple→Π→Tuple {n = suc n} (x , xs) i .fst = x
Tuple→Π→Tuple {n = suc n} (x , xs) i .snd = Tuple→Π→Tuple xs i

Tuple⇔ΠFin : ∀ {a n u} {U : Lift a (Fin n) → Type u} → Tuple n U ⇔ ((i : Lift a (Fin n)) → U i)
Tuple⇔ΠFin .fun = ind
Tuple⇔ΠFin .inv = tab
Tuple⇔ΠFin .leftInv = Tuple→Π→Tuple
Tuple⇔ΠFin .rightInv x = funExt (Π→Tuple→Π x)
