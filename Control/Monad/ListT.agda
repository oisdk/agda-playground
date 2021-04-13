{-# OPTIONS --cubical --no-positivity-check --no-termination-check #-}

open import Prelude hiding (⊤)
open import Algebra
open import Relation.Binary
open import Data.Unit.UniversePolymorphic

module Control.Monad.ListT
  {ℓ}
  (gmon : GradedMonad ℓ ℓ ℓ)
  where

open GradedMonad gmon

private
  variable
    x y z : 𝑆



infixr 5 _∷_
mutual
  record List (A : Type ℓ) (w : 𝑆) : Type ℓ where
    constructor cons
    field
      step : 𝑆
      uncons : 𝐹 step (Cons step A w)

  data Cons (w : 𝑆) (A : Type ℓ) : 𝑆 → Type ℓ where
    []  : Cons w A w
    _∷_ : {ws : 𝑆} → (x : A) → (xs : List A ws) → Cons w A (w ∙ ws)

open List

-- lmap : (A → B) → List x A → List x B
-- lmap f (cons t xs) = cons t (map (λ { [] → [] ; (x ∷ xs) → f x ∷ lmap f xs}) xs)

-- lpure : A → List ε A
-- lpure x = cons ε (pure (subst (Cons ε _) (ε∙ ε) (x ∷ cons ε (pure []))))

subst₂ : (P : A → B → Type c) → {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P p₁ p₂ = transport (cong₂ P p₁ p₂)

-- infixr 5 _++_

-- _++_ : List A x → List A y → List A (x ∙ y)
-- cons wˣ xs ++ ys =
--   let p = xs >>=[ {!!} ] λ { [] → subst₂ 𝐹 {!!} {!!} (uncons ys) ; (x ∷ xs) → subst₂ 𝐹 {!!} {!!} (pure (x ∷ (xs ++ ys))) }
--   in {!!}

postulate
  1# : 𝑆
  one : 𝐹 1# ⊤

rep : ℕ → 𝑆
rep zero = ε
rep (suc n) = 1# ∙ rep n

replicate : (n : ℕ) → List ⊤ (rep n)
replicate zero    = cons ε (pure  [])
replicate (suc n) = cons 1# (map (_∷ replicate n) one)

-- -- cons t xs ++ ys = cons t (xs >>=[ {!!} ] (λ { [] → {!!} ; (x ∷ xs) → subst₂ 𝐹 {!!} (cong (Cons t _) (sym (assoc t _ _))) (pure (x ∷ xs ++ ys))}))

-- -- -- -- -- lbind : List A → (A → List B) → List B
-- -- -- -- -- lbind xs f = xs >>= λ { [] → pure [] ; (x ∷ xs) → f x ++ lbind xs f}
