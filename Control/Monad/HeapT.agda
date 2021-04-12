{-# OPTIONS --cubical --no-positivity-check --no-termination-check #-}

open import Prelude
open import Algebra
open import Algebra.Monus
open import Relation.Binary

module Control.Monad.HeapT
  {ℓ}
  (gmon : GradedMonad ℓ ℓ ℓ)
  (comm : Commutative (GradedMonad._∙_ gmon))
  (tot : Total (λ x y → ∃[ z ] (y ≡ (GradedMonad._∙_ gmon x z))))
  (atsm : Antisymmetric (λ x y → ∃[ z ] (y ≡ (GradedMonad._∙_ gmon x z))))
  where

open GradedMonad gmon


monus : Monus ℓ
CommutativeMonoid.monoid (Monus.commutativeMonoid monus) = monoid
CommutativeMonoid.comm (Monus.commutativeMonoid monus) = comm
Monus._≤|≥_ monus = tot
Monus.antisym monus = atsm

open Monus monus hiding (monoid; 𝑆; _∙_; assoc; comm; ε)

private
  variable
    x y z : 𝑆

mutual
  Heaped : 𝑆 → Type ℓ → Type ℓ
  Heaped x A = 𝐹 x (Root x A)

  data Root (x : 𝑆) (A : Type ℓ) : Type ℓ where
    [] : Root x A
    _∷_ : Branch x A → Heaped x A → Root x A

  data Branch (x : 𝑆) (A : Type ℓ) : Type ℓ where
    leaf : A → Branch x A
    node : (y : 𝑆) (ys : Heaped (x ∙ y) A) → Branch x A

Heap : Type ℓ → Type ℓ
Heap = Heaped ε

hmap : (A → B) → Heaped x A → Heaped x B
bmap : (A → B) → Branch x A → Branch x B

hmap f = map λ { [] → [] ; (x ∷ xs) → bmap f x ∷ hmap f xs}
bmap f (leaf x) = leaf (f x)
bmap f (node y ys) = node y (hmap f ys)

-- -- _++_ : Heaped ε A → Heaped ε A → Heaped ε A
-- -- xs ++ ys = xs >>=[ {!!} ] (λ { [] → ys ; (x ∷ xs) → pure (x ∷ (xs ++ ys)) })


-- hbind : (A → Heap B) → Heaped x A → Heaped x B
-- bbind : (A → Heap B) → Branch x A → Heap B

-- hbind f xs′ = xs′ >>=[ ∙ε _ ]
--   (λ { [] → pure []
--      ; (x ∷ xs) →
--        let y = bbind f x
--            ys = hbind f xs
--        in {! !}})

-- bbind f (leaf x) = f x
-- bbind f (node y ys) = pure (node y {!!} ∷ pure [])

-- -- mutual
-- --   bind : ∀ {x} → Heaped x A → (A → Heaped ε B) → Heaped x B
-- --   bind xs f = subst (flip 𝐹 _) (∙ε _) (xs >>= go f)

-- --   go : (A → Heaped ε B) → Root x A → 𝐹 ε (Root x B)
-- --   go f [] = pure []
-- --   go f (leaf x    ∷ xs) =
-- --     let p = f x
-- --         q = bind xs f
-- --     in {!!}
-- --   go f (node y ys ∷ xs) = {!!}

-- --   -- go′ : (A → Heaped ε B) → Branch x A → Heaped x B → Root x B
-- --   -- go′ f (leaf x) xs = {!!}
-- --   -- go′ f (node y ys) zs = {!!}
