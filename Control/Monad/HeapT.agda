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


monus : TMAPOM ℓ
CommutativeMonoid.monoid (TMPOM.commutativeMonoid (TMAPOM.tmpom monus)) = monoid
CommutativeMonoid.comm (TMPOM.commutativeMonoid (TMAPOM.tmpom monus)) = comm
TMPOM._≤|≥_ (TMAPOM.tmpom monus) = tot
TMAPOM.antisym monus = atsm

open TMAPOM monus hiding (monoid; 𝑆; _∙_; assoc; comm; ε; ε∙; ∙ε)

private
  variable
    w : 𝑆

mutual
  Heaped :  Type ℓ → 𝑆 → Type ℓ
  Heaped A w = 𝐹 w (Root A)

  data Root (A : Type ℓ) : Type ℓ where
    [] : Root A
    _∷_ : (x : Branch A) → (xs : 𝐹 ε (Root A)) → Root A

  data Branch (A : Type ℓ) : Type ℓ where
    leaf : A → Branch A
    node : (w : 𝑆) (xs : Heaped A w) → Branch A

Heap : Type ℓ → Type ℓ
Heap A = Heaped A ε

_++_ : 𝐹 w (Root A) → 𝐹 ε (Root A) → 𝐹 w (Root A)
xs ++ ys = xs >>=[ ∙ε _ ] ( λ { [] → ys ; (x ∷ xs) → pure (x ∷ (xs ++ ys))})

hbind : (A → Heap B) → Heaped A w → Heaped B w
rbind : (A → Heap B) → Root A → Heap B
bbind : (A → Heap B) → Branch A → Heap B

hbind f xs = xs >>=[ ∙ε _ ] rbind f

bbind f (leaf x) = f x
bbind f (node y ys) = pure (node y (hbind f ys) ∷ pure [])

rbind f [] = pure []
rbind f (x ∷ xs) = bbind f x ++ hbind f xs

liftT : 𝐹 w A → Heaped A w
liftT = map λ x → leaf x ∷ pure []

pushT : Heaped A w → Heap A
pushT {w = w} x = pure (node w x ∷ pure [])

open import Data.List hiding (map)

partition : List (Branch A) → List A × List (Σ 𝑆 (Heaped A))
partition = foldr f ([] , [])
  where
  f : Branch A → List A × List (Σ 𝑆 (Heaped A)) → List A × List (Σ 𝑆 (Heaped A))
  f (leaf x) = map₁ (x ∷_)
  f (node w xs) = map₂ ((w , xs) ∷_)

flattenTop : Heaped A w → 𝐹 w (List (Branch A))
flattenTop xs = xs >>=[ ∙ε _ ] λ { [] → pure [] ; (x ∷ xs) → map (x ∷_) (flattenTop xs)}

module _ (decomp : ∀ {A B} {w₁ w₂ w₃} → 𝐹 (w₁ ∙ w₂) A → 𝐹 (w₁ ∙ w₃) B → 𝐹 w₁ (𝐹 w₂ A × 𝐹 w₃ B)) where
  merge : ∃ (Heaped A) → ∃ (Heaped A) → ∃ (Heaped A)
  merge (wˣ , xs) (wʸ , ys) with wˣ ≤|≥ wʸ
  ... | inl (k , x≤y) = wˣ , map (λ { (xs , ys) → node k ys ∷ xs }) (decomp (subst (flip 𝐹 _) (sym (∙ε _)) xs) (subst (flip 𝐹 _) x≤y ys))
  ... | inr (k , y≤x) = wʸ , map (λ { (ys , xs) → node k xs ∷ ys }) (decomp (subst (flip 𝐹 _) (sym (∙ε _)) ys) (subst (flip 𝐹 _) y≤x xs))

  mergeLists⁺ : ∃ (Heaped A) → List (∃ (Heaped A)) → ∃ (Heaped A)
  mergeLists⁺ x₁ [] = x₁
  mergeLists⁺ x₁ (x₂ ∷ []) = merge x₁ x₂
  mergeLists⁺ x₁ (x₂ ∷ x₃ ∷ xs) = merge (merge x₁ x₂) (mergeLists⁺ x₃ xs)

  mergeLists : List (∃ (Heaped A)) → Maybe (∃ (Heaped A))
  mergeLists [] = nothing
  mergeLists (x ∷ xs) = just (mergeLists⁺ x xs)

  popMin : Heaped A w → 𝐹 w (List A × Maybe (∃ (Heaped A)))
  popMin = map (map₂ mergeLists ∘ partition) ∘ flattenTop
