{-# OPTIONS --no-positivity-check --allow-unsolved-metas #-}

open import Algebra
open import Prelude
open import Relation.Binary
open import WellFounded
open import Algebra.Monus
open import Data.Maybe

module Control.Comonad.Stepped {s}
  (mon : TMAPOM s)
  (comon : GradedComonad (TMAPOM.monoid mon) s )
  (functor : Functor s s)
  where

open TMAPOM mon
open GradedComonad comon renaming (𝐹 to 𝑊; map to cmap)
open Functor functor renaming (map to fmap)

CofreeF : Type s → 𝑆 → Type s → Type s
CofreeF A w B = 𝑊 w (A × 𝐹 B)

functorCofreeF : ∀ {w} → IsFunctor (CofreeF A w)
functorCofreeF .IsFunctor.map f = cmap (map₂ (fmap f))
functorCofreeF .IsFunctor.map-id = {!!}
functorCofreeF .IsFunctor.map-comp = {!!}

module _ {A : Type s} where
  open import Codata.SegFix commutativeMonoid (CofreeF A) (functorCofreeF {A = A}) public using (Fix; unfold)

Cofree⁺ : Type s → 𝑆 → Type s
Cofree⁺ A = Fix {A = A}

Cofree : Type s → Type s
Cofree A = Cofree⁺ A ε

private variable u v w : 𝑆

traceT-alg : (𝑊 ε A → B) → (𝑊 ε A → 𝐹 (∃ v × (v ≢ ε) × 𝑊 v A)) → 𝑊 w A → CofreeF B w (∃ v × (v ≢ ε) × 𝑊 v A)
traceT-alg f c r = r =>>[ ∙ε _ ] λ rs → f rs , c rs

module _ (wf : WellFounded _≺_) where

  traceT : (𝑊 ε A → B) → (𝑊 ε A → 𝐹 (∃ v × (v ≢ ε) × 𝑊 v A)) → 𝑊 w A → Cofree⁺ B w
  traceT f c = unfold wf (flip 𝑊 _) (traceT-alg f c)


--   extend-alg : (Cofree A → B) → Cofree⁺ A w → CofreeF B w (∃ v × (v ≢ ε) × Cofree⁺ A v)
--   extend-alg {w = w} f xs = xs =>>[ ∙ε _ ] (λ ys → f ys , fmap (λ k → fst (k {i = w}) , {!!} , cmap {!!} (snd (k {i = w}))) (snd (extract ys)))

--   extend : (Cofree A → B) → Cofree⁺ A w → Cofree⁺ B w
--   extend f = unfold wf (Cofree⁺ _) (extend-alg f)


-- Weighted : (𝑆 → Type a → Type b) → Type a → Type (s ℓ⊔ b)
-- Weighted C A = ∃ w × C w A


-- module OnFunctor (functor : Functor s s) where
--   open Functor functor renaming (map to fmap)

--   record Cofree⁺ (w : 𝑆) (A : Type s) : Type s where
--     constructor ⟪_⟫
--     field step : 𝑊 w (A × 𝐹 (Weighted Cofree⁺ A))
--   open Cofree⁺ public

--   Cofree : Type s → Type s
--   Cofree = Cofree⁺ ε

--   extend : (Cofree A → B) → Cofree⁺ w A → Cofree⁺ w B
--   extend f x .step = x .step =>>[ ∙ε _ ] λ ys → f ⟪ ys ⟫ , fmap (map₂ (extend f)) (snd (extract ys)) 

--   extract′ : Cofree A → A
--   extract′ = fst ∘ extract ∘ step


--   iterT : (𝑊 ε A → 𝐹 (Weighted 𝑊 A)) → 𝑊 ε A → Cofree A
--   iterT = traceT extract

-- module AsHeap (_<*>_ : ∀ {w A B} → 𝑊 w (A → B) → 𝑊 w A → 𝑊 w B) where
--   open import Data.List.Properties using (listFunctor)
--   open import Data.List using (List; _∷_; [])
--   open OnFunctor listFunctor
--   Heap : Type s → Type s
--   Heap = Weighted Cofree⁺ 

--   _∪_ : Heap A → Heap A → Heap A
--   (xʷ , xs) ∪ (yʷ , ys) with xʷ ≤|≥ yʷ
--   ... | inl (k , y≡x∙k) = xʷ , ⟪ (step ys =>>[ sym y≡x∙k ] λ { y (x , xs) → x , ((k , ⟪ y ⟫) ∷ xs)}) <*> step xs ⟫
--   ... | inr (k , x≡y∙k) = yʷ , ⟪ (step xs =>>[ sym x≡y∙k ] λ { x (y , ys) → y , ((k , ⟪ x ⟫) ∷ ys)}) <*> step ys ⟫

--   merge⁺ : Heap A → List (Heap A) → Heap A
--   merge⁺ x [] = x
--   merge⁺ x₁ (x₂ ∷ []) = x₁ ∪ x₂
--   merge⁺ x₁ (x₂ ∷ x₃ ∷ xs) = (x₁ ∪ x₂) ∪ merge⁺ x₃ xs

--   merge : List (Heap A) → Maybe (Heap A)
--   merge [] = nothing
--   merge (x ∷ xs) = just (merge⁺ x xs)

  
--   open import Data.Maybe.Properties using (maybeFunctor)
--   open import Data.Maybe using (mapMaybe)

--   module L = OnFunctor maybeFunctor

--   search : Cofree⁺ w A → L.Cofree⁺ w A
--   search = L.⟪_⟫ ∘ map (map₂ (mapMaybe (map₂ search) ∘ merge)) ∘ step
  


-- -- data Heap (A : Type s) : Type s where
-- --   _◃_ : (w : 𝑆) → (xs : 𝐹 w (A × List (Heap A))) → Heap A

-- -- extend : (Heap A → B) → Heap A → Heap B
-- -- extend f (w ◃ xs) = w ◃ (xs =>>[ ∙ε w ] (λ ys → f (ε ◃ ys) , Lmap (extend f) (snd (extract ys))))

-- -- module _ (2-monoid : ∀ {A B w} → 𝐹 w A → 𝐹 w B → 𝐹 w (A × B)) where
-- --   _∪_ : Heap A → Heap A → Heap A
-- --   (xw ◃ xs) ∪ (yw ◃ ys) with xw ≤|≥ yw
-- --   ... | inl (k , p) = xw ◃ map (λ { (y , (x , xs)) → x , (k ◃ y) ∷ xs }) (2-monoid (ys =>>[ sym p ] id) xs)
-- --   ... | inr (k , p) = yw ◃ map (λ { (x , (y , ys)) → y , (k ◃ x) ∷ ys }) (2-monoid (xs =>>[ sym p ] id) ys)

-- -- -- mutual
-- -- --   record Heap (A : Type a) : Type (s ℓ⊔ a) where
-- -- --     inductive; constructor _◃_
-- -- --     field
-- -- --       hd : A
-- -- --       tl : Next A

-- -- --   record Next {a} (A : Type a) : Type (s ℓ⊔ a) where
-- -- --     coinductive; constructor ⟪_⟫
-- -- --     field next : Span A

-- -- --   data Span {a} (A : Type a) : Type (s ℓ⊔ a) where
-- -- --     [] : Span A
-- -- --     until : (s : 𝑆) → (s≢ε : s ≢ ε) → (xs : Heap A) → Span A
-- -- -- open Heap public
-- -- -- open Next public

-- -- -- State : Type a → Type _
-- -- -- State A = 𝑆 → A × 𝑆

-- -- -- pop′ : (s : 𝑆) → Acc _<_ s → Heap A → A × 𝑆
-- -- -- pop′ s₂ a xs with xs .tl .next
-- -- -- pop′ s₂ a xs | [] = xs .hd , ε
-- -- -- pop′ s₂ a xs | until s₁ s₁≢ε ys with s₁ ≤? s₂
-- -- -- pop′ s₂ a xs | until s₁ s₁≢ε ys | no s₁≰s₂ = xs .hd , fst (<⇒≤ s₁≰s₂)
-- -- -- pop′ s₂ (acc wf) xs | until s₁ s₁≢ε ys | yes (k₁ , s₂≡s₁∙k₁) = pop′ k₁ (wf k₁ lemma) ys
-- -- --   where
-- -- --   lemma : k₁ < s₂
-- -- --   lemma (k₂ , k₁≡s₂∙k₂) = s₁≢ε (zeroSumFree s₁ k₂ (sym (cancel k₁ _ _ p)))
-- -- --     where
-- -- --     p : k₁ ∙ ε ≡ k₁ ∙ (s₁ ∙ k₂)
-- -- --     p = ∙ε k₁ ; k₁≡s₂∙k₂ ; cong (_∙ k₂) s₂≡s₁∙k₁ ; cong (_∙ k₂) (comm s₁ k₁) ; assoc k₁ s₁ k₂

-- -- -- pop : Heap A → State A
-- -- -- pop xs s = pop′ s (wf s) xs

-- -- -- mutual
-- -- --   stepFrom : State A → (s : 𝑆) → Dec (s ≡ ε) → Span A
-- -- --   stepFrom f s (yes p) = []
-- -- --   stepFrom f s (no ¬p) = until s ¬p (tabulate (f ∘ (s ∙_)))

-- -- --   tabulate : State A → Heap A
-- -- --   tabulate f =
-- -- --     let x , s = f ε
-- -- --     in x ◃ λ where .next → stepFrom f s (s ≟ ε)

-- -- -- pop-ε : (xs : Heap A) (a : Acc _<_ ε) → pop′ ε a xs .fst ≡ xs .hd
-- -- -- pop-ε xs _ with xs .tl .next
-- -- -- pop-ε xs _ | [] = refl
-- -- -- pop-ε xs _ | until s s≢ε ys with s ≤? ε
-- -- -- pop-ε xs _ | until s s≢ε ys | no  s≰ε = refl
-- -- -- pop-ε xs _ | until s s≢ε ys | yes s≤ε = ⊥-elim (s≢ε (antisym s≤ε (positive s)))

-- -- -- -- slide : Heap A → Heap A
-- -- -- -- slide xs with xs .tl .next
-- -- -- -- slide xs | [] = xs
-- -- -- -- slide xs | [] = []

-- -- -- -- pop-tl : ∀ (x : A) s₁ (s₁≢ε : s₁ ≢ ε) xs s₂ → pop (x ◃ ⟪ until s₁ s₁≢ε xs ⟫) (s₁ ∙ s₂) ≡ pop xs s₂
-- -- -- -- pop-tl x s₁ s₁≢ε xs s₂ with s₁ ≤? (s₁ ∙ s₂)
-- -- -- -- pop-tl x s₁ s₁≢ε xs s₂ | no  s₁≰s₁∙s₂ = ⊥-elim (s₁≰s₁∙s₂ (s₂ , refl))
-- -- -- -- pop-tl x s₁ s₁≢ε xs s₂ | yes (k , s₁≤s₁∙s₂) =
-- -- -- --   let p = cancel s₁ s₂ k s₁≤s₁∙s₂
-- -- -- --   in {!!} ; cong (λ w → pop′ s₂ w xs) (isPropAcc {!!} (wf s₂))

-- -- -- -- seg-leftInv′ : (x : Heap A) → tabulate (pop x) ≡ x
-- -- -- -- seg-leftInv′ x = {!!}

-- -- -- -- mutual
-- -- -- --   seg-leftInv′ : (xs : Heap A) → stepFrom (pop xs) (pop xs ε .snd) (pop xs ε .snd ≟ ε) ≡ xs .tl .next
-- -- -- --   seg-leftInv′ (x ◃ xs) with pop (x ◃ xs) ε .snd ≟ ε
-- -- -- --   seg-leftInv′ (x ◃ xs) | yes s≡ε = {!!}
-- -- -- --   seg-leftInv′ (x ◃ xs) | no  s≢ε = {!!}

-- -- -- --   seg-leftInv : (x : Heap A) → tabulate (pop x) ≡ x
-- -- -- --   seg-leftInv (x ◃ xs) i .hd = pop-ε (x ◃ xs) (wf ε) i
-- -- -- --   seg-leftInv (x ◃ xs) i .tl .next = seg-leftInv′ (x ◃ xs) i

-- -- -- -- state-iso : Heap A ⇔ State A
-- -- -- -- state-iso .fun = pop
-- -- -- -- state-iso .inv = tabulate
-- -- -- -- state-iso .rightInv = {!!}
-- -- -- -- state-iso .leftInv  = {!!}
