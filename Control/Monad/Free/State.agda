{-# OPTIONS --allow-unsolved-metas #-}

module Control.Monad.Free.State where

open import Control.Monad.Free.Quotiented
open import Prelude hiding (⊤)
open import Data.Unit.UniversePolymorphic
open import Algebra
open import Data.List
open import Data.List.Syntax


private variable S : Type a

data StateF (S : Type a) (A : Type a)  : Type a where
  getF : (S → A) → StateF S A
  putF : S → A → StateF S A

put′ : S → Syntax (StateF S) ⊤
put′ x = lift′ (putF x _)

_>>′_ : Syntax (StateF S) A → Syntax (StateF S) B → Syntax (StateF S) B
xs >>′ ys = xs >>=′ const ys

StateLaws : Theory (StateF S)
StateLaws {S = S} =
  ((S × S) , ⊤ , (λ { (u , u′) → (put′ u >>′ put′ u′) , (put′ u′) })) ∷ []

State : Type a → Type a → Type _
State S = Free (StateF S) StateLaws

get : State A A
get = lift (getF id)

put : A → State A ⊤
put x = lift (putF x _)

module _ {s} {S : Type s} where
  functorState : Functor s s
  functorState .Functor.𝐹 = StateF S
  functorState .Functor.map f (getF x) = getF (f ∘ x)
  functorState .Functor.map f (putF s x) = putF s (f x)
  functorState .Functor.map-id i (getF x) = getF x
  functorState .Functor.map-id i (putF x x₁) = putF x x₁
  functorState .Functor.map-comp f g i (getF x) = getF (f ∘ g ∘ x)
  functorState .Functor.map-comp f g i (putF x x₁) = putF x (f (g x₁))

-- runState-alg : Φ (StateF S) StateLaws λ A → S → A × S
-- runState-alg .fst (liftF (getF k)) s = k s , s
-- runState-alg .fst (liftF (putF s₂ k)) s₁ = k , s₂
-- runState-alg .fst (returnF x) s = x , s
-- runState-alg .fst (bindF _ P⟨xs⟩ _ P⟨∘k⟩) s = uncurry P⟨∘k⟩ (P⟨xs⟩ s)
-- runState-alg .snd .c-set = {!!}
-- runState-alg .snd .c->>=idˡ isb f Pf x = refl
-- runState-alg .snd .c->>=idʳ isa x Px = refl
-- runState-alg .snd .c->>=assoc isa xs Pxs f Pf g Pg = refl
-- runState-alg .snd .c-quot nothing iss e = refl

runState : State S A → S → A × S
runState = cata functorState {!!} _,_ ϕ lemma
  where
  ϕ : StateF S (S → A × S) → S → A × S
  ϕ = (λ { (getF k) s → k s s ; (putF s₂ k) s₁ → k s₂ })

  lemma : InTheory functorState {!!} ϕ
  lemma nothing f iss e = refl

  -- lemma′ : ∀ {T} → (f : T → (S → A × S)) (xs ys : Syntax (StateF S) T) → xs ≐ ys ∈ StateLaws → ⟦ act functorState {!!} ϕ ⟧↑ xs f ≡ ⟦ act functorState {!!} ϕ ⟧↑ ys f
  -- lemma′ f (lift′ x) ys (nothing , xs~ys) = let p = xs~ys in {!!}
  -- lemma′ f (return′ x) ys (nothing , xs~ys) = {!!}
  -- lemma′ f (xs >>=′ x) ys (nothing , xs~ys) = {!!}

-- open import Data.Nat using (_∸_)

-- example : State ℕ ℕ
-- example = do
--   x ← get
--   put (suc x)
--   put x
--   return (x ∸ 1)

-- res : ℕ × ℕ
-- res = runState example 5
