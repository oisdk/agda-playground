{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude hiding (⊤)

module Control.Monad.Free.State {ℓ} (S : Type ℓ) (isSetS : isSet S) where

open import Control.Monad.Free.Quotiented
open import Data.Unit.UniversePolymorphic
open import Algebra
open import Data.List
open import Data.List.Syntax
open import Cubical.Foundations.HLevels using (isSetΠ; isSet×)

data StateF (A : Type ℓ) : Type ℓ where
  getF : (k : S → A) → StateF A
  putF : (s : S) (k : A) → StateF A

put′ : S → Syntax StateF ⊤
put′ x = lift′ (putF x _)

get′ : Syntax StateF S
get′ = lift′ (getF id)

_>>′_ : Syntax StateF A → Syntax StateF B → Syntax StateF B
xs >>′ ys = xs >>=′ const ys

StateLaws : Theory StateF
StateLaws =
  ((S × S) , ⊤ , (λ { (u , u′) → (put′ u >>′ put′ u′) , (put′ u′) })) ∷
  (S , S , (λ u → (put′ u >>′ get′) , lift′ (putF u u))) ∷
  []

State : Type ℓ → Type _
State = Free StateF StateLaws

get : State S
get = lift (getF id)

put : S → State ⊤
put x = lift (putF x _)

isSetState : isSet A → isSet (S → A × S)
isSetState isSetA = isSetΠ λ _ → isSet× isSetA isSetS

state-alg : Φ[ StateF ⋆ A / StateLaws ] ⇒ (S → A × S)
state-alg .fst (liftF (getF k)) s = k s , s
state-alg .fst (liftF (putF s₂ k)) s₁ = k , s₂
state-alg .fst (returnF x) s = x , s
state-alg .fst (bindF _ P⟨xs⟩ _ P⟨∘k⟩) s = uncurry P⟨∘k⟩ (P⟨xs⟩ s)
state-alg .snd .c-set isSetT _ = isSetState isSetT
state-alg .snd .c->>=idˡ isb f Pf x = refl
state-alg .snd .c->>=idʳ isa x Px = refl
state-alg .snd .c->>=assoc isa xs Pxs f Pf g Pg = refl
state-alg .snd .c-quot nothing iss γ = refl
state-alg .snd .c-quot (just nothing) iss γ = refl

runState : State A → S → A × S
runState = ⟦ state-alg ⟧

functorState : Functor ℓ ℓ
functorState .Functor.𝐹 = StateF
functorState .Functor.map f (getF k) = getF (f ∘ k)
functorState .Functor.map f (putF s k) = putF s (f k)
functorState .Functor.map-id i (getF k) = getF k
functorState .Functor.map-id i (putF s k) = putF s k
functorState .Functor.map-comp f g i (getF k) = getF (f ∘ g ∘ k)
functorState .Functor.map-comp f g i (putF s k) = putF s (f (g k))


runState′ : isSet A → State A → S → A × S
runState′ isSetA = cata functorState (isSetState isSetA) _,_ ϕ lemma
  where
  ϕ : StateF (S → A × S) → S → A × S
  ϕ = (λ { (getF k) s → k s s ; (putF s₂ k) s₁ → k s₂ })

  lemma : InTheory functorState (isSetState isSetA) ϕ
  lemma nothing f iss e = refl
  lemma (just nothing) f iss e = refl

-- open import Data.Nat using (_∸_)

-- example : State ℕ ℕ
-- example = do
--   x ← get
--   put (suc x)
--   put x
--   return (x ∸ 1)

-- res : ℕ × ℕ
-- res = runState example 5
