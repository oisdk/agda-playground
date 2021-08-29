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

module Laws where
  open RawMonadSyntax
  put : S → Syntax StateF ⊤
  put x = lift (putF x _)

  get : Syntax StateF S
  get = lift (getF id)

  law₁ law₂ law₃ law₄ : Law StateF

  law₁ .Γ = S × S

  law₁ .ν = ⊤
  law₁ .eqn (u , u′) .lhs = do put u
                               put u′
  law₁ .eqn (u , u′) .rhs = put u′

  law₂ .Γ = S
  law₂ .ν = S
  law₂ .eqn u .lhs = do put u
                        u′ ← get
                        return u′
  law₂ .eqn u .rhs = do put u
                        return u

  law₃ .Γ = ⊤
  law₃ .ν = S × S
  law₃ .eqn _ .lhs = do s  ← get
                        s′ ← get
                        return (s , s′)
  law₃ .eqn _ .rhs = do s ← get
                        return (s , s)

  law₄ .Γ = ⊤
  law₄ .ν = ⊤
  law₄ .eqn _ .lhs = do s ← get
                        put s
  law₄ .eqn _ .rhs = return tt

  StateLaws : Theory StateF
  StateLaws = [ law₁ , law₂ , law₃ , law₄ ]

open Laws using (StateLaws)

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
state-alg .snd .c-quot (0 , p) iss γ = refl
state-alg .snd .c-quot (1 , p) iss γ = refl
state-alg .snd .c-quot (2 , p) iss γ = refl
state-alg .snd .c-quot (3 , p) iss γ = refl

runState : State A → S → A × S
runState = ⟦ state-alg ⟧

open FreeMonadSyntax

fromState : (S → A × S) → State A
fromState k = do
  s₁ ← get
  let x , s₂ = k s₁
  put s₂
  return x

open import Path.Reasoning

state-state : isSet A → State A ⇔ (S → A × S)
state-state _ .fun = runState
state-state _ .inv = fromState
state-state _ .rightInv _ = refl
state-state isSetA .leftInv xs = ⟦ lemma ⟧ xs isSetA
  where
  dup : S → S × S
  dup x = x , x

  lemma : Ψ StateF StateLaws (λ A xs → isSet A → fromState (runState xs) ≡ xs)
  lemma .snd = {!!}


  lemma .fst (liftF (getF k)) iss =
    fromState (runState (lift (getF k))) ≡⟨ {!!} ⟩
    lift (getF k) ∎

  lemma .fst (liftF (putF s k)) = {!!}
  lemma .fst (returnF x) = {!!}
  lemma .fst (bindF xs P⟨xs⟩ k P⟨∘k⟩) = {!!}

functorState : Functor ℓ ℓ
functorState .Functor.𝐹 = StateF
functorState .Functor.map f (getF k) = getF (f ∘ k)
functorState .Functor.map f (putF s k) = putF s (f k)
functorState .Functor.map-id i (getF k) = getF k
functorState .Functor.map-id i (putF s k) = putF s k
functorState .Functor.map-comp f g i (getF k) = getF (f ∘ g ∘ k)
functorState .Functor.map-comp f g i (putF s k) = putF s (f (g k))

runState′ : isSet A → State A → S → A × S
runState′ isSetA = cata functorState (isSetState isSetA) _,_ ϕ ℒ
  where
  ϕ : StateF (S → A × S) → S → A × S
  ϕ (getF k) s = k s s
  ϕ (putF s₂ k) s₁ = k s₂

  ℒ : InTheory functorState {𝒯 = StateLaws} (isSetState isSetA) ϕ
  ℒ (0 , p) f iss e = refl
  ℒ (1 , p) f iss e = refl
  ℒ (2 , p) f iss e = refl
  ℒ (3 , p) f iss e = refl

-- open import Data.Nat using (_∸_)

-- example : State ℕ ℕ
-- example = do
--   x ← get
--   put (suc x)
--   put x
--   return (x ∸ 1)

-- res : ℕ × ℕ
-- res = runState example 5
