module Control.Monad.Free.Quotiented where

open import Prelude
open import Data.List hiding (map)
open import Data.Fin.Sigma
open import Algebra
open import Cubical.Foundations.HLevels using (isSetΠ)

--------------------------------------------------------------------------------
-- Some functors
--------------------------------------------------------------------------------

private variable
  F : Type a → Type a
  G : Type b → Type b

--------------------------------------------------------------------------------
-- A free monad without any quotients: this can be treated as the "syntax tree"
-- for the later proper free monad.
--------------------------------------------------------------------------------

data Syntax (F : Type a → Type a) (A : Type a) : Type (ℓsuc a) where
  lift   : (Fx : F A) → Syntax F A
  return : (x  : A) → Syntax F A
  _>>=_  : (xs : Syntax F B) → (k : B → Syntax F A) → Syntax F A

module RawMonadSyntax where
  _>>_ : Syntax F A → Syntax F B → Syntax F B
  xs >> ys = xs >>= const ys

--------------------------------------------------------------------------------
-- Quotients for functors
--------------------------------------------------------------------------------

-- All of these quotients are defined on syntax trees, since otherwise we get a
-- cyclic dependency.
record Equation (Σ : Type a → Type a) (ν : Type a) : Type (ℓsuc a) where
  constructor _⊜_
  field lhs rhs : Syntax Σ ν
open Equation public

record Law (F : Type a → Type a) : Type (ℓsuc a) where
  constructor _↦_⦂_
  field
    Γ : Type a
    ν : Type a
    eqn : Γ → Equation F ν
open Law public

Theory : (Type a → Type a) → Type (ℓsuc a)
Theory Σ = List (Law Σ)

private variable 𝒯 : Theory F

Quotiented : Theory F → (∀ {ν} → Syntax F ν → Syntax F ν → Type b) → Type _
Quotiented 𝒯 R =
      (i : Fin (length 𝒯)) → -- An index into the list of equations
      let Γ ↦ ν ⦂ 𝓉 = 𝒯 !! i in -- one of the equations in the list
      isSet ν → -- I *think* this is needed
      (γ : Γ) → -- The environment, basically the needed things for the equation
      R (lhs (𝓉 γ)) (rhs (𝓉 γ))

--------------------------------------------------------------------------------
-- The free monad, quotiented over a theory
--------------------------------------------------------------------------------
mutual
  data Free (F : Type a → Type a) (𝒯 : Theory F) : Type a → Type (ℓsuc a) where
  -- The first three constructors are the same as the syntax type
    lift   : (Fx : F A) → Free F 𝒯 A
    return : (x  : A) → Free F 𝒯 A
    _>>=_  : (xs : Free F 𝒯 B) → (k : B → Free F 𝒯 A) → Free F 𝒯 A

  -- The quotients for the monad laws
  -- Each of these also takes an isSet parameter: that's the only way I was able
  -- to get it to work!

    >>=-idˡ   : isSet A → (f : B → Free F 𝒯 A) (x : B) → (return x >>= f) ≡ f x
    >>=-idʳ   : isSet A → (x : Free F 𝒯 A) → (x >>= return) ≡ x
    >>=-assoc : isSet A →
                (xs : Free F 𝒯 C) (f : C → Free F 𝒯 B) (g : B → Free F 𝒯 A) →
                ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))

  -- Truncation: you wouldn't need this on a normal free monad, but I think it's
  -- theoretically sound and necessary.
    trunc : isSet A → isSet (Free F 𝒯 A)

  -- This is the quotient for the theory.
    quot : Quotiented 𝒯 (λ lhs rhs → ∣ lhs ∣↑ ≡ ∣ rhs ∣↑)
     
  -- This converts from the unquotiented syntax to the free type.
  -- You cannot go the other way!
  -- The fact that we're doing all this conversion is what makes things trickier
  -- later (and also that this is interleaved with the data definition).
  ∣_∣↑ : Syntax F A → Free F 𝒯 A
  ∣ lift x   ∣↑ = lift x
  ∣ return x ∣↑ = return x
  ∣ xs >>= k ∣↑ = ∣ xs ∣↑ >>= (∣_∣↑ ∘ k)

module FreeMonadSyntax where
  _>>_ : Free F 𝒯 A → Free F 𝒯 B → Free F 𝒯 B
  xs >> ys = xs >>= const ys

--------------------------------------------------------------------------------
-- Recursion Schemes
--------------------------------------------------------------------------------

private variable
  p : Level
  P : ∀ T → Free F 𝒯 T → Type p

-- The functor for a free monad (not really! This is a "raw" free functor)
data FreeF (F : Type a → Type a)
           (𝒯 : Theory F)
           (P : ∀ T → Free F 𝒯 T → Type b)
           (A : Type a) : Type (ℓsuc a ℓ⊔ b) where
  liftF : (Fx : F A) → FreeF F 𝒯 P A
  returnF : (x : A) → FreeF F 𝒯 P A
  bindF : (xs : Free F 𝒯 B)
          (P⟨xs⟩ : P _ xs)
          (k : B → Free F 𝒯 A)
          (P⟨∘k⟩ : ∀ x → P _ (k x)) → FreeF F 𝒯 P A

-- There can also be a quotiented free functor (I think)

-- The "in" function
⟪_⟫ : FreeF F 𝒯 P A → Free F 𝒯 A
⟪ liftF x ⟫ = lift x
⟪ returnF x ⟫ = return x
⟪ bindF xs P⟨xs⟩ k P⟨∘k⟩ ⟫ = xs >>= k

-- An algebra
Alg : (F : Type a → Type a) → (𝒯 : Theory F) → (P : ∀ T → Free F 𝒯 T → Type b) → Type _
Alg F 𝒯 P = ∀ {A} → (xs : FreeF F 𝒯 P A) → P A ⟪ xs ⟫

-- You can run a non-coherent algebra on a syntax tree
⟦_⟧↑ : Alg F 𝒯 P → (xs : Syntax F A) → P A ∣ xs ∣↑
⟦ alg ⟧↑ (lift x) = alg (liftF x)
⟦ alg ⟧↑ (return x) = alg (returnF x)
⟦ alg ⟧↑ (xs >>= k) = alg (bindF ∣ xs ∣↑ (⟦ alg ⟧↑ xs) (∣_∣↑ ∘ k) (⟦ alg ⟧↑ ∘ k))

-- Coherency for an algebra: an algebra that's coherent can be run on a proper
-- Free monad.
record Coherent {a p}
                {F : Type a → Type a}
                {𝒯 : Theory F}
                {P : ∀ T → Free F 𝒯 T → Type p}
                (ψ : Alg F 𝒯 P) : Type (ℓsuc a ℓ⊔ p) where
  field
    c-set : ∀ {T} → isSet T → ∀ xs → isSet (P T xs)

    c->>=idˡ : ∀ (isb : isSet B) (f : A → Free F 𝒯 B) Pf x →
      ψ (bindF (return x) (ψ (returnF x)) f Pf)
        ≡[ i ≔ P _ (>>=-idˡ isb f x i) ]≡ Pf x

    c->>=idʳ : ∀ (isa : isSet A) (x : Free F 𝒯 A) Px →
      ψ (bindF x Px return (λ y → ψ (returnF y)))
        ≡[ i ≔ P A (>>=-idʳ isa x i) ]≡ Px

    c->>=assoc : ∀ (isa : isSet A)
      (xs : Free F 𝒯 C) Pxs
      (f : C → Free F 𝒯 B) Pf
      (g : B → Free F 𝒯 A) Pg →
      ψ (bindF (xs >>= f) (ψ (bindF xs Pxs f Pf)) g Pg)
        ≡[ i ≔ P A (>>=-assoc isa xs f g i) ]≡
          ψ (bindF xs Pxs (λ x → f x >>= g) λ x → ψ (bindF (f x) (Pf x) g Pg))

    c-quot : (i : Fin (length 𝒯)) →
             let Γ ↦ ν ⦂ 𝓉 = 𝒯 !! i in
             (iss : isSet ν) →
             (γ : Γ) →
             ⟦ ψ ⟧↑ (lhs (𝓉 γ)) ≡[ j ≔ P ν (quot i iss γ j) ]≡ ⟦ ψ ⟧↑ (rhs (𝓉 γ))
open Coherent public

-- A full dependent algebra
Ψ : (F : Type a → Type a) (𝒯 : Theory F) (P : ∀ T → Free F 𝒯 T → Type p) → Type _
Ψ F 𝒯 P = Σ (Alg F 𝒯 P) Coherent

Ψ-syntax : (F : Type a → Type a) (𝒯 : Theory F) (P : ∀ {T} → Free F 𝒯 T → Type p) → Type _
Ψ-syntax F 𝒯 P = Ψ F 𝒯 (λ T → P {T})

syntax Ψ-syntax F 𝒯 (λ xs → P) = Ψ[ xs ⦂ F ⋆ * / 𝒯 ] ⇒ P

-- Non-dependent algebras
Φ : (F : Type a → Type a) → (𝒯 : Theory F) → (Type a → Type b) → Type _
Φ A 𝒯 B = Ψ A 𝒯 (λ T _ → B T)

syntax Φ F 𝒯 (λ A → B) = Φ[ F ⋆ A / 𝒯 ] ⇒ B

-- Running the algebra
module _ (ψ : Ψ F 𝒯 P) where
  ⟦_⟧ : (xs : Free F 𝒯 A) → P A xs

  -- We need the terminating pragma here because Agda can't see that ∣_∣↑ makes
  -- something the same size (I think)
  {-# TERMINATING #-}
  undecorate : (xs : Syntax F A) → ⟦ fst ψ ⟧↑ xs ≡ ⟦ ∣ xs ∣↑ ⟧
  undecorate (lift x) i = fst ψ (liftF x)
  undecorate (return x) i = fst ψ (returnF x)
  undecorate (xs >>= k) i =
    fst ψ
        (bindF ∣ xs ∣↑ (undecorate xs i) (λ x → ∣ k x ∣↑)
        (λ x → undecorate (k x) i))

  ⟦ lift x ⟧ = ψ .fst (liftF x)
  ⟦ return x ⟧ = ψ .fst (returnF x)
  ⟦ xs >>= k ⟧ = ψ .fst (bindF xs ⟦ xs ⟧ k (⟦_⟧ ∘ k))

  ⟦ >>=-idˡ iss f k i ⟧ = ψ .snd .c->>=idˡ iss f (⟦_⟧ ∘ f) k i
  ⟦ >>=-idʳ iss xs i ⟧ = ψ .snd .c->>=idʳ iss xs ⟦ xs ⟧ i
  ⟦ >>=-assoc iss xs f g i ⟧ =
    ψ .snd .c->>=assoc iss xs ⟦ xs ⟧ f (⟦_⟧ ∘ f) g (⟦_⟧ ∘ g) i

  ⟦ quot p iss e i ⟧ =
      subst₂ (PathP (λ j → P _ (quot p iss e j)))
              (undecorate _)
              (undecorate _)
              (ψ .snd .c-quot p iss e) i

  ⟦ trunc AIsSet xs ys p q i j ⟧ =
    isOfHLevel→isOfHLevelDep 2
      (ψ .snd .c-set AIsSet)
      ⟦ xs ⟧ ⟦ ys ⟧
      (cong ⟦_⟧ p) (cong ⟦_⟧ q)
      (trunc AIsSet xs ys p q)
      i j

-- For a proposition, use this to prove the algebra is coherent
prop-coh : {alg : Alg F 𝒯 P} → (∀ {T} → isSet T → ∀ xs → isProp (P T xs)) → Coherent alg
prop-coh P-isProp .c-set TIsSet xs = isProp→isSet (P-isProp TIsSet xs)
prop-coh {P = P} P-isProp .c->>=idˡ iss f Pf x =
  toPathP (P-isProp iss (f x) (transp (λ i → P _ (>>=-idˡ iss f x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=idʳ iss x Px =
  toPathP (P-isProp iss x (transp (λ i → P _ (>>=-idʳ iss x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=assoc iss xs Pxs f Pf g Pg =
  toPathP (P-isProp iss (xs >>= (λ x → f x >>= g)) (transp (λ i → P _ (>>=-assoc iss xs f g i)) i0 _) _)
prop-coh {𝒯 = 𝒯} {P = P} P-isProp .c-quot i iss e =
  toPathP (P-isProp iss (∣ (𝒯 !! i) .eqn e .rhs ∣↑) (transp (λ j → P _ (quot i iss e j)) i0 _) _)

-- A more conventional catamorphism
module _ {ℓ} (fun : Functor ℓ ℓ) where
  open Functor fun using (map; 𝐹)
  module _ {B : Type ℓ} {𝒯 : Theory 𝐹} (BIsSet : isSet B) where
    module _ (ϕ : 𝐹 B → B) where
      ϕ₁ : Alg 𝐹 𝒯 λ T _ → (T → B) → B
      ϕ₁ (liftF x) h = ϕ (map h x)
      ϕ₁ (returnF x) h = h x
      ϕ₁ (bindF _ P⟨xs⟩ _ P⟨∘k⟩) h = P⟨xs⟩ (flip P⟨∘k⟩ h)

      InTheory : Type _
      InTheory = Quotiented 𝒯 λ lhs rhs → ∀ f → ⟦ ϕ₁ ⟧↑ lhs f ≡ ⟦ ϕ₁ ⟧↑ rhs f

      module _ (ϕ-coh : InTheory) where
        cata-coh : Coherent ϕ₁
        cata-coh .c-set _ _ = isSetΠ λ _ → BIsSet
        cata-coh .c->>=idˡ isb f Pf x = refl
        cata-coh .c->>=idʳ isa x Px = refl
        cata-coh .c->>=assoc isa xs Pxs f Pf g Pg = refl
        cata-coh .c-quot i iss e j f = ϕ-coh i iss e f j

        cata-alg : Φ[ 𝐹 ⋆ A / 𝒯 ] ⇒ ((A → B) → B)
        cata-alg = ϕ₁ , cata-coh

    cata : (A → B) → (ϕ : 𝐹 B → B) → InTheory ϕ → Free 𝐹 𝒯 A → B
    cata h ϕ coh xs = ⟦ cata-alg ϕ coh ⟧ xs h

