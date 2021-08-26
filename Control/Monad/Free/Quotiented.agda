module Control.Monad.Free.Quotiented where

open import Prelude
open import Data.List hiding (map)
open import Data.List.Relation.Unary
open import Data.Fin

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
  lift′   : (Fx : F A) → Syntax F A
  return′ : (x  : A) → Syntax F A
  _>>=′_  : (xs : Syntax F B) → (k : B → Syntax F A) → Syntax F A

--------------------------------------------------------------------------------
-- Quotients for functors
--------------------------------------------------------------------------------

-- All of these quotients are defined on syntax trees, since otherwise we get a
-- cyclic dependency.
Equation : (Type a → Type a) → Type a → Type a → Type (ℓsuc a)
Equation Σ Γ ν = Γ → Syntax Σ ν × Syntax Σ ν

Theory : (Type a → Type a) → Type (ℓsuc a)
Theory Σ = List (∃ Γ × ∃ ν × Equation Σ Γ ν)

private variable 𝒯 : Theory F

Quotiented : Theory F → (∀ {ν} → Syntax F ν → Syntax F ν → Type b) → Type _
Quotiented 𝒯 cons =
      (i : Fin (length 𝒯)) → -- An index into the list of equations
      let Γ , ν , 𝓉 = 𝒯 ! i in -- one of the equations in the list
      isSet ν → -- I *think* this is needed
      (γ : Γ) → -- The environment, basically the needed things for the equation
      let lhs , rhs = 𝓉 γ in -- The two sides of the equation
      cons lhs rhs

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
    quot : Quotiented 𝒯 λ lhs rhs → ∣ lhs ∣↑ ≡ ∣ rhs ∣↑
     
  -- This converts from the unquotiented syntax to the free type.
  -- You cannot go the other way!
  -- The fact that we're doing all this conversion is what makes things trickier
  -- later (and also that this is interleaved with the data definition).
  ∣_∣↑ : Syntax F A → Free F 𝒯 A
  ∣ lift′ x   ∣↑ = lift x
  ∣ return′ x ∣↑ = return x
  ∣ xs >>=′ k ∣↑ = ∣ xs ∣↑ >>= (∣_∣↑ ∘ k)

--------------------------------------------------------------------------------
-- Recursion Schemes
--------------------------------------------------------------------------------

private variable
  p : Level
  P : ∀ T → Free F 𝒯 T → Type p

-- The functor for a free monad
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
⟦ alg ⟧↑ (lift′ x) = alg (liftF x)
⟦ alg ⟧↑ (return′ x) = alg (returnF x)
⟦ alg ⟧↑ (xs >>=′ k) = alg (bindF ∣ xs ∣↑ (⟦ alg ⟧↑ xs) (∣_∣↑ ∘ k) (⟦ alg ⟧↑ ∘ k))

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
             let Γ , ν , 𝓉 = 𝒯 ! i in
             (iss : isSet ν) →
             (γ : Γ) →
             let lhs , rhs = 𝓉 γ in
             ⟦ ψ ⟧↑ lhs ≡[ j ≔ P ν (quot i iss γ j) ]≡ ⟦ ψ ⟧↑ rhs
open Coherent public

open import Path.Reasoning

Ψ : (F : Type a → Type a) (𝒯 : Theory F) (P : ∀ T → Free F 𝒯 T → Type p) → Type _
Ψ F 𝒯 P = Σ (Alg F 𝒯 P) Coherent

⟦_⟧ : Ψ F 𝒯 P → (xs : Free F 𝒯 A) → P A xs

{-# TERMINATING #-}
lemma₂ : (alg : Ψ F 𝒯 P) (xs : Syntax F A) → ⟦ fst alg ⟧↑ xs ≡ ⟦ alg ⟧ ∣ xs ∣↑
lemma₂ alg (lift′ x) i = fst alg (liftF x)
lemma₂ alg (return′ x) i = fst alg (returnF x)
lemma₂ alg (xs >>=′ k) i =
  fst alg
      (bindF ∣ xs ∣↑ (lemma₂ alg xs i) (λ x → ∣ k x ∣↑)
       (λ x → lemma₂ alg (k x) i))

⟦ alg ⟧ (lift x) = alg .fst (liftF x)
⟦ alg ⟧ (return x) = alg .fst (returnF x)
⟦ alg ⟧ (xs >>= k) = alg .fst (bindF xs (⟦ alg ⟧ xs) k (⟦ alg ⟧ ∘ k))
⟦ alg ⟧ (>>=-idˡ iss f k i) = alg .snd .c->>=idˡ iss f (⟦ alg ⟧ ∘ f) k i
⟦ alg ⟧ (>>=-idʳ iss xs i) = alg .snd .c->>=idʳ iss xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (>>=-assoc iss xs f g i) = alg .snd .c->>=assoc iss xs (⟦ alg ⟧ xs) f (⟦ alg ⟧ ∘ f) g (⟦ alg ⟧ ∘ g) i
⟦_⟧ {𝒯 = 𝒯} {P = P} alg (quot ind iss e i) =
  let Γ , v , eqn = 𝒯 ! ind
      lhs , rhs = eqn e
  in subst₂ (PathP (λ j → P v (quot ind iss e j))) (lemma₂ alg lhs) (lemma₂ alg rhs) (alg .snd .c-quot ind iss e) i

⟦ alg ⟧ (trunc AIsSet xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-set AIsSet)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc AIsSet xs ys p q)
    i j

Φ : (F : Type a → Type a) → (𝒯 : Theory F) → (Type a → Type b) → Type _
Φ A 𝒯 B = Ψ A 𝒯 (λ T _ → B T)

prop-coh : {alg : Alg F 𝒯 P} → (∀ {T} → isSet T → ∀ xs → isProp (P T xs)) → Coherent alg
prop-coh P-isProp .c-set TIsSet xs = isProp→isSet (P-isProp TIsSet xs)
prop-coh {P = P} P-isProp .c->>=idˡ iss f Pf x =
  toPathP (P-isProp iss (f x) (transp (λ i → P _ (>>=-idˡ iss f x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=idʳ iss x Px =
  toPathP (P-isProp iss x (transp (λ i → P _ (>>=-idʳ iss x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=assoc iss xs Pxs f Pf g Pg =
  toPathP (P-isProp iss (xs >>= (λ x → f x >>= g)) (transp (λ i → P _ (>>=-assoc iss xs f g i)) i0 _) _)
prop-coh {𝒯 = 𝒯} {P = P} P-isProp .c-quot i iss e =
  toPathP (P-isProp iss (∣ (𝒯 ! i) .snd .snd e .snd ∣↑) (transp (λ j → P _ (quot i iss e j)) i0 _) _)


open import Algebra

open import Cubical.Foundations.HLevels using (isSetΠ)

module _ {ℓ} (fun : Functor ℓ ℓ) where
  open Functor fun using (map; 𝐹)
  module _ {B : Type ℓ} {𝒯 : Theory 𝐹} (BIsSet : isSet B) where
    module _ (ϕ : 𝐹 B → B) where
      act : Alg 𝐹 𝒯 λ T _ → (T → B) → B
      act (liftF x) h = ϕ (map h x)
      act (returnF x) h = h x
      act (bindF _ P⟨xs⟩ _ P⟨∘k⟩) h = P⟨xs⟩ (flip P⟨∘k⟩ h)


    module _ (ϕ : 𝐹 B → B) where
      InTheory : Type _
      InTheory = 
       ∀ (i : Fin (length 𝒯)) →
              let Γ , V , eqn = 𝒯 ! i in
              (f : V → B)
              (iss : isSet V) →
              (e : Γ) →
              let lhs , rhs = eqn e in
              (⟦ act ϕ ⟧↑ lhs f) ≡ (⟦ act ϕ ⟧↑ rhs f)

    module _ (ϕ : 𝐹 B → B) (act-lemma : InTheory ϕ) where

      cata-alg : Ψ 𝐹 𝒯 λ T _ → (T → B) → B
      cata-alg .fst = act ϕ
      cata-alg .snd .c-set _ _ = isSetΠ λ _ → BIsSet
      cata-alg .snd .c->>=idˡ isb f Pf x = refl
      cata-alg .snd .c->>=idʳ isa x Px = refl
      cata-alg .snd .c->>=assoc isa xs Pxs f Pf g Pg = refl
      cata-alg .snd .c-quot i iss e j f = act-lemma i f iss e j

    cata : (A → B) → (ϕ : 𝐹 B → B) → InTheory ϕ → Free 𝐹 𝒯 A → B
    cata h ϕ l xs = ⟦ cata-alg ϕ l ⟧ xs h

_>>_ : Free F 𝒯 A → Free F 𝒯 B → Free F 𝒯 B
xs >> ys = xs >>= const ys
