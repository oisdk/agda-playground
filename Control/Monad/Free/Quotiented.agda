{-# OPTIONS --allow-unsolved-metas #-}

module Control.Monad.Free.Quotiented where

open import Prelude
open import Data.List hiding (map)
open import Data.List.Relation.Unary
open import Data.Fin

private
  variable
    F : Type a → Type a
    G : Type b → Type b

data Syntax (F : Type a → Type a) (A : Type a) : Type (ℓsuc a) where
  lift′   : (Fx : F A) → Syntax F A
  return′ : (x  : A) → Syntax F A
  _>>=′_  : (xs : Syntax F B) → (k : B → Syntax F A) → Syntax F A

Equation : (Type a → Type a) → Type a → Type a → Type (ℓsuc a)
Equation F Γ v = Γ → Syntax F v × Syntax F v

Theory : (Type a → Type a) → Type (ℓsuc a)
Theory F = List (∃ Γ × ∃ v × Equation F Γ v)

private variable R : Theory F

mutual
  data Free (F : Type a → Type a) (R : Theory F) : Type a → Type (ℓsuc a) where
    lift : F A → Free F R A

    return : A → Free F R A
    _>>=_ : Free F R B → (B → Free F R A) → Free F R A

    >>=-idˡ   : isSet A → (f : B → Free F R A) (x : B) → (return x >>= f) ≡ f x
    >>=-idʳ   : isSet A → (x : Free F R A) → (x >>= return) ≡ x
    >>=-assoc : isSet A → (xs : Free F R C) (f : C → Free F R B) (g : B → Free F R A) → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))

    trunc : isSet A → isSet (Free F R A)

    quot :
      (i : Fin (length R)) →
      let Γ , V , eqn = R ! i in
      isSet V →
      (e : Γ) →
      let lhs , rhs = eqn e in
      ∣ lhs ∣↑ ≡ ∣ rhs ∣↑
     

  ∣_∣↑ : Syntax F A → Free F R A
  ∣ lift′ x   ∣↑ = lift x
  ∣ return′ x ∣↑ = return x
  ∣ xs >>=′ k ∣↑ = ∣ xs ∣↑ >>= (∣_∣↑ ∘ k)

private variable
    p : Level
    P : ∀ T → Free F R T → Type p

data FreeF (F : Type a → Type a) (R : Theory F) (P : ∀ T → Free F R T → Type b) (A : Type a) : Type (ℓsuc a ℓ⊔ b) where
  liftF : F A → FreeF F R P A
  returnF : A → FreeF F R P A
  bindF : (xs : Free F R B) (P⟨xs⟩ : P _ xs) (k : B → Free F R A) (P⟨∘k⟩ : ∀ x → P _ (k x)) → FreeF F R P A

⟪_⟫ : FreeF F R P A → Free F R A
⟪ liftF x ⟫ = lift x
⟪ returnF x ⟫ = return x
⟪ bindF xs P⟨xs⟩ k P⟨∘k⟩ ⟫ = xs >>= k

Alg : (F : Type a → Type a) → (R : Theory F) → (P : ∀ T → Free F R T → Type b) → Type _
Alg F R P = ∀ {A} → (xs : FreeF F R P A) → P A ⟪ xs ⟫

⟦_⟧↑ : Alg F R P → (xs : Syntax F A) → P A ∣ xs ∣↑
⟦ alg ⟧↑ (lift′ x) = alg (liftF x)
⟦ alg ⟧↑ (return′ x) = alg (returnF x)
⟦ alg ⟧↑ (xs >>=′ k) = alg (bindF ∣ xs ∣↑ (⟦ alg ⟧↑ xs) (∣_∣↑ ∘ k) (⟦ alg ⟧↑ ∘ k))

record Coherent {a p} {F : Type a → Type a} {R : Theory F} {P : ∀ T → Free F R T → Type p} (ψ : Alg F R P) : Type (ℓsuc a ℓ⊔ p)

Ψ : (F : Type a → Type a) (R : Theory F) (P : ∀ T → Free F R T → Type p) → Type _
Ψ F R P = Σ (Alg F R P) Coherent

record Coherent {a p} {F} {R} {P} ψ where
  field
    c-set : ∀ {T} → isSet T → ∀ xs → isSet (P T xs)

    c->>=idˡ : ∀ (isb : isSet B) (f : A → Free F R B) Pf x → ψ (bindF (return x) (ψ (returnF x)) f Pf) ≡[ i ≔ P _ (>>=-idˡ isb f x i) ]≡ Pf x
    c->>=idʳ : ∀ (isa : isSet A) (x : Free F R A) Px → ψ (bindF x Px return (λ y → ψ (returnF y))) ≡[ i ≔ P A (>>=-idʳ isa x i) ]≡ Px
    c->>=assoc : ∀ (isa : isSet A)
      (xs : Free F R C) Pxs
      (f : C → Free F R B) Pf
      (g : B → Free F R A) Pg →
      ψ (bindF (xs >>= f) (ψ (bindF xs Pxs f Pf)) g Pg)
        ≡[ i ≔ P A (>>=-assoc isa xs f g i) ]≡
          ψ (bindF xs Pxs (λ x → f x >>= g) λ x → ψ (bindF (f x) (Pf x) g Pg))

    c-quot : (i : Fin (length R)) →
              let Γ , V , eqn = R ! i in
              (iss : isSet V) →
              (e : Γ) →
              let lhs , rhs = eqn e in
              ⟦ ψ ⟧↑ lhs ≡[ j ≔ P V (quot i iss e j) ]≡ ⟦ ψ ⟧↑ rhs
open Coherent public

open import Path.Reasoning

⟦_⟧ : Ψ F R P → (xs : Free F R A) → P A xs

{-# TERMINATING #-}
lemma₂ : (alg : Ψ F R P) (xs : Syntax F A) → ⟦ fst alg ⟧↑ xs ≡ ⟦ alg ⟧ ∣ xs ∣↑
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
⟦_⟧ {R = R} {P = P} alg (quot ind iss e i) =
  let Γ , v , eqn = R ! ind
      lhs , rhs = eqn e
  in subst₂ (PathP (λ j → P v (quot ind iss e j))) (lemma₂ alg lhs) (lemma₂ alg rhs) (alg .snd .c-quot ind iss e) i

⟦ alg ⟧ (trunc AIsSet xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-set AIsSet)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc AIsSet xs ys p q)
    i j

Φ : (F : Type a → Type a) → (R : Theory F) → (Type a → Type b) → Type _
Φ A R B = Ψ A R (λ T _ → B T)

prop-coh : {alg : Alg F R P} → (∀ {T} → isSet T → ∀ xs → isProp (P T xs)) → Coherent alg
prop-coh P-isProp .c-set TIsSet xs = isProp→isSet (P-isProp TIsSet xs)
prop-coh {P = P} P-isProp .c->>=idˡ iss f Pf x =
  toPathP (P-isProp iss (f x) (transp (λ i → P _ (>>=-idˡ iss f x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=idʳ iss x Px =
  toPathP (P-isProp iss x (transp (λ i → P _ (>>=-idʳ iss x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=assoc iss xs Pxs f Pf g Pg =
  toPathP (P-isProp iss (xs >>= (λ x → f x >>= g)) (transp (λ i → P _ (>>=-assoc iss xs f g i)) i0 _) _)
prop-coh {R = R} {P = P} P-isProp .c-quot i iss e =
  toPathP (P-isProp iss (∣ (R ! i) .snd .snd e .snd ∣↑) (transp (λ j → P _ (quot i iss e j)) i0 _) _)


open import Algebra

open import Cubical.Foundations.HLevels using (isSetΠ)

module _ {ℓ} (fun : Functor ℓ ℓ) where
  open Functor fun using (map; 𝐹)
  module _ {B : Type ℓ} {R : Theory 𝐹} (BIsSet : isSet B) where
    module _ (ϕ : 𝐹 B → B) where
      act : Alg 𝐹 R λ T _ → (T → B) → B
      act (liftF x) h = ϕ (map h x)
      act (returnF x) h = h x
      act (bindF _ P⟨xs⟩ _ P⟨∘k⟩) h = P⟨xs⟩ (flip P⟨∘k⟩ h)


    module _ (ϕ : 𝐹 B → B) where
      InTheory : Type _
      InTheory = 
       ∀ (i : Fin (length R)) →
              let Γ , V , eqn = R ! i in
              (f : V → B)
              (iss : isSet V) →
              (e : Γ) →
              let lhs , rhs = eqn e in
              (⟦ act ϕ ⟧↑ lhs f) ≡ (⟦ act ϕ ⟧↑ rhs f)

    module _ (ϕ : 𝐹 B → B) (act-lemma : InTheory ϕ) where

      cata-alg : Ψ 𝐹 R λ T _ → (T → B) → B
      cata-alg .fst = act ϕ
      cata-alg .snd .c-set _ _ = isSetΠ λ _ → BIsSet
      cata-alg .snd .c->>=idˡ isb f Pf x = refl
      cata-alg .snd .c->>=idʳ isa x Px = refl
      cata-alg .snd .c->>=assoc isa xs Pxs f Pf g Pg = refl
      cata-alg .snd .c-quot i iss e j f = act-lemma i f iss e j

    cata : (A → B) → (ϕ : 𝐹 B → B) → InTheory ϕ → Free 𝐹 R A → B
    cata h ϕ l xs = ⟦ cata-alg ϕ l ⟧ xs h

_>>_ : Free F R A → Free F R B → Free F R B
xs >> ys = xs >>= const ys
