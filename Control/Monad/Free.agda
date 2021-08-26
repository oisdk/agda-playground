{-# OPTIONS --allow-unsolved-metas #-}

module Control.Monad.Free where

open import Prelude

data Free (F : Type a → Type a) (A : Type a) : Type (ℓsuc a) where
  lift : F A → Free F A

  return : A → Free F A
  _>>=_ : Free F B → (B → Free F A) → Free F A

  >>=-idˡ   : isSet A → (f : B → Free F A) (x : B) → (return x >>= f) ≡ f x
  >>=-idʳ   : isSet A → (x : Free F A) → (x >>= return) ≡ x
  >>=-assoc : isSet A → (xs : Free F C) (f : C → Free F B) (g : B → Free F A) → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))

  trunc : isSet A → isSet (Free F A)

data FreeF (F : Type a → Type a)  (P : ∀ {T} → Free F T → Type b) (A : Type a) : Type (ℓsuc a ℓ⊔ b) where
  liftF : F A → FreeF F P A
  returnF : A → FreeF F P A
  bindF : (xs : Free F B) (P⟨xs⟩ : P xs) (k : B → Free F A) (P⟨∘k⟩ : ∀ x → P (k x)) → FreeF F P A

private
  variable
    F : Type a → Type a
    G : Type b → Type b
    p : Level
    P : ∀ {T} → Free F T → Type p

⟪_⟫ : FreeF F P A → Free F A
⟪ liftF x ⟫ = lift x
⟪ returnF x ⟫ = return x
⟪ bindF xs P⟨xs⟩ k P⟨∘k⟩ ⟫ = xs >>= k

Alg : (F : Type a → Type a) (P : ∀ {T} → Free F T → Type b) → Type _
Alg F P = ∀ {A} → (xs : FreeF F P A) → P ⟪ xs ⟫

record Coherent {a p} {F : Type a → Type a} {P : ∀ {T} → Free F T → Type p} (ψ : Alg F P) : Type (ℓsuc a ℓ⊔ p) where
  field
    c-set : ∀ {T} → isSet T → ∀ xs → isSet (P {T = T} xs) -- possibly needs to be isSet T → isSet (P {T = T} xs)

    c->>=idˡ : ∀ (isb : isSet B) (f : A → Free F B) Pf x → ψ (bindF (return x) (ψ (returnF x)) f Pf) ≡[ i ≔ P (>>=-idˡ isb f x i) ]≡ Pf x
    c->>=idʳ : ∀ (isa : isSet A) (x : Free F A) Px → ψ (bindF x Px return (λ y → ψ (returnF y))) ≡[ i ≔ P (>>=-idʳ isa x i) ]≡ Px
    c->>=assoc : ∀ (isa : isSet A)
      (xs : Free F C) Pxs
      (f : C → Free F B) Pf
      (g : B → Free F A) Pg →
      ψ (bindF (xs >>= f) (ψ (bindF xs Pxs f Pf)) g Pg)
        ≡[ i ≔ P (>>=-assoc isa xs f g i) ]≡
          ψ (bindF xs Pxs (λ x → f x >>= g) λ x → ψ (bindF (f x) (Pf x) g Pg))
open Coherent public

Ψ : (F : Type a → Type a) (P : ∀ {T} → Free F T → Type p) → Type _
Ψ F P = Σ (Alg F P) Coherent

infixr 1 Ψ
syntax Ψ F (λ v → e) = Ψ[ v ⦂ F * ] ⇒ e

Φ : (Type a → Type a) → Type b → Type _
Φ A B = Ψ A (λ _ → B)

⟦_⟧ : Ψ F P → (xs : Free F A) → P xs
⟦ alg ⟧ (lift x) = alg .fst (liftF x)
⟦ alg ⟧ (return x) = alg .fst (returnF x)
⟦ alg ⟧ (xs >>= k) = alg .fst (bindF xs (⟦ alg ⟧ xs) k (⟦ alg ⟧ ∘ k))
⟦ alg ⟧ (>>=-idˡ iss f k i) = alg .snd .c->>=idˡ iss f (⟦ alg ⟧ ∘ f) k i
⟦ alg ⟧ (>>=-idʳ iss xs i) = alg .snd .c->>=idʳ iss xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (>>=-assoc iss xs f g i) = alg .snd .c->>=assoc iss xs (⟦ alg ⟧ xs) f (⟦ alg ⟧ ∘ f) g (⟦ alg ⟧ ∘ g) i
⟦ alg ⟧ (trunc AIsSet xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-set AIsSet)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc AIsSet xs ys p q)
    i j

prop-coh : {alg : Alg F P} → (∀ {T} → isSet T → ∀ xs → isProp (P {T} xs)) → Coherent alg
prop-coh P-isProp .c-set TIsSet xs = isProp→isSet (P-isProp TIsSet xs)
prop-coh {P = P} P-isProp .c->>=idˡ iss f Pf x =
  toPathP (P-isProp iss (f x) (transp (λ i → P (>>=-idˡ iss f x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=idʳ iss x Px =
  toPathP (P-isProp iss x (transp (λ i → P (>>=-idʳ iss x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=assoc iss xs Pxs f Pf g Pg =
  toPathP (P-isProp iss (xs >>= (λ x → f x >>= g)) (transp (λ i → P (>>=-assoc iss xs f g i)) i0 _) _)

-- infix 4 _⊜_
-- record AnEquality (F : Type a → Type a) (A : Type a) : Type (ℓsuc a) where
--   constructor _⊜_
--   field lhs rhs : Free F A
-- open AnEquality public

-- EqualityProof-Alg : (F : Type a → Type a) (P : ∀ {A} → Free F A → AnEquality G A) → Type _
-- EqualityProof-Alg F P = Alg F (λ xs → let Pxs = P xs in lhs Pxs ≡ rhs Pxs)

-- eq-coh : {P : ∀ {A} → Free F A → AnEquality G A} {alg : EqualityProof-Alg F P} → Coherent alg
-- eq-coh {P = P} = prop-coh λ xs → let Pxs = P xs in trunc (lhs Pxs) (rhs Pxs)

open import Algebra

module _ {F : Type a → Type a} where
  freeMonad : SetMonad a (ℓsuc a)
  freeMonad .SetMonad.𝐹 = Free F
  freeMonad .SetMonad.isSetMonad .IsSetMonad._>>=_ = _>>=_
  freeMonad .SetMonad.isSetMonad .IsSetMonad.return = return
  freeMonad .SetMonad.isSetMonad .IsSetMonad.>>=-idˡ = >>=-idˡ
  freeMonad .SetMonad.isSetMonad .IsSetMonad.>>=-idʳ = >>=-idʳ
  freeMonad .SetMonad.isSetMonad .IsSetMonad.>>=-assoc = >>=-assoc
  freeMonad .SetMonad.isSetMonad .IsSetMonad.trunc = trunc

module _ {ℓ} (mon : SetMonad ℓ ℓ) where
  module F = SetMonad mon

  open F using (𝐹)

  module _ {G : Type ℓ → Type ℓ} (h : ∀ {T} → G T → 𝐹 T) where
    ⟦_⟧′ : Free G A → 𝐹 A
    ⟦ lift x ⟧′ = h x
    ⟦ return x ⟧′ = F.return x
    ⟦ xs >>= k ⟧′ = ⟦ xs ⟧′ F.>>= λ x → ⟦ k x ⟧′
    ⟦ >>=-idˡ iss f x i ⟧′ = F.>>=-idˡ iss (⟦_⟧′ ∘ f) x i
    ⟦ >>=-idʳ iss xs i ⟧′ = F.>>=-idʳ iss ⟦ xs ⟧′ i
    ⟦ >>=-assoc iss xs f g i ⟧′ = F.>>=-assoc iss ⟦ xs ⟧′ (⟦_⟧′ ∘ f) (⟦_⟧′ ∘ g) i

    ⟦ trunc iss xs ys p q i j ⟧′ =
      isOfHLevel→isOfHLevelDep 2
        (λ xs → F.trunc iss)
        ⟦ xs ⟧′ ⟦ ys ⟧′
        (cong ⟦_⟧′ p) (cong ⟦_⟧′ q)
        (trunc iss xs ys p q)
        i j

    module _ (hom : SetMonadHomomorphism freeMonad {F = G} ⟶ mon) where
      module Hom = SetMonadHomomorphism_⟶_ hom
      open Hom using (f)

      uniq-alg : (inv : ∀ {A : Type _} → (x : G A) → f (lift x) ≡ h x) → Ψ[ xs ⦂ G * ] ⇒ ⟦ xs ⟧′ ≡ f xs
      uniq-alg inv .snd = prop-coh λ iss xs → F.trunc iss _ _
      uniq-alg inv .fst (liftF x) = sym (inv x)
      uniq-alg inv .fst (returnF x) = sym (Hom.return-homo x)
      uniq-alg inv .fst (bindF xs P⟨xs⟩ k P⟨∘k⟩) = cong₂ F._>>=_ P⟨xs⟩ (funExt P⟨∘k⟩) ; Hom.>>=-homo xs k

      uniq : (inv : ∀ {A : Type _} → (x : G A) → f (lift x) ≡ h x) → (xs : Free G A) → ⟦ xs ⟧′ ≡ f xs
      uniq inv = ⟦ uniq-alg inv ⟧

open import Cubical.Foundations.HLevels using (isSetΠ)

module _ {ℓ} (fun : Functor ℓ ℓ) where
  open Functor fun using (map; 𝐹)
  module _ {B : Type ℓ} (BIsSet : isSet B) where

    cata-alg : (𝐹 B → B) → Ψ 𝐹 λ {T} _ → (T → B) → B
    cata-alg ϕ .fst (liftF x) h = ϕ (map h x)
    cata-alg ϕ .fst (returnF x) h = h x
    cata-alg ϕ .fst (bindF _ P⟨xs⟩ _ P⟨∘k⟩) h = P⟨xs⟩ (flip P⟨∘k⟩ h)
    cata-alg ϕ .snd .c-set _ _ = isSetΠ λ _ → BIsSet
    cata-alg ϕ .snd .c->>=idˡ isb f Pf x = refl
    cata-alg ϕ .snd .c->>=idʳ isa x Px = refl
    cata-alg ϕ .snd .c->>=assoc isa xs Pxs f Pf g Pg = refl

    cata : (A → B) → (𝐹 B → B) → Free 𝐹 A → B
    cata h ϕ xs = ⟦ cata-alg ϕ ⟧ xs h

_>>_ : Free F A → Free F B → Free F B
xs >> ys = xs >>= const ys
