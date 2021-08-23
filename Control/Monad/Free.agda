{-# OPTIONS --safe #-}

module Control.Monad.Free where

open import Prelude

data Free (F : Type a → Type a) (A : Type a) : Type (ℓsuc a) where
  lift : F A → Free F A

  return : A → Free F A
  _>>=_ : Free F B → (B → Free F A) → Free F A

  >>=-idˡ : (f : B → Free F A) (x : B) → (return x >>= f) ≡ f x
  >>=-idʳ : (x : Free F A) → (x >>= return) ≡ x
  >>=-assoc : (xs : Free F C) (f : C → Free F B) (g : B → Free F A) → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))

  trunc : isSet (Free F A)

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
    c-set : ∀ {T} xs → isSet (P {T = T} xs) -- possibly needs to be isSet T → isSet (P {T = T} xs)

    c->>=idˡ : ∀ (f : A → Free F B) Pf x → ψ (bindF (return x) (ψ (returnF x)) f Pf) ≡[ i ≔ P (>>=-idˡ f x i) ]≡ Pf x
    c->>=idʳ : ∀ (x : Free F A) Px → ψ (bindF x Px return (λ y → ψ (returnF y))) ≡[ i ≔ P (>>=-idʳ x i) ]≡ Px
    c->>=assoc : ∀
      (xs : Free F C) Pxs
      (f : C → Free F B) Pf
      (g : B → Free F A) Pg →
      ψ (bindF (xs >>= f) (ψ (bindF xs Pxs f Pf)) g Pg)
        ≡[ i ≔ P (>>=-assoc xs f g i) ]≡
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
⟦ alg ⟧ (>>=-idˡ f k i) = alg .snd .c->>=idˡ f (⟦ alg ⟧ ∘ f) k i
⟦ alg ⟧ (>>=-idʳ xs i) = alg .snd .c->>=idʳ xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (>>=-assoc xs f g i) = alg .snd .c->>=assoc xs (⟦ alg ⟧ xs) f (⟦ alg ⟧ ∘ f) g (⟦ alg ⟧ ∘ g) i
⟦ alg ⟧ (trunc xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-set)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc xs ys p q)
    i j

prop-coh : {alg : Alg F P} → (∀ {T} xs → isProp (P {T} xs)) → Coherent alg
prop-coh P-isProp .c-set xs = isProp→isSet (P-isProp xs)
prop-coh {P = P} P-isProp .c->>=idˡ f Pf x =
  toPathP (P-isProp (f x) (transp (λ i → P (>>=-idˡ f x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=idʳ x Px =
  toPathP (P-isProp x (transp (λ i → P (>>=-idʳ x i)) i0 _) _)
prop-coh {P = P} P-isProp .c->>=assoc xs Pxs f Pf g Pg =
  toPathP (P-isProp (xs >>= (λ x → f x >>= g)) (transp (λ i → P (>>=-assoc xs f g i)) i0 _) _)

infix 4 _⊜_
record AnEquality (F : Type a → Type a) (A : Type a) : Type (ℓsuc a) where
  constructor _⊜_
  field lhs rhs : Free F A
open AnEquality public

EqualityProof-Alg : (F : Type a → Type a) (P : ∀ {A} → Free F A → AnEquality G A) → Type _
EqualityProof-Alg F P = Alg F (λ xs → let Pxs = P xs in lhs Pxs ≡ rhs Pxs)

eq-coh : {P : ∀ {A} → Free F A → AnEquality G A} {alg : EqualityProof-Alg F P} → Coherent alg
eq-coh {P = P} = prop-coh λ xs → let Pxs = P xs in trunc (lhs Pxs) (rhs Pxs)

-- open import Algebra

-- module _ {F : Type a → Type a} where
--   freeMonad : Monad a (ℓsuc a)
--   freeMonad .Monad.𝐹 = Free F
--   freeMonad .Monad.isMonad .IsMonad._>>=_ = _>>=_
--   freeMonad .Monad.isMonad .IsMonad.return = return
--   freeMonad .Monad.isMonad .IsMonad.>>=-idˡ = >>=-idˡ
--   freeMonad .Monad.isMonad .IsMonad.>>=-idʳ = >>=-idʳ
--   freeMonad .Monad.isMonad .IsMonad.>>=-assoc = >>=-assoc

-- module _ {ℓ} (mon : Monad ℓ ℓ) where
--   module F = Monad mon

--   open F using (𝐹)

--   module _ {G : Type ℓ → Type ℓ} (FisSet : ∀ {T} → isSet (𝐹 T)) (h : ∀ {T} → G T → 𝐹 T) where
--     ⟦_⟧ : Free G A → 𝐹 A
--     ⟦ lift x ⟧ = h x
--     ⟦ return x ⟧ = F.return x
--     ⟦ xs >>= k ⟧ = ⟦ xs ⟧ F.>>= λ x → ⟦ k x ⟧
--     ⟦ >>=-idˡ f x i ⟧ = F.>>=-idˡ (⟦_⟧ ∘ f) x i
--     ⟦ >>=-idʳ xs i ⟧ = F.>>=-idʳ ⟦ xs ⟧ i
--     ⟦ >>=-assoc xs f g i ⟧ = F.>>=-assoc ⟦ xs ⟧ (⟦_⟧ ∘ f) (⟦_⟧ ∘ g) i

--     ⟦ trunc xs ys p q i j ⟧ =
--       isOfHLevel→isOfHLevelDep 2
--         (λ xs → FisSet)
--         ⟦ xs ⟧ ⟦ ys ⟧
--         (cong ⟦_⟧ p) (cong ⟦_⟧ q)
--         (trunc xs ys p q)
--         i j

--     -- module _ (hom : MonadHomomorphism freeMonad {F = G} ⟶ mon) where
--     --   module Hom = MonadHomomorphism_⟶_ hom
--     --   open Hom using (f)

--     --   uniq : (inv : ∀ {A : Type _} → (x : G A) → f (lift x) ≡ h x) (xs : Free G A) → ⟦ xs ⟧ ≡ f xs
--     --   uniq inv (lift x) = sym (inv x)
--     --   uniq inv (return x) = sym (Hom.return-homo x)
--     --   uniq inv (xs >>= k) = cong₂ F._>>=_ (uniq inv xs) (funExt (λ x → uniq inv (k x))) ; Hom.>>=-homo xs k

--     --   uniq inv (>>=-idˡ f₁ x i) = FisSet {!f (>>=-idˡ f₁ x i0)!} {!!} {!!} {!!} i

--     --   uniq inv (>>=-idʳ xs i) = {!!}
--     --   uniq inv (>>=-assoc xs f₁ g i) = {!!}

--     --   uniq inv (trunc xs ys p q i j) =
--     --     isOfHLevel→isOfHLevelDep 2
--     --       (λ xs → isProp→isSet (FisSet _ _))
--     --       (uniq inv xs) (uniq inv ys)
--     --       (cong (uniq inv) p) (cong (uniq inv) q)
--     --       (trunc xs ys p q)
--     --       i j

-- module _ {ℓ} (fun : Functor ℓ ℓ) where
--   open Functor fun using (map; 𝐹)
--   module _ {B : Type ℓ} (BIsSet : isSet B) where

--     cata : (A → B) → (𝐹 B → B) → Free 𝐹 A → B
--     cata h ϕ (lift x) = ϕ (map h x)
--     cata h ϕ (return x) = h x
--     cata h ϕ (xs >>= k) = cata (cata h ϕ ∘ k) ϕ xs

--     cata h ϕ (>>=-idˡ f x i) = cata h ϕ (f x)
--     cata h ϕ (>>=-idʳ xs i) = cata h ϕ xs
--     cata h ϕ (>>=-assoc xs f g i) = cata (cata (cata h ϕ ∘ g) ϕ ∘ f) ϕ xs
--     cata h ϕ (trunc xs ys p q i j) =
--       isOfHLevel→isOfHLevelDep 2
--         (λ xs → BIsSet)
--         (cata h ϕ xs) (cata h ϕ ys)
--         (cong (cata h ϕ) p) (cong (cata h ϕ) q)
--         (trunc xs ys p q)
--         i j
