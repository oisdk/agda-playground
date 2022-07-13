{-# OPTIONS --allow-unsolved-metas #-}

module Container.Quotiented where

open import Prelude

record Container : Type₁ where
  constructor _◁_
  field
    Op : Type
    Arity : Op → Type
open Container

⟦_⟧ : Container → Type a → Type a
⟦ Op ◁ Arity ⟧ X = Σ[ Oᵢ ⦂ Op ] × (Arity Oᵢ → X)



open import HITs.SetQuotients
-- open Iso

record Quots (A : Type) : Type₁ where
  constructor _◁≡_
  field
    Eqns : Type
    Quot : Eqns → A ⇔ A
open Quots

AllQuots : Container → Type₁
AllQuots 𝔽 = ∀ Oᵢ → Quots (Arity 𝔽 Oᵢ)

record Container/ : Type₁ where
  constructor _/Q_
  field
    Repr : Container
    Isos : AllQuots Repr

open Container/
    
data [_]⇔ₛ (A : Type) : Type where
  ⇔ₛ-id    : [ A ]⇔ₛ
  ⇔ₛ-trans : [ A ]⇔ₛ → [ A ]⇔ₛ → [ A ]⇔ₛ
  ⇔ₛ-inv   : [ A ]⇔ₛ → [ A ]⇔ₛ
  ⇔ₛ-quot  : A → [ A ]⇔ₛ

module _ (Q : Quots A) where
  _~⟦_⟧⇔ : [ Q .Eqns ]⇔ₛ → A ⇔ A
  _~⟦_⟧⇔ ⇔ₛ-id = refl-⇔
  _~⟦_⟧⇔ (⇔ₛ-trans xs ys) = trans-⇔ (_~⟦_⟧⇔ xs) (_~⟦_⟧⇔ ys)
  _~⟦_⟧⇔ (⇔ₛ-inv xs) = sym-⇔ (_~⟦_⟧⇔ xs)
  _~⟦_⟧⇔ (⇔ₛ-quot xs) = Q .Quot xs

module _ {𝔽 : Container} {A : Type a} where
  [_]_~ₛ_ : AllQuots 𝔽 → ⟦ 𝔽 ⟧ A → ⟦ 𝔽 ⟧ A → Type a
  [ G ] (Oᵢ , f) ~ₛ (Oⱼ , f′) = Σ[ O~ ⦂ Oᵢ ≡ Oⱼ ] × Σ[ Q ⦂ [ G Oᵢ .Eqns ]⇔ₛ ] × PathP (λ i → 𝔽 .Arity (O~ i) → A) (λ x → f ((G Oᵢ ~⟦ Q ⟧⇔) .fun x)) f′

  module _ (G : AllQuots 𝔽) where
    ~ₛ-refl : (xs : ⟦ 𝔽 ⟧ A) → [ G ] xs ~ₛ xs
    ~ₛ-refl xs .fst = refl
    ~ₛ-refl xs .snd .fst = ⇔ₛ-id
    ~ₛ-refl xs .snd .snd = refl

⟦_⟧Q : Container/ → Type a → Type a
⟦ (Op ◁ Arity) /Q G ⟧Q X = ⟦ Op ◁ Arity ⟧ X / [ G ]_~ₛ_

Pair : Container
Pair .Op = ⊤
Pair .Arity _ = Bool

not-iso : Bool ⇔ Bool
not-iso .fun = not
not-iso .inv = not
not-iso .rightInv false = refl
not-iso .rightInv true  = refl
not-iso .leftInv  false = refl
not-iso .leftInv  true  = refl

Unordered : Container/
Unordered .Repr = Pair
Unordered .Isos Oᵢ .Eqns = ⊤
Unordered .Isos Oᵢ .Quot _ = not-iso

ex : ⟦ Unordered ⟧Q ℕ
ex = [ _ , bool 4 5 ]

fst′ : ⟦ Pair ⟧ A → A
fst′ (_ , f) = f false

open import Data.Nat
open import Data.Nat.Properties using (+-comm)

add′ : ⟦ Pair ⟧ ℕ → ℕ
add′ (_ , f) = f false + f true


{-# TERMINATING #-}
add″ : ⟦ Unordered ⟧Q ℕ → ℕ
add″ = rec {!!} add′ lemma
  where
  lemma : (xs ys : ⟦ Pair ⟧ ℕ) → [ Unordered .Isos ] xs ~ₛ ys → add′ xs ≡ add′ ys
  lemma xs ys (_ , ⇔ₛ-id , p) = cong add′ (cong (_,_ tt) p)
  lemma xs ys (_ , ⇔ₛ-trans l r , p) = {!!}
  lemma xs ys (_ , ⇔ₛ-inv r , p) = sym (lemma ys xs (refl , r , {!!}))
  lemma (_ , xs) (_ , ys) (_ , ⇔ₛ-quot x , p) =
    let lhs = cong (_$ false) p
        rhs = cong (_$ true) p
    in +-comm (xs false) (xs true) ; cong₂ _+_ lhs rhs
