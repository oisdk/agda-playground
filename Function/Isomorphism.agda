{-# OPTIONS --cubical --safe #-}

module Function.Isomorphism where

open import Cubical.Foundations.Equiv using (isoToEquiv) public
open import Cubical.Foundations.Isomorphism using (Iso; section; retract; isoToPath; iso) public
open import Level
open import Path
open import Function
open import Data.Sigma
open import Relation.Binary

open Iso public

infix 4 _⇔_
_⇔_ = Iso

sym-⇔ : (A ⇔ B) → (B ⇔ A)
fun (sym-⇔ A⇔B) = inv A⇔B
inv (sym-⇔ A⇔B) = fun A⇔B
leftInv (sym-⇔ A⇔B) = rightInv A⇔B
rightInv (sym-⇔ A⇔B) = leftInv A⇔B

refl-⇔ : A ⇔ A
fun refl-⇔ x = x
inv refl-⇔ x = x
leftInv refl-⇔ x = refl
rightInv refl-⇔  x = refl

trans-⇔ : A ⇔ B → B ⇔ C → A ⇔ C
fun      (trans-⇔ A⇔B B⇔C) = fun B⇔C ∘ fun A⇔B
inv      (trans-⇔ A⇔B B⇔C) = inv A⇔B ∘ inv B⇔C
leftInv  (trans-⇔ A⇔B B⇔C) x = cong (inv A⇔B) (leftInv B⇔C _) ; leftInv A⇔B _
rightInv (trans-⇔ A⇔B B⇔C) x = cong (fun B⇔C) (rightInv A⇔B _) ; rightInv B⇔C _

iso-Σ : {B : A → Type b} {C : A → Type c} → (∀ x → B x ⇔ C x) → Σ A B ⇔ Σ A C
iso-Σ B⇔C .fun (x , xs) = x , B⇔C x .fun xs
iso-Σ B⇔C .inv (x , xs) = x , B⇔C x .inv xs
iso-Σ B⇔C .rightInv (x , xs) i .fst = x
iso-Σ B⇔C .rightInv (x , xs) i .snd = B⇔C x .rightInv xs i
iso-Σ B⇔C .leftInv (x , xs) i .fst = x
iso-Σ B⇔C .leftInv (x , xs) i .snd = B⇔C x .leftInv xs i

⇔-equiv : Equivalence (Type a) a
Equivalence._≋_ ⇔-equiv = _⇔_
Equivalence.sym ⇔-equiv = sym-⇔
Equivalence.refl ⇔-equiv = refl-⇔
Equivalence.trans ⇔-equiv = trans-⇔

open import HLevels
open import Equiv

iso⇔equiv : isSet A → (A ⇔ B) ⇔ (A ≃ B)
iso⇔equiv isSetA .fun = isoToEquiv
iso⇔equiv isSetA .inv = equivToIso
iso⇔equiv isSetA .rightInv x i .fst = x .fst
iso⇔equiv isSetA .rightInv x i .snd = isPropIsEquiv (x .fst) (isoToEquiv (equivToIso x) .snd) (x .snd) i
iso⇔equiv isSetA .leftInv x i .fun = x .fun
iso⇔equiv isSetA .leftInv x i .inv = x .inv
iso⇔equiv isSetA .leftInv x i .rightInv = x .rightInv
iso⇔equiv isSetA .leftInv x i .leftInv y = isSetA _ y (equivToIso (isoToEquiv x) .leftInv y) (x .leftInv y) i
