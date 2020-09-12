{-# OPTIONS --cubical --safe #-}

module Data.List.Relation.Unary where

open import Prelude
open import Data.List.Base
open import Data.Fin
open import Relation.Nullary
open import Data.Sum

private
  variable p : Level

module Inductive◇ where
 data ◇ {A : Type a} (P : A → Type p) : List A → Type (a ℓ⊔ p) where
   here   : ∀ {x xs} → P x      → ◇ P (x ∷ xs)
   there  : ∀ {x xs} → ◇ P xs   → ◇ P (x ∷ xs)

◇ : (P : A → Type p) → List A → Type _
◇ P xs = ∃[ i ] P (xs ! i)

◇! : (P : A → Type p) → List A → Type _
◇! P xs = isContr (◇ P xs)

module Exists {a} {A : Type a} {p} (P : A → Type p) where
  push : ∀ {x xs} → ◇ P xs → ◇ P (x ∷ xs)
  push (n , p) = fs n , p

  pull : ∀ {x xs} → ¬ P x → ◇ P (x ∷ xs) → ◇ P xs
  pull ¬Px (f0   , p) = ⊥-elim (¬Px p)
  pull ¬Px (fs n , p) = n , p

  uncons : ∀ {x xs} → ◇ P (x ∷ xs) → P x ⊎ ◇ P xs
  uncons (f0 , p) = inl p
  uncons (fs x , p) = inr (x , p)

  infixr 5 _++◇_ _◇++_
  _++◇_ : ∀ {xs} ys → ◇ P xs → ◇ P (ys ++ xs)
  [] ++◇ ys = ys
  (x ∷ xs) ++◇ ys = push (xs ++◇ ys)

  _◇++_ : ∀ xs → ◇ P xs → ∀ {ys} → ◇ P (xs ++ ys)
  _◇++_ (x ∷ xs) (f0  , ∃Pxs) = f0 , ∃Pxs
  _◇++_ (x ∷ xs) (fs n , ∃Pxs) = push (xs ◇++ (n , ∃Pxs))

  push! : ∀ {x xs} → ¬ P x → ◇! P xs → ◇! P (x ∷ xs)
  push! ¬Px x∈!xs .fst = push (x∈!xs .fst)
  push! ¬Px x∈!xs .snd (f0   , px) = ⊥-elim (¬Px px)
  push! ¬Px x∈!xs .snd (fs n  , y∈xs) i = push (x∈!xs .snd (n , y∈xs) i)

  pull! : ∀ {x xs} → ¬ P x → ◇! P (x ∷ xs) → ◇! P xs
  pull! ¬Px ((f0   , px    ) , uniq) = ⊥-elim (¬Px px)
  pull! ¬Px ((fs n  , x∈xs  ) , uniq) .fst = (n , x∈xs)
  pull! ¬Px ((fs n  , x∈xs  ) , uniq) .snd (m , x∈xs′) i =
    pull ¬Px (uniq (fs m , x∈xs′ ) i)

  here! : ∀ {x xs} → isContr (P x) → ¬ ◇ P xs → ◇! P (x ∷ xs)
  here! Px p∉xs .fst = f0 , Px .fst
  here! Px p∉xs .snd (f0  , p∈xs) i .fst = f0
  here! Px p∉xs .snd (f0  , p∈xs) i .snd = Px .snd p∈xs i
  here! Px p∉xs .snd (fs n , p∈xs) = ⊥-elim (p∉xs (n , p∈xs))

  module _ (P? : ∀ x → Dec (P x)) where
    open import Relation.Nullary.Decidable.Logic

    ◇? : ∀ xs → Dec (◇ P xs)
    ◇? [] = no λ ()
    ◇? (x ∷ xs) =  ⟦yes ⟦l f0 ,_ ,r push ⟧ ,no uncons ⟧ (P? x || ◇? xs)

◻ : (P : A → Type p) → List A → Type _
◻ P xs = ∀ i → P (xs ! i)

module Forall {a} {A : Type a} {p} (P : A → Type p) where
  push : ∀ {x xs} → P x → ◻ P xs → ◻ P (x ∷ xs)
  push Px Pxs f0 = Px
  push Px Pxs (fs n) = Pxs n

  uncons : ∀ {x xs} → ◻ P (x ∷ xs) → P x × ◻ P xs
  uncons Pxs = Pxs f0 , Pxs ∘ fs

  pull : ∀ {x xs} → ◻ P (x ∷ xs) → ◻ P xs
  pull = snd ∘ uncons

  _++◇_ : ∀ xs {ys} → ◻ P (xs ++ ys) → ◻ P ys
  [] ++◇ xs⊆P = xs⊆P
  (x ∷ xs) ++◇ xs⊆P = xs ++◇ (xs⊆P ∘ fs)

  _◇++_ : ∀ xs {ys} → ◻ P (xs ++ ys) → ◻ P xs
  ([] ◇++ xs⊆P) ()
  ((x ∷ xs) ◇++ xs⊆P) f0 = xs⊆P f0
  ((x ∷ xs) ◇++ xs⊆P) (fs n) = (xs ◇++ pull xs⊆P) n

  both : ∀ xs {ys} → ◻ P xs → ◻ P ys → ◻ P (xs ++ ys)
  both [] xs⊆P ys⊆P = ys⊆P
  both (x ∷ xs) xs⊆P ys⊆P f0 = xs⊆P f0
  both (x ∷ xs) xs⊆P ys⊆P (fs i) = both xs (pull xs⊆P) ys⊆P i

  empty : ◻ P []
  empty ()

  module _ where
    open import Relation.Nullary.Decidable.Logic
    ◻? : (∀ x → Dec (P x)) → ∀ xs → Dec (◻ P xs)
    ◻? P? [] = yes λ ()
    ◻? P? (x ∷ xs) =  ⟦yes uncurry push
                      ,no uncons
                      ⟧ (P? x && ◻? P? xs)

module Forall-NotExists {a} {A : Type a} {p} (P : A → Type p) where
  open import Relation.Nullary.Stable
  open import Data.Empty.Properties

  open Forall P
  ¬P = ¬_ ∘ P
  module ∃¬ = Exists ¬P

  ∀⇒¬∃¬ : ∀ xs → ◻ P xs → ¬ (◇ ¬P xs)
  ∀⇒¬∃¬ (x ∷ xs) xs⊆P (f0 , ∃¬P∈xs) = ∃¬P∈xs(xs⊆P f0)
  ∀⇒¬∃¬ (x ∷ xs) xs⊆P (fs n , ∃¬P∈xs) = ∀⇒¬∃¬ xs (xs⊆P ∘ fs) (n , ∃¬P∈xs)

  module _ (stable : ∀ {x} → Stable (P x)) where
    ¬∃¬⇒∀ : ∀ xs → ¬ (◇ ¬P xs) → ◻ P xs
    ¬∃¬⇒∀ (x ∷ xs) ¬∃¬P∈xs f0 = stable (¬∃¬P∈xs ∘ (f0 ,_))
    ¬∃¬⇒∀ (x ∷ xs) ¬∃¬P∈xs (fs n) = ¬∃¬⇒∀ xs (¬∃¬P∈xs ∘ ∃¬.push) n

    leftInv′ : ∀ (prop : ∀ {x} → isProp (P x)) xs → (x : ◻ P xs) → ¬∃¬⇒∀ xs (∀⇒¬∃¬ xs x) ≡ x
    leftInv′ prop [] x i ()
    leftInv′ prop (x ∷ xs) xs⊆P i f0 = prop (stable λ ¬p → ¬p (xs⊆P f0)) (xs⊆P f0) i
    leftInv′ prop (x ∷ xs) xs⊆P i (fs n) = leftInv′ prop xs (pull xs⊆P) i n

    ∀⇔¬∃¬ : ∀ (prop : ∀ {x} → isProp (P x)) xs → ◻ P xs ⇔ (¬ ◇ ¬P xs)
    ∀⇔¬∃¬ _ xs .fun = ∀⇒¬∃¬ xs
    ∀⇔¬∃¬ _ xs .inv = ¬∃¬⇒∀ xs
    ∀⇔¬∃¬ p xs .leftInv  = leftInv′ p xs
    ∀⇔¬∃¬ _ xs .rightInv x = isProp¬ _ _ x

module Exists-NotForall {a} {A : Type a} {p} (P : A → Type p) where
  open Exists P
  ¬P = ¬_ ∘ P
  module ∀¬ = Forall ¬P

  ∃⇒¬∀¬ : ∀ xs → ◇ P xs → ¬ ◻ ¬P xs
  ∃⇒¬∀¬ (x ∷ xs) (f0  , P∈xs) xs⊆P = xs⊆P f0 P∈xs
  ∃⇒¬∀¬ (x ∷ xs) (fs n , P∈xs) xs⊆P = ∃⇒¬∀¬ xs (n , P∈xs) (xs⊆P ∘ fs)

  module _ (P? : ∀ x → Dec (P x)) where
    ¬∀¬⇒∃ : ∀ xs → ¬ ◻ ¬P xs → ◇ P xs
    ¬∀¬⇒∃ [] ¬xs⊆¬P = ⊥-elim (¬xs⊆¬P λ ())
    ¬∀¬⇒∃ (x ∷ xs) ¬xs⊆¬P with P? x
    ¬∀¬⇒∃ (x ∷ xs) ¬xs⊆¬P | yes p = f0 , p
    ¬∀¬⇒∃ (x ∷ xs) ¬xs⊆¬P | no ¬p = push (¬∀¬⇒∃ xs (¬xs⊆¬P ∘ ∀¬.push ¬p))

module Congruence {p q} (P : A → Type p) (Q : B → Type q)
                  {f : A → B} (f↑ : ∀ {x} → P x → Q (f x)) where
  cong-◇ : ∀ xs → ◇ P xs → ◇ Q (map f xs)
  cong-◇ (x ∷ xs) (f0 , P∈xs) = f0 , f↑ P∈xs
  cong-◇ (x ∷ xs) (fs n , P∈xs) = Exists.push Q (cong-◇ xs (n , P∈xs))

◇-concat : ∀ (P : A → Type p) xs → ◇ (◇ P) xs → ◇ P (concat xs)
◇-concat P (x ∷ xs) (f0 , ps) = Exists._◇++_ P x ps
◇-concat P (x ∷ xs) (fs n , ps) = Exists._++◇_ P x (◇-concat P xs (n , ps))

◻-concat : ∀ (P : A → Type p) xs → ◻ (◻ P) xs → ◻ P (concat xs)
◻-concat P [] xs⊆P ()
◻-concat P (x ∷ xs) xs⊆P = Forall.both P x (xs⊆P f0) (◻-concat P xs (xs⊆P ∘ fs))

module Search {A : Type a} where
  data Result {p} (P : A → Type p) (xs : List A) : Bool → Type (a ℓ⊔ p) where
    all′ : ◻ P xs → Result P xs true
    except′ : ◇ (¬_ ∘ P) xs → Result P xs false

  record Found {p} (P : A → Type p) (xs : List A) : Type (a ℓ⊔ p) where
    field
      found? : Bool
      result : Result P xs found?
  open Found public

  pattern all    ps = record { found? = true ; result = all′ ps }
  pattern except ¬p = record { found? = false ; result = except′ ¬p }

  module _ {p} {P : A → Type p} (P? : ∀ x → Dec (P x)) where
    search : ∀ xs → Found P xs
    search [] = all λ ()
    search (x ∷ xs) = search′ x xs (P? x) (search xs)
      where
      search′ : ∀ x xs → Dec (P x) → Found P xs → Found P (x ∷ xs)
      search′ x xs Px Pxs .found? = Px .does and Pxs .found?
      search′ x xs (no ¬p) Pxs .result = except′ (f0 , ¬p)
      search′ x xs (yes p) (except ¬p) .result = except′ (Exists.push (¬_ ∘ P) ¬p)
      search′ x xs (yes p) (all ps) .result = all′ (Forall.push P p ps)
