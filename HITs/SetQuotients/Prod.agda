{-# OPTIONS --allow-unsolved-metas #-}

module HITs.SetQuotients.Prod where

open import Prelude
open import HITs.SetQuotients
open import Data.Vec.Iterated
import Data.Unit.UniversePolymorphic as Poly

private variable n : ℕ

Vec-Rel : (A → A → Type b) → Vec A n → Vec A n → Type b
Vec-Rel {n = zero}  R xs ys = Poly.⊤
Vec-Rel {n = suc n} R (x ∷ xs) (y ∷ ys) = R x y × Vec-Rel R xs ys

private variable R : A → A → Type b


trav : {A : Type a} {R : A → A → Type b} → Vec (A / R) n → Vec A n / Vec-Rel R
trav {n = zero}  xs = [ [] ]
trav {n = suc n} (x ∷ xs) = rec squash/ (λ x′ → rec squash/ (λ xs′ → [ x′ ∷ xs′ ]) (λ xs ys p → {!!}) (trav xs)) {!!} x
