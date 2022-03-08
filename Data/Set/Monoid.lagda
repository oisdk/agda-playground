\begin{code}
{-# OPTIONS --prop #-}

module Data.Set.Monoid where

open import Data.Set.Definition
open import Data.Set.Eliminators renaming (⟦_⟧ to ψ⟦_⟧)
open import Data.Set.Union
open import Prelude
open import Algebra

open import Data.Nat
open import Cubical.Foundations.HLevels using (isSetΠ)


module _ {a} {A : Type a} where
  setMonoid : Monoid a
  setMonoid .Monoid.𝑆 = 𝒦 A
  setMonoid .Monoid._∙_ = _∪_
  setMonoid .Monoid.ε = ∅
  setMonoid .Monoid.assoc = ∪-assoc
  setMonoid .Monoid.ε∙ _ = refl
  setMonoid .Monoid.∙ε = ∪-idʳ

  𝒦-semilattice : Semilattice a
  𝒦-semilattice .Semilattice.commutativeMonoid .CommutativeMonoid.monoid = setMonoid
  𝒦-semilattice .Semilattice.commutativeMonoid .CommutativeMonoid.comm = ∪-com
  𝒦-semilattice .Semilattice.idem = ∪-idem

GraphOf : Type a → Type a
GraphOf A = A → 𝒦 A

module SlowIds {a} {A : Type a} where
  open import Data.Set.Hom (𝒦-semilattice {A = A}) trunc

\end{code}
%<*slow-ids>
\begin{code}
  ids : GraphOf A → A → ℕ → 𝒦 A
  ids g r zero     = r ∷ ∅
  ids g r (suc n)  = ⟦ flip (ids g) n ⟧ (g r)
\end{code}
%</slow-ids>
\begin{code}

module DFS {a} {A : Type a} where
  open import Data.Set.Hom (𝒦-semilattice {A = A}) trunc

  {-# NON_TERMINATING #-}
\end{code}
%<*dfs>
\begin{code}
  dfs : GraphOf A → A → 𝒦 A
  dfs g r = r ∷ ⟦ dfs g ⟧ (g r)
\end{code}
%</dfs>
\begin{code}


module _ {a} {A : Type a} where

  open import Algebra.Construct.Cayley (setMonoid {A = A}) trunc public

  open import Algebra.Construct.LiftedLattice  (semiLattice ∪-idem ∪-com)

  -- open import Data.Set.Hom (liftedSemilattice ℕ) (isSetΠ (λ _ → isSet𝒞)) public
  open import Data.Set.Hom (semiLattice ∪-idem ∪-com)  isSet𝒞 public

𝒦⊙ : Type a → Type a
𝒦⊙ A = 𝒞 {A = A}


open import Path.Reasoning
\end{code}
%<*ids-p>
\begin{code}
ids⊙ : GraphOf A → ℕ → A → 𝒦⊙ A
ids⊙ g zero     r = ⟦ r ∷ ∅ ⇑⟧
ids⊙ g (suc n)  r = ⟦ ids⊙ g n ⟧ (g r)
\end{code}
%</ids-p>
%<*ids>
\begin{code}
ids : GraphOf A → A → ℕ → 𝒦 A
ids g r n = ⟦ ids⊙ g n r ⇓⟧
\end{code}
%</ids>

