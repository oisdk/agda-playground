\begin{code}
module Data.Set.TreeDefinition where

open import Prelude


data 𝒦 (A : Type a) : Type a where
\end{code}
%<*constructors>
\begin{code}
  ∅ : 𝒦 A

  ⟅_⟆ : A → 𝒦 A

  _∪_ : 𝒦 A → 𝒦 A → 𝒦 A
\end{code}
%</constructors>
%<*quotients>
\begin{code}
  assoc   : ∀ x y z   → (x ∪  y)  ∪ z  ≡ x ∪ (y ∪ z)
  com     : ∀ x y     →       x   ∪ y  ≡ y ∪ x

  ident  : ∀ x → ∅  ∪ x ≡ x
  idem   : ∀ x → x   ∪ x ≡ x
\end{code}
%</quotients>
