\begin{code}
module Data.Set.Definition where

open import Prelude
open import HLevels

infixr 5 _∷_
data 𝒦 (A : Type a) : Type a
\end{code}
%<*points>
\begin{code}
data 𝒦 A where
  ∅ : 𝒦 A
  _∷_ : A → 𝒦 A → 𝒦 A
\end{code}
%</points>
%<*quot1>
\begin{code}
  com : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
\end{code}
%</quot1>
%<*quot2>
\begin{code}
  dup : ∀ x xs → x ∷ x ∷ xs ≡ x ∷ xs
\end{code}
%</quot2>
%<*trunc>
\begin{code}
  trunc : isSet (𝒦 A)
\end{code}
%</trunc>
