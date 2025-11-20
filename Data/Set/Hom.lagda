\begin{code}
open import Prelude
open import Algebra

module Data.Set.Hom {ℓ} {𝑆 : Type ℓ} (latt : Semilattice 𝑆) (sIsSet : isSet 𝑆) where


open import Data.Set.Definition
open import Data.Set.Eliminators renaming (⟦_⟧ to ψ⟦_⟧)


open Semilattice latt

module _ {A : Type a} where
\end{code}
%<*hom-ty>
\begin{code}
  ⟦_⟧ : (A → 𝑆) → 𝒦 A → 𝑆
\end{code}
%</hom-ty>
\begin{code}
  ⟦ h ⟧ = ψ⟦ alg ⟧
    where
    alg : ψ A 𝑆
    alg .fst ∅ = ε
    alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = h x ∙ P⟨xs⟩
    alg .snd .c-trunc _ = sIsSet
    alg .snd .c-com x y _ xs = sym (assoc (h x) _ _) ; cong (_∙ xs) (comm (h x) _) ; assoc (h y) _ _
    alg .snd .c-dup x _ xs = sym (assoc (h x) _ _) ; cong (_∙ xs) (idem (h x))
\end{code}
