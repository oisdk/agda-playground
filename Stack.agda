module Stack where

open import Data.List
open import Prelude
import Data.Unit.UniversePolymorphic as Poly

Max-ℓ : List Level → Level
Max-ℓ = foldr _ℓ⊔_ ℓzero

Types : (ℓs : List Level) → Type (ℓsuc (Max-ℓ ℓs))
Types []       = Poly.⊤
Types (ℓ ∷ ℓs) = Type ℓ × Types ℓs

private variable ℓs : List Level

Stack : (ts : Types ℓs) → Type (Max-ℓ ℓs)
Stack {[]}    ts        = Poly.⊤
Stack {ℓ ∷ ℓs} (t , ts)  = t × Stack ts

_++ₜ_ : {xs ys : List Level} → Types xs → Types ys → Types (xs ++ ys)
_++ₜ_ {[]} {ys} txs tys = tys
_++ₜ_ {x ∷ xs} {ys} (t , txs) tys = t , (txs ++ₜ tys)

_↦_ : {xs ys : List Level} → Types xs → Types ys → Typeω
xs ↦ ys = ∀ {ℓs} → ∀ {zs : Types ℓs} → Stack (xs ++ₜ zs) → Stack (ys ++ₜ zs)

dup : (A , Poly.tt) ↦ (A , A , Poly.tt)
dup (x , xs) = x , x , xs

-- q : ∀ {ℓs₁ ℓs₂} {xs : Types ℓs₁} {ys : Types ℓs₂} → (xs ↦ ys) → Poly.tt ↦ ((xs ↦ ys) , Poly.tt)
-- q = {!!}

