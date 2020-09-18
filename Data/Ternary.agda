{-# OPTIONS --cubical --safe #-}

module Data.Ternary where

open import Prelude
open import Relation.Nullary.Discrete.FromBoolean

infixl 5 _,0 _,1 _,2
data Tri : Type₀ where
  0t : Tri
  _,0 _,1 _,2 : Tri → Tri

infix 4 _≡ᴮ_
_≡ᴮ_ : Tri → Tri → Bool
0t   ≡ᴮ 0t   = true
x ,0 ≡ᴮ y ,0 = x ≡ᴮ y
x ,1 ≡ᴮ y ,1 = x ≡ᴮ y
x ,2 ≡ᴮ y ,2 = x ≡ᴮ y
_    ≡ᴮ _    = false

sound : ∀ x y → T (x ≡ᴮ y) → x ≡ y
sound 0t     0t     p = refl
sound (x ,0) (y ,0) p = cong _,0 (sound x y p)
sound (x ,1) (y ,1) p = cong _,1 (sound x y p)
sound (x ,2) (y ,2) p = cong _,2 (sound x y p)

complete : ∀ x → T (x ≡ᴮ x)
complete 0t = tt
complete (x ,0) = complete x
complete (x ,1) = complete x
complete (x ,2) = complete x

_≟_ : (x y : Tri) → Dec (x ≡ y)
_≟_ = from-bool-eq _≡ᴮ_ sound complete
