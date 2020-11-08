{-# OPTIONS --cubical --safe --postfix-projections #-}

module Categories.Exercises where

open import Prelude
open import Categories

open Category ⦃ ... ⦄
open import Categories.Product
open Product public
open HasProducts ⦃ ... ⦄ public

-- module _ {ℓ₁} {ℓ₂} ⦃ c : Category ℓ₁ ℓ₂ ⦄ ⦃ hp : HasProducts c ⦄ where
--   ex17 : (t : Terminal) (x : Ob) → Product.obj (product (fst t) x) ≅ x
--   ex17 t x .fst = proj₂ (product (fst t) x)
--   ex17 t x .snd .fst = ump (product (fst t) x) (t .snd .fst) Id .fst
--   ex17 t x .snd .snd .fst = let p = ump (product (fst t) x) (t .snd .fst) Id .snd .snd ({!!} , {!!}) in {!!}
--   ex17 t x .snd .snd .snd = {!!}
