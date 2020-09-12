{-# OPTIONS --without-K --safe #-}

module Instance where

open import Level

it : ⦃ _ : A ⦄ → A
it ⦃ x ⦄ = x
