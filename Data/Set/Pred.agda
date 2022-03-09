module Data.Set.Pred where

open import Prelude
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar

memb-com-to : ∀ (x y x◇ys : Type a) → ∥ x ⊎ ∥ y ⊎ x◇ys ∥ ∥ → ∥ y ⊎ ∥ x ⊎ x◇ys ∥ ∥
memb-com-to x y x◇ys t = t >>= (either′ (∣_∣ ∘ inr ∘ ∣_∣ ∘ inl) (_∥$∥_ (mapʳ (∣_∣ ∘ inr))) )

memb-com : ∀ (x y x◇ys : Type a) → ∥ x ⊎ ∥ y ⊎ x◇ys ∥ ∥ ⇔ ∥ y ⊎ ∥ x ⊎ x◇ys ∥ ∥
memb-com x y x◇ys .fun = memb-com-to x y x◇ys
memb-com x y x◇ys .inv = memb-com-to y x x◇ys
memb-com x y x◇ys .rightInv _ = squash _ _
memb-com x y x◇ys .leftInv _ = squash _ _

memb-dup-to : ∀ (x x◇ys : Type a) → ∥ x ⊎ ∥ x ⊎ x◇ys ∥ ∥ → ∥ x ⊎ x◇ys ∥
memb-dup-to x x◇ys t = t >>= either (∣_∣ ∘ inl) id

memb-dup : ∀ (x x◇ys : Type a) → ∥ x ⊎ ∥ x ⊎ x◇ys ∥ ∥ ⇔ ∥ x ⊎ x◇ys ∥
memb-dup x x◇ys .fun = memb-dup-to x x◇ys
memb-dup x x◇ys .inv = ∣_∣ ∘ inr
memb-dup x x◇ys .rightInv _ = squash _ _
memb-dup x x◇ys .leftInv _ = squash _ _
