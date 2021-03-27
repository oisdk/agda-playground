{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Data.Row where

open import Prelude
open import Data.Nat.Properties using (snotz)
open import Data.Bool.Properties using (isPropT)

infixr 5 _∷_
data Row (A : Type a) : Type a where
  [] : Row A
  _∷_ : A → Row A → Row A
  swap : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs

record Alg {a p} (A : Type a) (P : Row A → Type p) : Type (a ℓ⊔ p) where
  constructor algebra
  field
    [_]_∷_⟨_⟩ : (x : A) → (xs : Row A) → (P⟨xs⟩ : P xs) → P (x ∷ xs)
    [_][] : P []
  private _∷_⟨_⟩ = [_]_∷_⟨_⟩

  Swap-Coh : Type _
  Swap-Coh =
      ∀ x y xs (P⟨xs⟩ : P xs) →
      PathP (λ i → P (swap x y xs i)) (x ∷ (y ∷ xs) ⟨ y ∷ xs ⟨ P⟨xs⟩ ⟩ ⟩) (y ∷ (x ∷ xs) ⟨ x ∷ xs ⟨ P⟨xs⟩ ⟩ ⟩)
open Alg

infixr 2 ψ
record ψ {a p} (A : Type a) (P : Row A → Type p) : Type (a ℓ⊔ p) where
  constructor elim
  field
    alg : Alg A P
  field
    swap-coh : Swap-Coh alg

  [_] : ∀ xs → P xs
  [ [] ] = [ alg ][]
  [ x ∷ xs ] = [ alg ] x ∷ xs ⟨ [ xs ] ⟩
  [ swap x y xs i ] = swap-coh x y xs [ xs ] i

syntax ψ ty (λ v → e) = ψ[ v ⦂ ty ] e
open ψ


record ψ-prop {a p} (A : Type a) (P : Row A → Type p) : Type (a ℓ⊔ p) where
  constructor elim-prop
  field
    p-alg : Alg A P
    is-prop : ∀ xs → isProp (P xs)

  prop-swap-coh : Swap-Coh p-alg
  prop-swap-coh x y xs P⟨xs⟩ = toPathP (is-prop _ (transp (λ i → P (swap x y xs i)) i0 _) _)

  to-elim : ψ A P
  to-elim = elim p-alg prop-swap-coh

  ∥_∥⇓ : ∀ xs → P xs
  ∥_∥⇓ = [ to-elim ]



syntax ψ-prop ty (λ v → e) = ψ[ v ⦂ ty ]∥ e ∥
open ψ-prop


foldr : (f : A → B → B) (n : B)
        (p : ∀ x y xs → f x (f y xs) ≡ f y (f x xs)) →
        Row A → B
foldr f n p = [ elim (algebra (λ x _ xs → f x xs) n) (λ x y _ → p x y) ]

length : Row A → ℕ
length = foldr (const suc) zero λ _ _ _ → refl

infixr 5 _∈_ _∉_
_∈_ : A → Row A → Type _
x ∈ xs = ∃[ ys ] (x ∷ ys ≡ xs)

_∉_ : A → Row A → Type _
x ∉ xs = ¬ (x ∈ xs)

-- ∈-prop : ∀ (x : A) xs → isProp (x ∈ xs)
-- ∈-prop x xs x∈xs₁ x∈xs₂ = {!!}

union-alg : (ys : Row A) → ψ[ xs ⦂ A ] Row A
[ union-alg ys .alg ] x ∷ xs ⟨ P⟨xs⟩ ⟩ = x ∷ P⟨xs⟩
[ union-alg ys .alg ][] = ys
union-alg ys .swap-coh x y xs pxs = swap x y pxs

_∪_ : Row A → Row A → Row A
xs ∪ ys = [ union-alg ys ] xs

module _ (_≟_ : Discrete A) where
  _⁻ : A → ψ[ xs ⦂ A ] Row A
  [ (x ⁻) .alg ] y ∷ xs ⟨ P⟨xs⟩ ⟩ = if does (x ≟ y) then xs else y ∷ P⟨xs⟩
  [ (x ⁻) .alg ][] = []
  (x ⁻) .swap-coh y z xs pxs with x ≟ y | x ≟ z
  (x ⁻) .swap-coh y z xs pxs | no _    | no _  = swap y z pxs
  (x ⁻) .swap-coh y z xs pxs | no _    | yes _ = refl
  (x ⁻) .swap-coh y z xs pxs | yes _   | no _  = refl
  (x ⁻) .swap-coh y z xs pxs | yes x≡y | yes x≡z = cong (_∷ xs) (sym x≡z ; x≡y)

  rem-cons : ∀ x xs → [ x ⁻ ] (x ∷ xs) ≡ xs
  rem-cons x xs with x ≟ x
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  rem-swap : ∀ x y xs → x ≢ y → x ∷ [ y ⁻ ] xs ≡ [ y ⁻ ] (x ∷ xs)
  rem-swap x y xs x≢y with y ≟ x
  rem-swap x y xs x≢y | yes x≡y = ⊥-elim (x≢y (sym x≡y))
  rem-swap x y xs x≢y | no  _   = refl

  ∷-inj : ∀ x xs ys → x ∷ xs ≡ x ∷ ys → xs ≡ ys
  ∷-inj x xs ys p with x ≟ x | cong [ x ⁻ ] p
  ∷-inj x xs ys p | yes _ | q = q
  ∷-inj x xs ys p | no ¬p | q = ⊥-elim (¬p refl)


  member : A → ψ[ xs ⦂ A ] Bool
  [ member x .alg ] y ∷ xs ⟨ P⟨xs⟩ ⟩ = does (x ≟ y) or P⟨xs⟩
  [ member x .alg ][] = false
  member x .swap-coh y z xs pxs with does (x ≟ y) | does (x ≟ z)
  member x .swap-coh y z xs pxs | false | xz    = refl
  member x .swap-coh y z xs pxs | true  | false = refl
  member x .swap-coh y z xs pxs | true  | true  = refl

  member-conv-alg : (x : A) → Alg A (λ xs → T ([ member x ] xs) → x ∈ xs)
  [ member-conv-alg x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ m with x ≟ y
  [ member-conv-alg x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ m | yes p = xs , cong (_∷ xs) p
  [ member-conv-alg x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ m | no ¬p = let ys , x∈ys = P⟨xs⟩ m in y ∷ ys , (swap x y ys ; cong (y ∷_) x∈ys)
  [ member-conv-alg x ][] ()

  member-conv-coh : (x : A) → Swap-Coh (member-conv-alg x)
  member-conv-coh x y z xs P⟨xs⟩ = {!!}

  member-inv-alg : (x : A) → Alg A (λ xs → x ∈ xs → T ([ member x ] xs))
  [ member-inv-alg x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ x∈xs with x ≟ y
  [ member-inv-alg x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ x∈xs | yes x≡y = tt
  [ member-inv-alg x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ (ys , x∷ys≡y∷xs) | no x≢y = P⟨xs⟩ ([ y ⁻ ] ys , rem-swap x y ys x≢y ; cong [ y ⁻ ] x∷ys≡y∷xs ; rem-cons y xs)
  [ member-inv-alg x ][] x∈xs = snotz (cong length (snd x∈xs))

  member-inv : (x : A) → ψ[ xs ⦂ A ]∥ (x ∈ xs → T ([ member x ] xs)) ∥
  member-inv x .p-alg = member-inv-alg x
  member-inv x .is-prop xs f g = funExt λ x∈xs → isPropT ([ member x ] xs) (f x∈xs) (g x∈xs)


-- --   -- ∈?-alg : (x : A) → ψ[ xs ⦂ A ] Dec (x ∈ xs)
-- --   -- [ ∈?-alg x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ =
-- --   --   ∣ x ≟ y
-- --   --     ∣yes x≡y ⇒ yes (xs , cong (_∷ xs) x≡y)
-- --   --     ∣no  x≢y ⇒ ∣ P⟨xs⟩
-- --   --       ∣yes (ys , x≡y) ⇒ yes (y ∷ ys , swap x y ys ; cong (y ∷_) x≡y)
-- --   --       ∣no  x∉xs ⇒ no (∉-cons x y xs x≢y x∉xs)
-- --   -- [ ∈?-alg x ][] = no (snotz ∘ cong length ∘ snd)
-- --   -- [ ∈?-alg x ]-swap = {!!}

-- --   -- _∈?_ : (x : A) → (xs : Row A) → Dec (x ∈ xs)
-- --   -- x ∈? [] = 
-- --   -- x ∈? (y ∷ xs) = {!!}
-- --   -- x ∈? swap y z xs i = {!!}
