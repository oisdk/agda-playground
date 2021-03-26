{-# OPTIONS --cubical --safe #-}

module Data.Row where

open import Prelude
open import Data.Nat.Properties using (snotz)

infixr 5 _∷_
data Row (A : Type a) : Type a where
  [] : Row A
  _∷_ : A → Row A → Row A
  swap : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs

infixr 2 ψ
record ψ {a p} (A : Type a) (P : Row A → Type p) : Type (a ℓ⊔ p) where
  constructor elim
  field
    [_]_∷_⟨_⟩ : (x : A) → (xs : Row A) → (P⟨xs⟩ : P xs) → P (x ∷ xs)
    [_][] : P []
  private _∷_⟨_⟩ = [_]_∷_⟨_⟩
  field
    [_]-swap :
      ∀ x y xs (pxs : P xs) →
      PathP (λ i → P (swap x y xs i)) (x ∷ (y ∷ xs) ⟨ y ∷ xs ⟨ pxs ⟩ ⟩) (y ∷ (x ∷ xs) ⟨ x ∷ xs ⟨ pxs ⟩ ⟩)

  [_] : ∀ xs → P xs
  [ [] ] = [_][]
  [ x ∷ xs ] = [_]_∷_⟨_⟩ x xs [ xs ]
  [ swap x y xs i ] = [_]-swap x y xs [ xs ] i

syntax ψ ty (λ v → e) = ψ[ v ⦂ ty ] e
open ψ

foldr : (f : A → B → B) (n : B)
        (p : ∀ x y xs → f x (f y xs) ≡ f y (f x xs)) →
        Row A → B
foldr f n p = [ elim (λ x _ xs → f x xs) n (λ x y _ → p x y) ]

length : Row A → ℕ
length = foldr (const suc) zero λ _ _ _ → refl

infixr 5 _∈_ _∉_
_∈_ : A → Row A → Type _
x ∈ xs = ∃[ ys ] (x ∷ ys ≡ xs)

_∉_ : A → Row A → Type _
x ∉ xs = ¬ (x ∈ xs)



-- module _ (_≟_ : Discrete A) where
--   member : A → ψ[ xs ⦂ A ] Bool
--   [ member x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ = does (x ≟ y) or P⟨xs⟩
--   [ member x ][] = false
--   [ member x ]-swap y z xs pxs with does (x ≟ y) | does (x ≟ z)
--   [ member x ]-swap y z xs pxs | false | xz    = refl
--   [ member x ]-swap y z xs pxs | true  | false = refl
--   [ member x ]-swap y z xs pxs | true  | true  = refl

--   member-conv : (x : A) → ψ[ xs ⦂ A ] (T ([ member x ] xs) → x ∈ xs)
--   [ member-conv x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ m with x ≟ y
--   [ member-conv x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ m | yes p = xs , cong (_∷ xs) p
--   [ member-conv x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ m | no ¬p = let ys , x∈ys = P⟨xs⟩ m in y ∷ ys , (swap x y ys ; cong (y ∷_) x∈ys)
--   [ member-conv x ][] ()
--   [ member-conv x ]-swap = {!!}

--   member-inv : (x : A) → ψ[ xs ⦂ A ] (x ∈ xs → T ([ member x ] xs))
--   [ member-inv x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ x∈xs with x ≟ y
--   [ member-inv x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ x∈xs | yes p = tt
--   [ member-inv x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ (ys , x∈xs) | no ¬p = P⟨xs⟩ {!!}
--   [ member-inv x ][] x∈xs = snotz (cong length (snd x∈xs))
--   [ member-inv x ]-swap = {!!}

--   -- ∈?-alg : (x : A) → ψ[ xs ⦂ A ] Dec (x ∈ xs)
--   -- [ ∈?-alg x ] y ∷ xs ⟨ P⟨xs⟩ ⟩ =
--   --   ∣ x ≟ y
--   --     ∣yes x≡y ⇒ yes (xs , cong (_∷ xs) x≡y)
--   --     ∣no  x≢y ⇒ ∣ P⟨xs⟩
--   --       ∣yes (ys , x≡y) ⇒ yes (y ∷ ys , swap x y ys ; cong (y ∷_) x≡y)
--   --       ∣no  x∉xs ⇒ no (∉-cons x y xs x≢y x∉xs)
--   -- [ ∈?-alg x ][] = no (snotz ∘ cong length ∘ snd)
--   -- [ ∈?-alg x ]-swap = {!!}

--   -- _∈?_ : (x : A) → (xs : Row A) → Dec (x ∈ xs)
--   -- x ∈? [] = 
--   -- x ∈? (y ∷ xs) = {!!}
--   -- x ∈? swap y z xs i = {!!}
