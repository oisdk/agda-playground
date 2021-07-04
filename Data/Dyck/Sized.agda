module Data.Dyck.Sized where

open import Prelude
open import Data.Nat using (_+_)
open import Data.Vec.Iterated using (Vec; _∷_; []; foldlN; head; foldl′)

private
  variable
    n m k : ℕ

private
  variable
    n⊙ m⊙ k⊙ : ℕ → ℕ

data Stack : ℕ → ℕ → Type where
  [] : Stack 1 0
  push : Stack (1 + n) m → Stack n (1 + m)
  pull : Stack (1 + n) m → Stack (2 + n) m

data Tree : Type where
  ⟨⟩ : Tree
  _*_ : Tree → Tree → Tree

size⊙ : Tree → ℕ → ℕ
size⊙ ⟨⟩ = suc
size⊙ (xs * ys) = size⊙ xs ∘ size⊙ ys

size : Tree → ℕ
size t = size⊙ t zero

tree→prog⊙ : (t : Tree) → Stack (suc m) k → Stack m (size⊙ t k)
tree→prog⊙ ⟨⟩         = push
tree→prog⊙ (xs * ys) = tree→prog⊙ xs ∘ tree→prog⊙ ys ∘ pull

tree→prog : (t : Tree) → Stack 0 (size t)
tree→prog tr = tree→prog⊙ tr []

stack→tree⊙ : Stack n m → Vec Tree n → Tree
stack→tree⊙ []        (v ∷ [])       = v
stack→tree⊙ (push is) st             = stack→tree⊙ is (⟨⟩ ∷ st)
stack→tree⊙ (pull is) (t₁ ∷ t₂ ∷ st) = stack→tree⊙ is (t₂ * t₁ ∷ st)

stack→tree : Stack 0 n → Tree
stack→tree ds = stack→tree⊙ ds []

stack→tree-size⊙ :  {st : Vec Tree n} (is : Stack n m) →
 size (stack→tree⊙ is st) ≡ foldl′ size⊙ m st
stack→tree-size⊙  []       = refl
stack→tree-size⊙ (push is) = stack→tree-size⊙ is
stack→tree-size⊙ (pull is) = stack→tree-size⊙ is
