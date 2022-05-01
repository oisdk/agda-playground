{-# OPTIONS --no-positivity-check #-}

module Data.Braun where

open import Prelude hiding (_⟨_⟩_)
open import Data.Binary hiding (_+_)
open import Data.Nat using (_+_)

record Q (A : Type a) : Type a where
  inductive
  field q : (Q A → Q A) → (Q A → Q A) → A → A
open Q

data Tree (A : Type a) : Type a where
  ⟨⟩ : Tree A
  ⟨_,_,_⟩ : (x : A) → (s : Tree A) → (t : Tree A) → Tree A


diff : Tree A → 𝔹 → Bool
diff ⟨⟩            _      = false
diff ⟨ _ , _ , _ ⟩ 0ᵇ     = true
diff ⟨ x , s , t ⟩ (1ᵇ k) = diff s k
diff ⟨ x , s , t ⟩ (2ᵇ k) = diff t k

size : Tree A → 𝔹
size ⟨⟩            = 0ᵇ
size ⟨ _ , s , t ⟩ = let m = size t in (if diff s m then 2ᵇ_ else 1ᵇ_) m

module _ {A : Type a} {B : Type b} where
  {-# TERMINATING #-}
  foldr𝔹 : (A → B → B) → B → Tree A → B
  foldr𝔹 c n t = f t r .q id id n
    where
    f : Tree A → Q B → Q B
    f ⟨⟩            xs .q ls rs b = b
    f ⟨ x , l , r ⟩ xs .q ls rs b = c x (xs .q (ls ∘ f l) (rs ∘ f r) b)

    r : Q B
    r .q ls rs = ls (rs r) .q id id

infixr 5 _◂_
record Stream (A : Type a) : Type a where
  coinductive; constructor _◂_
  field
    head : A
    tail : Stream A
open Stream public

open import Data.List

TreeBuilder : Type a → Type a
TreeBuilder A = ℕ → ℕ → Stream (Stream (Tree A)) → Stream (Stream (Tree A))

repeat : A → Stream A
repeat x .head = x
repeat x .tail = repeat x

tnil : TreeBuilder A
tnil n m xs = repeat ⟨⟩ ◂ repeat ⟨⟩ ◂ xs

{-# NON_TERMINATING #-}
tl : (Stream (Stream (Tree A)) → Stream (Stream (Tree A))) → Stream (Tree A)
tl k = head xs
  where
  xs : Stream (Stream (Tree _))
  xs = k (tail xs)

double : ℕ → ℕ
double n = n + n

2^ : ℕ → ℕ
2^ zero    = 1
2^ (suc n) = double (2^ n)

head_ : (A → A) → Stream A → Stream A
head_ f xs .head = f (xs .head)
head_ f xs .tail = xs .tail


infixl 10 _[_] _⊢_
_⊢_ : Stream A → ℕ → Stream A
xs ⊢ zero  = xs
xs ⊢ suc n = tail xs ⊢ n

_[_] : Stream A → ℕ → A
xs [ n  ] = (xs ⊢ n) .head

{-# NON_TERMINATING #-}
tcons : A → TreeBuilder A → TreeBuilder A
tcons v k zero    j xs = repeat ⟨⟩ ◂ tl (tcons v k (2^ j) (suc j)) ◂ xs
tcons v k (suc i) j xs = head_ (⟨ v , xs [ 0 ] [ 0 ] , xs [ 1 ] [ 0 ] ⟩ ◂_) (k i j ((xs [ 0 ]) .tail ◂ (xs [ 1 ]) .tail ◂ xs ⊢ 2))
