{-# OPTIONS --cubical --safe #-}

module Data.Dyck where

open import Prelude
open import Data.Vec
open import Data.List
open import Data.Nat using (_+_)
open import Path.Reasoning

private
  variable
    n m k : ℕ

infixr 5 ⟨_ ⟩_
data Dyck : ℕ → ℕ → Type₀ where
  done : Dyck 0 0
  ⟨_ : Dyck (suc n) m → Dyck n (suc m)
  ⟩_ : Dyck n m → Dyck (suc n) m

Bal : ℕ → Type₀
Bal = Dyck 0

support-dyck : ∀ n m → List (Dyck n m)
support-dyck = λ n m → sup-k n m id []
  module ListDyck where
  Diff : Type₀ → Type₁
  Diff A = ∀ {B : Type₀} → (A → B) → List B → List B

  mutual
    sup-k : ∀ n m → Diff (Dyck n m)
    sup-k n m k = end n m k ∘ lefts n m k ∘ rights n m k

    lefts : ∀ n m → Diff (Dyck n m)
    lefts n zero    k = id
    lefts n (suc m) k = sup-k (suc n) m (k ∘ ⟨_)

    rights : ∀ n m → Diff (Dyck n m)
    rights (suc n) m k = sup-k n m (k ∘ ⟩_)
    rights zero    m k = id

    end : ∀ n m → Diff (Dyck n m)
    end (suc _) _    k = id
    end zero (suc _) k = id
    end zero zero    k xs = k done ∷ xs

module _ {p} (P : ℕ → ℕ → Type p)
             (lbrack : ∀ {n m} → P (suc n) m → P n (suc m))
             (rbrack : ∀ {n m} → P n m → P (suc n) m)
             (base : P 0 0)
             where
  foldrDyck : Dyck n m → P n m
  foldrDyck done = base
  foldrDyck (⟨ x) = lbrack (foldrDyck x)
  foldrDyck (⟩ x) = rbrack (foldrDyck x)

data Tree : Type₀ where
  leaf : Tree
  _*_ : Tree → Tree → Tree

sz : Tree → ℕ → ℕ
sz leaf     = id
sz (xs * ys) = suc ∘ sz xs ∘ sz ys

size : Tree → ℕ
size t = sz t 0

toDyck′ : (t : Tree) → Dyck n m → Dyck n (sz t m)
toDyck′ leaf      d = d
toDyck′ (xs * ys) d = ⟨ toDyck′ xs (⟩ toDyck′ ys d)

toDyck : (t : Tree) → Dyck 0 (size t)
toDyck t = toDyck′ t done

tlbrack : Vec Tree (suc (suc n)) → Vec Tree (suc n)
tlbrack (x ∷ y ∷ xs) = (x * y) ∷ xs

trbrack : Vec Tree n → Vec Tree (suc n)
trbrack xs = leaf ∷ xs

fromDyck′ : Vec Tree (suc k) → Dyck n m → Vec Tree (suc n + k)
fromDyck′ {k = k} xs = foldrDyck (λ n m → Vec Tree (suc n + k)) tlbrack trbrack xs

fromDyck″ : Dyck 0 n → Vec Tree 1
fromDyck″ d = fromDyck′ {k = 0} (leaf ∷ []) d

fromDyck : Dyck 0 n → Tree
fromDyck d = head (fromDyck″ d)

from∘to′ : ∀ (xs : Vec Tree (k)) (d : Dyck n m) t → fromDyck′ (leaf ∷ xs) (toDyck′ t (⟩ d)) ≡ (t ∷ fromDyck′ (leaf ∷ xs) d)
from∘to′ xs d leaf = refl
from∘to′ xs d (ls * rs) =
  fromDyck′ (leaf ∷ xs) (⟨ toDyck′ ls (⟩ toDyck′ rs (⟩ d))) ≡⟨⟩
  tlbrack (fromDyck′ (leaf ∷ xs) (toDyck′ ls (⟩ toDyck′ rs (⟩ d)))) ≡⟨ cong tlbrack (from∘to′ xs (toDyck′ rs (⟩ d)) ls) ⟩
  tlbrack (ls ∷ fromDyck′ (leaf ∷ xs) (toDyck′ rs (⟩ d))) ≡⟨ cong tlbrack (cong (ls ∷_) (from∘to′ xs d rs)) ⟩
  tlbrack (ls ∷ rs ∷ fromDyck′ (leaf ∷ xs) d) ≡⟨⟩
  (ls * rs) ∷ fromDyck′ (leaf ∷ xs) d ∎

from∘to″ : ∀ t → fromDyck″ (toDyck t) ≡ t ∷ []
from∘to″ leaf      = refl
from∘to″ (ls * rs) =
  fromDyck″ (toDyck (ls * rs)) ≡⟨⟩
  tlbrack (fromDyck′ (leaf ∷ []) (toDyck′ ls (⟩ toDyck rs))) ≡⟨ cong ( tlbrack) (from∘to′ [] (toDyck rs) ls ) ⟩
  tlbrack (ls ∷ fromDyck′ (leaf ∷ []) (toDyck rs)) ≡⟨ cong tlbrack (cong (ls ∷_) (from∘to″ rs)) ⟩
  (ls * rs) ∷ [] ∎

from∘to : ∀ t → fromDyck (toDyck t) ≡ t
from∘to t = cong head (from∘to″ t)

-- sz′ : Tree → ℕ → ℕ
-- sz′ t n = suc (sz t n)


-- size-proof′ : (v : Vec Tree (suc k)) → (d : Dyck n m) → Data.Vec.foldr sz′ n (fromDyck′ v d) ≡ Data.Vec.foldr sz′ m v
-- size-proof′ v done = refl
-- size-proof′ v (⟨ d) = {!refl!} ; size-proof′ v d ; {!!} 
-- size-proof′ v (⟩ d) = {!refl!} ; size-proof′ v d  

-- size-proof : (d : Dyck 0 n) → size (fromDyck d) ≡ n
-- size-proof d = {!!}


-- to∘from : (t : Dyck 0 n) → PathP (λ i → Dyck 0 (size-proof t i)) (toDyck (fromDyck t)) t
-- to∘from = {!!}
