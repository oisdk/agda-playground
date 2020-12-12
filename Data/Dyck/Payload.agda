{-# OPTIONS --cubical --safe --postfix-projections #-}

-- This module defines a data type for balanced strings of parentheses,
-- which is isomorphic to binary trees.

module Data.Dyck.Payload where

open import Prelude
open import Data.List using (List; _∷_; []; _++_; length)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Function.Surjective
open import Function.Injective
open import Function.Injective.Properties using (inject-contrapositive)
open import Data.Nat.Properties using (snotz; znots; pred)
open import Data.Vec.Iterated

private
  variable
    n m k : ℕ

--------------------------------------------------------------------------------
-- Binary trees: definition and associated functions.
--------------------------------------------------------------------------------

-- A basic binary tree type.
data Tree (A : Type a) : Type a where
  [_] : A → Tree A
  _*_ : Tree A → Tree A → Tree A

--------------------------------------------------------------------------------
-- Conversion between binary trees and Progs. (leftwards)
--------------------------------------------------------------------------------

data Prog {a} (A : Type a) : ℕ → Type a where
  halt : Prog A zero
  push : A → Prog A (suc n) → Prog A n
  pull : Prog A n → Prog A (suc n)

module _{p} (P : ℕ → Type p)
             (lbrack : ∀ {n} → P (suc n) → P n)
             (rbrack : ∀ {n} → A → P n → P (suc n))
             where
  foldlProg : P n → Prog A n → P zero
  foldlProg bs halt = bs
  foldlProg bs (push x xs) = foldlProg (rbrack x bs) xs
  foldlProg bs (pull   xs) = foldlProg (lbrack bs) xs
-- In terms of foldr:
-- foldlProg P lb rb bs xs = foldrProg (λ n → P n → P zero) (λ x k bs → k (rb x bs)) (λ k bs → k (lb bs)) id xs bs

reduce : Vec (Tree A) (2 + n) → Vec (Tree A) (1 + n)
reduce (t₁ ∷ t₂ ∷ s) = (t₂ * t₁) ∷ s

shift : A → Vec (Tree A) n → Vec (Tree A) (1 + n)
shift x s = [ x ] ∷ s

prog→tree⊙ : Prog A n → Vec (Tree A) (1 + n) → Vec (Tree A) 1
prog→tree⊙ p s = foldlProg (λ n → Vec (Tree _) (1 + n)) reduce shift s p

prog→tree : A × Prog A zero → Tree A
prog→tree (x , ds) = head (prog→tree⊙ ds ([ x ] ∷ []))

tree→prog⊙ : Tree A → Prog A n → A × Prog A n
tree→prog⊙ [ x ]     = x ,_
tree→prog⊙ (xs * ys) = tree→prog⊙ xs ∘ uncurry push ∘ tree→prog⊙ ys ∘ pull

tree→prog : Tree A → A × Prog A zero
tree→prog tr = tree→prog⊙ tr halt

shuttle : A × Prog A n → Vec (Tree A) m → Prog A n × Vec (Tree A) (suc m)
shuttle (x , xs) ys = xs , [ x ] ∷ ys

tree→prog→tree-assoc : (xs : Tree A) (is : Prog A (1 + n)) (st : Vec (Tree A) (1 + n)) → prog→tree⊙ (uncurry push (tree→prog⊙ xs is)) st ≡ prog→tree⊙ is (xs ∷ st)
tree→prog→tree-assoc [ x ]     is st = refl
tree→prog→tree-assoc (xs * ys) is st = tree→prog→tree-assoc xs _ st ; tree→prog→tree-assoc ys (pull is) (xs ∷ st)

tree→prog→tree-ε : (e : Tree A) (is : Prog A n) (st : Vec (Tree A) n) → uncurry prog→tree⊙ (shuttle (tree→prog⊙ e is) st) ≡ prog→tree⊙ is (e ∷ st)
tree→prog→tree-ε [ x ]     is st = refl
tree→prog→tree-ε (xs * ys) is st =
  uncurry prog→tree⊙ (shuttle (tree→prog⊙ xs (uncurry push (tree→prog⊙ ys (pull is)))) st) ≡⟨ tree→prog→tree-ε xs _ st ⟩
  prog→tree⊙  (uncurry push (tree→prog⊙ ys (pull is))) (xs ∷ st) ≡⟨ tree→prog→tree-assoc ys (pull is) (xs ∷ st) ⟩
  prog→tree⊙ is ((xs * ys) ∷ st) ∎

tree→prog→tree : (t : Tree A) → prog→tree (tree→prog t) ≡ t
tree→prog→tree t = cong head (tree→prog→tree-ε t halt [])

unreduce : Vec (Tree A) (1 + n) → Vec (Tree A) (2 + n)
unreduce ([ x ] ∷ xs) = [ x ] ∷ [ x ] ∷ xs
unreduce ((x₁ * x₂) ∷ xs) = x₂ ∷ x₁ ∷ xs

reduce-inj : {xs ys : Vec (Tree A) (2 + n)} → reduce xs ≡ reduce ys → xs ≡ ys
reduce-inj xs≡ys = cong unreduce xs≡ys

root : Tree A → A
root [ x ] = x
root (xs * _) = root xs

shift-inj : ∀ {A : Type a} {x y : A} {xs ys : Vec (Tree A) n} → shift x xs ≡ shift y ys → (x , xs) ≡ (y , ys)
shift-inj = cong λ where (z ∷ zs) → root z , zs

payload : Prog A n → List A
payload halt = []
payload (push x xs) = x ∷ payload xs
payload (pull xs) = payload xs

content⊙ : Tree A → List A → List A
content⊙ [ x ] = x ∷_
content⊙ (xs * ys) = content⊙ xs ∘ content⊙ ys

contents⊙ : Vec (Tree A) n → List A → List A
contents⊙ xs ks = foldl′ content⊙ ks xs

contents : Vec (Tree A) n → List A
contents xs = contents⊙ xs []

encode⊙ : Tree A → List (Maybe A) → List (Maybe A)
encode⊙ [ x ] = just x ∷_
encode⊙ (xs * ys) = encode⊙ xs ∘ encode⊙ ys ∘ (nothing ∷_)

encodes⊙ : Vec (Tree A) n → List (Maybe A) → List (Maybe A)
encodes⊙ = flip (foldl′ encode⊙)

encodes : Vec (Tree A) n → List (Maybe A)
encodes xs = encodes⊙ xs []

open import Data.List.Properties using (∷-inj)

tail′ : List A → List A
tail′ (_ ∷ xs) = xs
tail′ [] = []

encode⊙-inj : (ts : Tree A) → Injective (encode⊙ ts)
encode⊙-inj [ x ]       xs ys xs≡ys = ∷-inj (just x) xs ys xs≡ys
encode⊙-inj (ts₁ * ts₂) xs ys xs≡ys = cong tail′ (encode⊙-inj ts₂ (nothing ∷ xs) (nothing ∷ ys) (encode⊙-inj ts₁ (encode⊙ ts₂ (nothing ∷ xs)) (encode⊙ ts₂ (nothing ∷ ys)) xs≡ys))

encodes⊙-inj : {A : Type a} (vs : Vec (Tree A) n) → Injective (encodes⊙ vs)
encodes⊙-inj {n = zero } vs       xs ys fxs≡fys = fxs≡fys
encodes⊙-inj {n = suc n} (v ∷ vs) xs ys fxs≡fys = encode⊙-inj v xs ys (encodes⊙-inj vs (encode⊙ v xs) (encode⊙ v ys) fxs≡fys)

unind : Prog A n → List (Maybe A)
unind halt        = []
unind (push x xs) = just x  ∷ unind xs
unind (pull   xs) = nothing ∷ unind xs

unind-conv : (vs : Vec (Tree A) (1 + n)) (xs : Prog A n) → encodes (prog→tree⊙ xs vs) ≡ encodes⊙ vs (unind xs)
unind-conv vs  halt       = refl
unind-conv vs (push x xs) = unind-conv (shift x vs) xs
unind-conv vs (pull   xs) = unind-conv (reduce  vs) xs

prog→tree→unind→inj : (vs : Vec (Tree A) (1 + n)) (xs ys : Prog A n) → prog→tree⊙ xs vs ≡ prog→tree⊙ ys vs → unind xs ≡ unind ys
prog→tree→unind→inj vs xs ys prf = encodes⊙-inj vs (unind xs) (unind ys) (sym (unind-conv vs xs) ; cong encodes prf ; unind-conv vs ys)

content⊙-inj : (ts : Tree A) → Injective (content⊙ ts)
content⊙-inj [ x ]       xs ys xs≡ys = ∷-inj x xs ys xs≡ys
content⊙-inj (ts₁ * ts₂) xs ys xs≡ys = content⊙-inj ts₂ xs ys (content⊙-inj ts₁ (content⊙ ts₂ xs) (content⊙ ts₂ ys) xs≡ys)


contents⊙-inj : {A : Type a} (vs : Vec (Tree A) n) → Injective (contents⊙ vs)
contents⊙-inj {n = zero}  vs       xs ys fxs≡fys = fxs≡fys
contents⊙-inj {n = suc n} (v ∷ vs) xs ys fxs≡fys = content⊙-inj v xs ys (contents⊙-inj vs (content⊙ v xs) (content⊙ v ys) fxs≡fys)

contents-conv : (vs : Vec (Tree A) (1 + n)) (xs : Prog A n) → contents (prog→tree⊙ xs vs) ≡ foldl′ content⊙ (payload xs) vs
contents-conv vs halt = refl
contents-conv vs (push x xs) = contents-conv (shift x vs) xs
contents-conv vs (pull xs)   = contents-conv (reduce  vs) xs

prog→tree→contents→inj : (vs : Vec (Tree A) (1 + n)) (xs ys : Prog A n) → prog→tree⊙ xs vs ≡ prog→tree⊙ ys vs → payload xs ≡ payload ys
prog→tree→contents→inj vs xs ys prf = contents⊙-inj vs (payload xs) (payload ys) (sym (contents-conv vs xs) ; cong contents prf ; contents-conv vs ys)

branches⊙ : Tree A → ℕ → ℕ
branches⊙ [ _ ] = id
branches⊙ (xs * ys) = branches⊙ xs ∘ branches⊙ ys ∘ suc

pulls : Prog A n → ℕ
pulls halt = zero
pulls (push x xs) = pulls xs
pulls (pull xs) = suc (pulls xs)

branchess⊙ : Vec (Tree A) n → ℕ → ℕ
branchess⊙ vs n = foldl′ branches⊙ n vs

branchess : Vec (Tree A) n → ℕ
branchess vs = branchess⊙ vs zero

branches-conv : (vs : Vec (Tree A) (1 + n)) (xs : Prog A n) → foldl′ branches⊙ zero (prog→tree⊙ xs vs) ≡ foldl′ branches⊙ (pulls xs) vs
branches-conv vs halt = refl
branches-conv vs (push x xs) = branches-conv (shift x vs) xs
branches-conv vs (pull   xs) = branches-conv (reduce  vs) xs

branches⊙-inj : (t : Tree A) → Injective (branches⊙ t)
branches⊙-inj [ x ]       xs ys xs≡ys = xs≡ys
branches⊙-inj (ts₁ * ts₂) xs ys xs≡ys = cong pred (branches⊙-inj ts₂ (suc xs) (suc ys) (branches⊙-inj ts₁ (branches⊙ ts₂ (suc xs)) (branches⊙ ts₂ (suc ys)) xs≡ys))

branchess⊙-inj : {A : Type a} (vs : Vec (Tree A) n) → Injective (branchess⊙ vs)
branchess⊙-inj {n = zero } vs       x y x≡y = x≡y
branchess⊙-inj {n = suc n} (v ∷ vs) x y x≡y = branches⊙-inj v x y (branchess⊙-inj vs (branches⊙ v x) (branches⊙ v y) x≡y)

prog→tree→branches→inj : (vs : Vec (Tree A) (1 + n)) (xs ys : Prog A n) → prog→tree⊙ xs vs ≡ prog→tree⊙ ys vs → pulls xs ≡ pulls ys
prog→tree→branches→inj vs xs ys prf = branchess⊙-inj vs (pulls xs) (pulls ys) (sym (branches-conv vs xs) ; cong branchess prf ; branches-conv vs ys)

head′ : List (Maybe A) → Maybe A
head′ [] = nothing
head′ (x ∷ _) = x

open import Data.Maybe.Properties

prog→tree⊙-inj : (vs : Vec (Tree A) (1 + n)) → (xs ys : Prog A n) → prog→tree⊙ xs vs ≡ prog→tree⊙ ys vs → xs ≡ ys
prog→tree⊙-inj vs  halt        halt       fxs≡fys = refl
prog→tree⊙-inj vs (pull xs)   (pull ys)   fxs≡fys = cong pull (prog→tree⊙-inj (reduce vs) xs ys fxs≡fys)
prog→tree⊙-inj vs (push x xs) (push y ys) fxs≡fys = cong₂ push prf (prog→tree⊙-inj (shift x vs) xs ys (fxs≡fys ; cong (λ xy → prog→tree⊙ ys ([ xy ] ∷ vs)) (sym prf)))
  where
  prf : x ≡ y
  prf = cong (λ { [] → x ; (z ∷ _) → z}) (prog→tree→contents→inj vs (push x xs) (push y ys) fxs≡fys)
prog→tree⊙-inj vs halt (push y ys) fxs≡fys = ⊥-elim (znots (cong length (prog→tree→contents→inj vs halt (push y ys) fxs≡fys)))
prog→tree⊙-inj vs (push x xs) halt fxs≡fys = ⊥-elim (snotz (cong length (prog→tree→contents→inj vs (push x xs) halt fxs≡fys)))
prog→tree⊙-inj vs (push x xs) (pull ys) fxs≡fys = ⊥-elim (just≢nothing (cong head′ (prog→tree→unind→inj vs (push x xs) (pull ys) fxs≡fys)))
prog→tree⊙-inj vs (pull xs) (push y ys) fxs≡fys = ⊥-elim (nothing≢just (cong head′ (prog→tree→unind→inj vs (pull xs) (push y ys) fxs≡fys)))


prog→tree⊙→fst→inj : (x y : A) (vs : Vec (Tree A) n) (xs ys : Prog A n) → prog→tree⊙ xs ([ x ] ∷ vs) ≡ prog→tree⊙ ys ([ y ] ∷ vs) → x ≡ y
prog→tree⊙→fst→inj x y vs xs ys fx≡fy =
  let p = unind-conv ([ x ] ∷ vs) xs
      p′ = cong encodes fx≡fy
      q = unind-conv ([ y ] ∷ vs) ys
      j = sym p ; p′ ; q
      h = cong head′ (encodes⊙-inj vs (encode⊙ [ x ] (unind xs)) (encode⊙ [ y ] (unind ys)) j)
  in just-inj h

head-zero : (xs ys : Vec A 1) → head xs ≡ head ys → xs ≡ ys
head-zero (x ∷ []) (y ∷ []) prf = cong (_∷ []) prf

prog→tree→fst→inj : (xs ys : A × Prog A zero) → prog→tree xs ≡ prog→tree ys → fst xs ≡ fst ys
prog→tree→fst→inj (x , xs) (y , ys) fx≡fy = prog→tree⊙→fst→inj x y [] xs ys (head-zero _ _ fx≡fy)


prog→tree-inj : Injective (prog→tree {A = A})
prog→tree-inj (x , xs) (y , ys) fx≡fy = let p = prog→tree→fst→inj (x , xs) (y , ys) fx≡fy in cong₂ _,_ p (prog→tree⊙-inj ([ x ] ∷ []) xs ys (head-zero (prog→tree⊙ xs ([ x ] ∷ [])) (prog→tree⊙ ys ([ y ] ∷ [])) fx≡fy ; cong (λ xy → prog→tree⊙ ys ( [ xy ] ∷ [])) (sym p)))

prog-iso : (A × Prog A zero) ⇔ Tree A
prog-iso = surj×inj⇒iso prog→tree (λ y → tree→prog y , tree→prog→tree y) prog→tree-inj
