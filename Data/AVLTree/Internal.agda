{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Relation.Binary

module Data.AVLTree.Internal {k} {K : Type k} {r₁ r₂} (totalOrder : TotalOrder K r₁ r₂) where

open import Relation.Binary.Construct.Bounded totalOrder
open import Data.Nat using (_+_)
open TotalOrder totalOrder using (_<?_; compare)
open TotalOrder b-ord using (<-trans) renaming (refl to <-refl)
import Data.Empty.UniversePolymorphic as Poly

private
  variable
    n m l : ℕ

data Bal : ℕ → ℕ → ℕ → Type where
  ll : Bal (suc n) n (suc n)
  ee : Bal n n n
  rr : Bal n (suc n) (suc n)

balr : Bal n m l → Bal l n l
balr ll = ee
balr ee = ee
balr rr = ll

ball : Bal n m l → Bal m l l
ball ll = rr
ball ee = ee
ball rr = ee

private
  variable
    v : Level
    Val : K → Type v

data Tree {v} (Val : K → Type v) (lb ub : [∙]) : ℕ → Type (k ℓ⊔ r₁ ℓ⊔ v) where
  leaf : (lb<ub : lb [<] ub) →
         Tree Val lb ub zero
  node : (key : K)
         (val : Val key)
         (bal : Bal n m l)
         (lchild : Tree Val lb [ key ] n)
         (rchild : Tree Val [ key ] ub m) →
         Tree Val lb ub (suc l)

private
  variable
    lb ub : [∙]

data Inc {t} (T : ℕ → Type t) (n : ℕ) : Type t where
  stay : T n       → Inc T n
  high : T (suc n) → Inc T n

private
  variable
    t : Level
    N : ℕ → Type t

rotʳ : (x : K) →
       (xv : Val x) →
       (ls : Tree Val lb [ x ] (2 + n)) →
       (rs : Tree Val [ x ] ub n) →
       Inc (Tree Val lb ub) (2 + n)
rotʳ y yv (node x xv ll xl xr) zs = stay (node x xv ee xl (node y yv ee xr zs))
rotʳ y yv (node x xv ee xl xr) zs = high (node x xv rr xl (node y yv ll xr zs))
rotʳ z zv (node x xv rr xl (node y yv bl yl yr)) zr = stay (node y yv ee (node x xv (balr bl) xl yl) (node z zv (ball bl) yr zr))

rotˡ : (x : K) → (xv : Val x) →
       (ls : Tree Val lb [ x ] n) →
       (rs : Tree Val [ x ] ub (2 + n)) →
       Inc (Tree Val lb ub) (2 + n)
rotˡ x xv xl (node y yv ee yl yr) = high (node y yv ll (node x xv rr xl yl) yr)
rotˡ x xv xl (node y yv rr yl yr) = stay (node y yv ee (node x xv ee xl yl) yr)
rotˡ x xv xl (node z zv ll (node y yv bl yl yr) zr) = stay (node y yv ee (node x xv (balr bl) xl yl) (node z zv (ball bl) yr zr))

insertWith : (x : K) → Val x →
             ((new : Val x) → (old : Val x) → Val x) →
             (lb [<] [ x ]) →
             ([ x ] [<] ub) →
             (tr : Tree Val lb ub n) →
             Inc (Tree Val lb ub) n
insertWith x xv xf lb<x x<ub (leaf lb<ub) =
  high (node x xv ee (leaf lb<x) (leaf x<ub))
insertWith x xv xf lb<x x<ub (node y yv bal ls rs) with compare x y
... | lt x<y with insertWith x xv xf lb<x x<y ls
... | stay ls′ = stay (node y yv bal ls′ rs)
... | high ls′ with bal
... | ll = rotʳ y yv ls′ rs
... | ee = high (node y yv ll ls′ rs)
... | rr = stay (node y yv ee ls′ rs)
insertWith x xv xf lb<x x<ub (node y yv bal ls rs)
    | gt y<x with insertWith x xv xf y<x x<ub rs
... | stay rs′ = stay (node y yv bal ls rs′)
... | high rs′ with bal
... | ll = stay (node y yv ee ls rs′)
... | ee = high (node y yv rr ls rs′)
... | rr = rotˡ y yv ls rs′
insertWith x xv xf lb<x x<ub (node y yv bal ls rs)
    | eq x≡y = stay (node y (subst _ x≡y (xf xv (subst _ (sym x≡y) yv))) bal ls rs)

lookup : (x : K) → Tree  Val lb ub n → Maybe (Val x)
lookup x (leaf lb<ub) = nothing
lookup x (node y val bal lhs rhs) with compare y x
... | lt x<y = lookup x lhs
... | eq x≡y = just (subst _ x≡y val)
... | gt x>y = lookup x rhs

record Cons (Val : K → Type v) (lb ub : [∙]) (h : ℕ) : Type (k ℓ⊔ v ℓ⊔ r₁) where
  constructor cons
  field
    head : K
    val  : Val head
    bounds : lb [<] [ head ]
    tail : Inc (Tree Val [ head ] ub) h
open Cons public

map-tail : ∀ {ub₁ ub₂} →
             Cons Val lb ub₁ n →
             (∀ {lb} → Inc (Tree Val lb ub₁) n → Inc (Tree Val lb ub₂) m) →
             Cons Val lb ub₂ m
map-tail (cons h v b t) f = cons h v b (f t)

uncons : (x : K) →
         Val x →
         Bal n m l →
         Tree Val lb [ x ] n →
         Tree Val [ x ] ub m →
         Cons Val lb ub l
uncons x xv bl (leaf lb<ub) rhs .head = x
uncons x xv bl (leaf lb<ub) rhs .val = xv
uncons x xv bl (leaf lb<ub) rhs .bounds = lb<ub
uncons x xv ee (leaf lb<ub) rhs .tail = stay rhs
uncons x xv rr (leaf lb<ub) rhs .tail = stay rhs
uncons x xv bl (node y yv yb ls yrs) rs =
  map-tail (uncons y yv yb ls yrs)
    λ { (high ys) → high (node x xv bl ys rs)
      ; (stay ys) → case bl of
        λ { ll → stay (node x xv ee ys rs)
          ; ee → high (node x xv rr ys rs)
          ; rr → rotˡ x xv ys rs
          }
      }

ext : ∀ {ub′} → ub [<] ub′ → Tree Val lb ub n → Tree Val lb ub′ n
ext {lb = lb} ub<ub′ (leaf lb<ub) = leaf (<-trans {x = lb} lb<ub ub<ub′)
ext ub<ub′ (node x xv bal lhs rhs) = node x xv bal lhs (ext ub<ub′ rhs)

join : ∀ {x} →
       Tree Val lb [ x ] m →
       Bal m n l →
       Tree Val [ x ] ub n →
       Inc (Tree Val lb ub) l
join lhs ll (leaf lb<ub) = stay (ext lb<ub lhs)
join {lb = lb} (leaf lb<ub₁) ee (leaf lb<ub) = stay (leaf (<-trans {x = lb} lb<ub₁ lb<ub))
join lhs bl (node x xv xb xl xr) with uncons x xv xb xl xr
... | cons k′ v′ l<u (high tr′) = high (node k′ v′ bl (ext l<u lhs) tr′)
... | cons k′ v′ l<u (stay tr′) with bl
... | ll = rotʳ k′ v′ (ext l<u lhs) tr′
... | ee = high (node k′ v′ ll (ext l<u lhs) tr′)
... | rr = stay (node k′ v′ ee (ext l<u lhs) tr′)

data Decr {t} (T : ℕ → Type t) : ℕ → Type t where
  same : T n → Decr T n
  decr : T n → Decr T (suc n)

inc→dec : Inc N n → Decr N (suc n)
inc→dec (stay x) = decr x
inc→dec (high x) = same x

delete : (x : K)
        → Tree Val lb ub n
        → Decr (Tree Val lb ub) n
delete x (leaf l<u) = same (leaf l<u)
delete x (node y yv b l r) with compare x y
delete x (node y yv b l r) | eq _ = inc→dec (join l b r)
delete x (node y yv b l r) | lt a with delete x l
... | same l′ = same (node y yv b l′ r)
... | decr l′ with b
... | ll = decr (node y yv ee l′ r)
... | ee = same (node y yv rr l′ r)
... | rr = inc→dec (rotˡ y yv l′ r)
delete x (node y yv b l r) | gt c with delete x r
... | same r′ = same (node y yv b l r′)
... | decr r′ with b
... | ll = inc→dec (rotʳ y yv l r′)
... | ee =  same (node y yv ll  l r′)
... | rr =  decr (node y yv ee  l r′)

data Change {t} (T : ℕ → Type t) : ℕ → Type t where
  up : T (suc n) → Change T n
  ev : T n → Change T n
  dn : T n → Change T (suc n)

inc→changeup : Inc N n → Change N (suc n)
inc→changeup (stay x) = dn x
inc→changeup (high x) = ev x

inc→changedn : Inc N n → Change N n
inc→changedn (stay x) = ev x
inc→changedn (high x) = up x

_<_<_ : [∙] → K → [∙] → Type _
l < x < u = l [<] [ x ] × [ x ] [<] u

alter : (x : K)
      → (Maybe (Val x) → Maybe (Val x))
      → Tree Val lb ub n
      → lb < x < ub
      → Change (Tree Val lb ub) n
alter x f (leaf l<u) (l , u) with f nothing
...  | just xv = up (node x xv ee (leaf l) (leaf u))
...  | nothing = ev (leaf l<u)
alter x f (node y yv b tl tr) (l , u) with compare x y
alter x f (node y yv b tl tr) (l , u)
     | eq x≡y with f (just (subst _ (sym x≡y) yv))
...  | just xv = ev (node y (subst _ x≡y xv) b tl tr)
...  | nothing = inc→changeup (join tl b tr)
alter x f (node y yv b tl tr) (l , u)
      | lt a with alter x f tl (l , a) | b
...  | ev tl′ | _  = ev (node y yv b  tl′ tr)
...  | up tl′ | ll = inc→changedn (rotʳ y yv tl′ tr)
...  | up tl′ | ee = up (node y yv ll  tl′ tr)
...  | up tl′ | rr = ev (node y yv ee  tl′ tr)
...  | dn tl′ | ll = dn (node y yv ee  tl′ tr)
...  | dn tl′ | ee = ev (node y yv rr  tl′ tr)
...  | dn tl′ | rr = inc→changeup (rotˡ y yv tl′ tr)
alter x f (node y yv b tl tr) (l , u)
     | gt c with alter x f tr (c , u) | b
...  | ev tr′ | _  = ev (node y yv b  tl tr′)
...  | up tr′ | ll = ev (node y yv ee tl tr′)
...  | up tr′ | ee = up (node y yv rr  tl tr′)
...  | up tr′ | rr = inc→changedn (rotˡ y yv tl tr′)
...  | dn tr′ | ll = inc→changeup (rotʳ y yv tl tr′)
...  | dn tr′ | ee = ev (node y yv ll  tl tr′)
...  | dn tr′ | rr = dn (node y yv ee  tl tr′)

open import Lens

alterF : (x : K) →
         Tree Val lb ub n →
         lb < x < ub →
         LensPart (Change (Tree Val lb ub) n) (Maybe (Val x))
alterF x xs bnds = go (ev xs) x xs bnds id
  where
  go : A → (x : K) →
       Tree Val lb ub n →
       lb < x < ub →
       (Change (Tree Val lb ub) n → A) →
       LensPart A (Maybe (Val x))
  go xs x (leaf lb<ub) (l , u) k = λ where
    .get → nothing
    .set nothing → xs
    .set (just xv) → k (up (node x xv ee (leaf l) (leaf u)))
  go xs x (node y yv bl yl yr) (l , u) k with compare x y
  go xs x (node y yv bl yl yr) (l , u) k | eq x≡y = λ where
    .get → just (subst _ (sym x≡y) yv)
    .set nothing → k (inc→changeup (join yl bl yr))
    .set (just xv) → k (ev (node y (subst _ x≡y xv) bl yl yr))
  go xs x (node y yv bl yl yr) (l , u) k | lt x<y =
    go xs x yl (l , x<y)
      λ { (up yl′) → case bl of
          λ { ll → k (inc→changedn (rotʳ y yv yl′ yr))
            ; ee → k (up (node y yv ll yl′ yr))
            ; rr → k (ev (node y yv ee yl′ yr))
            }
        ; (ev yl′) → k (ev (node y yv bl yl′ yr))
        ; (dn yl′) → case bl of
          λ { rr → k (inc→changeup (rotˡ y yv yl′ yr))
            ; ee → k (ev (node y yv rr yl′ yr))
            ; ll → k (dn (node y yv ee yl′ yr))
            }
        }
  go xs x (node y yv bl yl yr) (l , u) k | gt x>y =
    go xs x yr (x>y , u)
      λ { (up yr′) → case bl of
          λ { rr → k (inc→changedn (rotˡ y yv yl yr′))
            ; ee → k (up (node y yv rr yl yr′))
            ; ll → k (ev (node y yv ee yl yr′))
            }
        ; (ev yr′) → k (ev (node y yv bl yl yr′))
        ; (dn yr′) → case bl of
          λ { ll → k (inc→changeup (rotʳ y yv yl yr′))
            ; ee → k (ev (node y yv ll yl yr′))
            ; rr → k (dn (node y yv ee yl yr′))
            }
        }

open import Data.List

toList⊙ : Tree Val lb ub n → List (∃ Val) → List (∃ Val)
toList⊙ (leaf lb<ub) ks = ks
toList⊙ (node x xv bal xl xr) ks = toList⊙ xl ((x , xv) ∷ toList⊙ xr ks)

toList : Tree Val lb ub n → List (∃ Val)
toList xs = toList⊙ xs []
