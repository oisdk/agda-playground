{-# OPTIONS --cubical --safe #-}

module Data.List.Properties where

open import Data.List
open import Prelude
open import Data.Fin
open import Strict.Properties

map-length : (f : A → B) (xs : List A)
           → length xs ≡ length (map f xs)
map-length f [] _ = zero
map-length f (x ∷ xs) i = suc (map-length f xs i)

map-ind : (f : A → B) (xs : List A)
        → PathP (λ i → Fin (map-length f xs i) → B) (f ∘ (xs !_)) (map f xs !_)
map-ind f [] i ()
map-ind f (x ∷ xs) i f0 = f x
map-ind f (x ∷ xs) i (fs n) = map-ind f xs i n

tab-length : ∀ n (f : Fin n → A) → length (tabulate n f) ≡ n
tab-length zero f _ = zero
tab-length (suc n) f i = suc (tab-length n (f ∘ fs) i)

tab-distrib : ∀ n (f : Fin n → A) m → ∃[ i ] (f i ≡ tabulate n f ! m)
tab-distrib (suc n) f f0 = f0 , refl
tab-distrib (suc n) f (fs m) = let i , p = tab-distrib n (f ∘ fs) m in fs i , p

tab-id : ∀ n (f : Fin n → A) → PathP (λ i → Fin (tab-length n f i) → A) (_!_ (tabulate n f)) f
tab-id zero f _ ()
tab-id (suc n) f i f0 = f f0
tab-id (suc n) f i (fs m) = tab-id n (f ∘ fs) i m

list-elim : ∀ {p} (P : List A → Type p) →
                  (∀ x xs → P xs → P (x ∷ xs)) →
                  (P []) →
                  ∀ xs → P xs
list-elim P f b [] = b
list-elim P f b (x ∷ xs) = f x xs (list-elim P f b xs)

foldr-universal : ∀ (h : List B → A) f e
                → (h [] ≡ e)
                → (∀ x xs → h (x ∷ xs) ≡ f x (h xs))
                → ∀ xs → h xs ≡ foldr f e xs
foldr-universal h f e base step [] = base
foldr-universal h f e base step (x ∷ xs) =
  step x xs ; cong (f x) (foldr-universal h f e base step xs)

foldr-fusion : ∀ (f : C → A) {_⊕_ : B → C → C} {_⊗_ : B → A → A} e
              → (∀ x y → f (x ⊕ y) ≡ x ⊗ f y)
              → ∀ xs → f (foldr _⊕_ e xs) ≡ foldr _⊗_ (f e) xs
foldr-fusion h {f} {g} e fuse =
  foldr-universal (h ∘ foldr f e) g (h e) refl (λ x xs → fuse x (foldr f e xs))

foldl-is-foldr : (f : B → A → B) (z : B) (xs : List A) →
                 foldl f z xs ≡ foldr (λ x k xs → k (f xs x)) id xs z
foldl-is-foldr f z xs =
  cong (_$ z) (foldr-universal (flip (foldl f)) (λ x k xs → k (f xs x)) id refl (λ x xs → refl) xs) 

foldl-fusion : ∀ (f : C → A) {_⊕_ : C → B → C}  {_⊗_ : A → B → A} e →
                 (∀ x y → f (x ⊕ y) ≡ f x ⊗ y) →
                 ∀ xs → f (foldl _⊕_ e xs) ≡ foldl _⊗_ (f e) xs
foldl-fusion h {f} {g} e fuse [] = refl
foldl-fusion h {f} {g} e fuse (x ∷ xs) =
  foldl-fusion h (f e x) fuse xs ; cong (flip (foldl g) xs) (fuse e x)

++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc xs ys zs = foldr-fusion (_++ zs) ys (λ _ _ → refl) xs

map-fusion : ∀ f (b : C) (g : A → B) xs → foldr f b (map g xs) ≡ foldr (f ∘ g) b xs
map-fusion f b g  = foldr-fusion (foldr f b) [] λ _ _ → refl

++-idʳ : (xs : List A) → xs ++ [] ≡ xs
++-idʳ [] = refl
++-idʳ (x ∷ xs) = cong (x ∷_) (++-idʳ xs)

open import Function.Injective

∷-inj : (x : A) → Injective (x ∷_)
∷-inj x xs ys = cong λ where [] → []
                             (_ ∷ zs) → zs

++-inj : (xs : List A) → Injective (xs ++_)
++-inj []       ys zs ys≡zs = ys≡zs
++-inj (x ∷ xs) ys zs ys≡zs = ++-inj xs ys zs (∷-inj x (xs ++ ys) (xs ++ zs) ys≡zs)

open import Algebra

module _ (mon : Monoid b) where
  open Monoid mon

  module _ (f : A → 𝑆) where
    monStepL : 𝑆 → A → 𝑆
    monStepL xs x = xs ∙ f x
    {-# INLINE monStepL #-}

    foldMapL : List A → 𝑆
    foldMapL = foldl monStepL ε

    foldMapLStep : ∀ x xs → f x ∙ foldMapL xs ≡ foldMapL (x ∷ xs)
    foldMapLStep x xs = foldl-fusion (f x ∙_) ε (λ y z → sym (assoc (f x) y (f z))) xs ; cong (flip (foldl monStepL) xs) (∙ε (f x) ; sym (ε∙ (f x)))

    foldl-foldr-monoid : (xs : List A) → foldMapL xs ≡ foldr (_∙_ ∘ f) ε xs
    foldl-foldr-monoid = foldr-universal _ (_∙_ ∘ f) ε refl λ x xs → sym (foldMapLStep x xs)

foldl′-foldl : (f : B → A → B) (z : B) (xs : List A) → foldl′ f z xs ≡ foldl f z xs
foldl′-foldl f z [] = refl
foldl′-foldl f z (x ∷ xs) = $!-≡ (λ y → foldl′ f y xs) (f z x) ; foldl′-foldl f (f z x) xs 

foldr′-foldr : (f : A → B → B) (z : B) (xs : List A) → foldr′ f z xs ≡ foldr f z xs
foldr′-foldr f z [] = refl
foldr′-foldr f z (x ∷ xs) = $!-≡ (f x) (foldr′ f z xs) ; cong (f x) (foldr′-foldr f z xs)
