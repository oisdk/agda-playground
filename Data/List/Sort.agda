{-# OPTIONS --cubical --safe #-}

module Data.List.Sort where


open import Data.List.Sort.InsertionSort using (insert-sort; sort-sorts; sort-perm; perm-invar)
open import Data.List.Sort.MergeSort using (merge-sort; merge≡insert-sort)
