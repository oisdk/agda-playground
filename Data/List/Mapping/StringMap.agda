{-# OPTIONS --cubical --safe #-}

module Data.List.Mapping.StringMap where

open import Data.String using (String; stringOrd)
open import Data.List.Mapping stringOrd public
open import Prelude
open import Data.Maybe

-- example : Record (∅ [ "name" ]︓ String [ "age" ]︓ ℕ [ "occ" ]︓ Bool)
-- example =
--   ∅ [ "age"  ]≔ 30
--     [ "occ"  ]≔ true
--     [ "name" ]≔ "Jo"
