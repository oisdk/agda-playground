module Algebra.FreeSemiring where

open import Prelude
open import Algebra

data 𝑅 : Type where
  _+_ : 𝑅 → 𝑅 → 𝑅
  _*_ : 𝑅 → 𝑅 → 𝑅
  1# : 𝑅
  0# : 𝑅

  +-comm : Commutative _+_
  +-assoc : Associative _+_
  *-assoc : Associative _*_
  0+ : Identityˡ _+_ 0#
  +0 : Identityʳ _+_ 0#
  1* : Identityˡ _*_ 1#
  *1 : Identityʳ _*_ 1#
  0* : Zeroˡ _*_ 0#
  *0 : Zeroʳ _*_ 0#
  ⟨+⟩* : _*_ Distributesˡ _+_
  *⟨+⟩ : _*_ Distributesʳ _+_

semiring𝑅 : Semiring 𝑅
semiring𝑅 .Semiring.nearSemiring .NearSemiring._+_ = _+_
semiring𝑅 .Semiring.nearSemiring .NearSemiring._*_ = _*_
semiring𝑅 .Semiring.nearSemiring .NearSemiring.1# = 1#
semiring𝑅 .Semiring.nearSemiring .NearSemiring.0# = 0#
semiring𝑅 .Semiring.nearSemiring .NearSemiring.+-assoc = +-assoc
semiring𝑅 .Semiring.nearSemiring .NearSemiring.*-assoc = *-assoc
semiring𝑅 .Semiring.nearSemiring .NearSemiring.0+ = 0+
semiring𝑅 .Semiring.nearSemiring .NearSemiring.+0 = +0
semiring𝑅 .Semiring.nearSemiring .NearSemiring.1* = 1*
semiring𝑅 .Semiring.nearSemiring .NearSemiring.*1 = *1
semiring𝑅 .Semiring.nearSemiring .NearSemiring.0* = 0*
semiring𝑅 .Semiring.nearSemiring .NearSemiring.⟨+⟩* = ⟨+⟩*
semiring𝑅 .Semiring.+-comm = +-comm
semiring𝑅 .Semiring.*0 = *0
semiring𝑅 .Semiring.*⟨+⟩ = *⟨+⟩

-- open import Algebra.SemiringLiterals semiring𝑅
-- open import Literals.Number
-- open import Data.Unit.UniversePolymorphic

-- ex : 𝑅
-- ex = 410928
