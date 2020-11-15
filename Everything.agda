{-# OPTIONS --cubical #-}
module Everything where
open import Equiv
open import Prelude
open import Relation.Unary
open import Relation.Binary.Bool
open import Relation.Binary.Equivalence.Reasoning
open import Relation.Binary.Construct.LowerBound
open import Relation.Binary.Construct.Bounded
open import Relation.Nullary.Stable.Properties
open import Relation.Nullary.Stable.Base
open import Relation.Nullary.Stable
open import Relation.Nullary.Discrete.Properties
open import Relation.Nullary.Discrete.Base
open import Relation.Nullary.Discrete.FromBoolean
open import Relation.Nullary.Decidable
open import Relation.Nullary.Discrete
open import Relation.Nullary.Omniscience
open import Relation.Nullary.Decidable.Properties
open import Relation.Nullary.Decidable.Logic
open import Relation.Nullary.Decidable.Base
open import Relation.Nullary
open import Relation.Binary
open import Categories
open import HLevels
open import Path
open import WellFounded
open import Function
open import Level
open import LexPerm
open import TreeFold
open import TreeFold.Indexed
open import Strict
open import Path.Reasoning
open import Instance
open import Function.Injective
open import Function.Biconditional
open import Function.Surjective.Properties
open import Function.Surjective.Base
open import Function.Isomorphism
open import Function.Fiber
open import Function.Injective.Properties
open import Function.Injective.Base
open import Function.Surjective
open import Algebra
open import Codata.Stream
open import Container.Membership
open import Container.Stream
open import Container.List
open import Container.List.Isomorphism
open import Container.List.Syntax
open import Karatsuba
open import Lens.Operators
open import Lens.Definition
open import Lens.Pair
open import Lens.Composition
open import Container
open import BCK
open import Strict.Properties
open import Literals.Number
open import Lens
open import HITs.PropositionalTruncation.Properties
open import HITs.PropositionalTruncation.Sugar
open import HITs.PropositionalTruncation
open import Data.Bits
open import Data.Tree.Rose
open import Data.Tree.Braun
open import Data.Vec
open import Data.Bool
open import Data.Dyck
open import Data.Unit.UniversePolymorphic
open import Data.Unit.Properties
open import Data.Fin.Properties
open import Data.Fin.Base
open import Data.Fin.Literals
open import Data.Empty.UniversePolymorphic
open import Data.Empty.Properties
open import Data.Empty.Base
open import Data.RBTree
open import Data.Empty
open import Data.AVLTree
open import Data.Tuple.UniverseMonomorphic
open import Data.Tuple.Base
open import Data.Array.Skew
open import Data.Nat.Fold
open import Data.Nat.WellFounded
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.Base
open import Data.Nat.Literals
open import Data.Maybe.Properties
open import Data.Maybe.Sugar
open import Data.Maybe.Base
open import Data.Lift
open import Data.Array
open import Data.Product.NAry
open import Data.Sigma.Properties
open import Data.Sigma.Base
open import Data.Pi.Base
open import Data.List
open import Data.Vec.Inductive
open import Data.Vec.Iterated
open import Data.Bits.Order.Reverse
open import Data.Bits.Fold
open import Data.Bits.Strict
open import Data.Bits.Equatable
open import Data.Bits.Order
open import Data.Maybe
open import Data.Sum.Properties
open import Data.Bag
open import Data.MonoidalHeap
open import Data.List.Membership
open import Data.List.Relation.Unary
open import Data.List.Relation.Binary.Permutation
open import Data.List.Filter
open import Data.List.Sort.MergeSort
open import Data.List.Sort.Sorted
open import Data.List.Sort.InsertionSort
open import Data.List.Properties
open import Data.List.Sugar
open import Data.List.Kleene
open import Data.List.Kleene.Membership
open import Data.List.Kleene.Relation.Unary
open import Data.List.Syntax
open import Data.List.Sort
open import Data.List.Base
open import Data.Sum
open import Data.Rational.Unnormalised
open import Data.Rational.SternBrocot
open import Data.Bool.Properties
open import Data.Bool.Base
open import Data.Bool.Truth
open import Data.Fin
open import Data.Integer.Literals
open import Data.Binary.PerformanceTests.Subtraction
open import Data.Binary.PerformanceTests.Conversion
open import Data.Binary.PerformanceTests.Multiplication
open import Data.Binary.PerformanceTests.Addition
open import Data.Binary.Testers
open import Data.Binary.Equatable
open import Data.Binary.Subtraction
open import Data.Binary.Increment
open import Data.Binary.Isomorphism
open import Data.Binary.Increment.Strict
open import Data.Binary.Conversion.Strict
open import Data.Binary.Conversion.Fast.Properties
open import Data.Binary.Conversion.Fast
open import Data.Binary.Skew
open import Data.Binary.Order
open import Data.Binary.Multiplication.Properties
open import Data.Binary.Definition
open import Data.Binary.Conversion
open import Data.Binary.Literals
open import Data.Binary.Multiplication
open import Data.Binary.Addition
open import Data.Binary.Addition.Properties
open import Data.Integer
open import Data.Pi
open import Data.Ternary
open import Data.FingerTree
open import Data.Tuple
open import Data.Unit
open import Data.Nat
open import Data.Sigma
open import Data.Binary
open import Categories.Pullback
open import Categories.Functor
open import Categories.Pushout
open import Categories.Coequalizer
open import Categories.Exercises
open import Categories.Exponential
open import Categories.HSets
open import Categories.Product
open import Control.Monad.State
open import Algebra.Construct.Dyck
open import Algebra.Construct.Free.Semilattice
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Membership
open import Algebra.Construct.Free.Semilattice.Relation.Unary.All.Properties
open import Algebra.Construct.Free.Semilattice.Relation.Unary.All.Dec
open import Algebra.Construct.Free.Semilattice.Relation.Unary.All.Map
open import Algebra.Construct.Free.Semilattice.Relation.Unary.All.Def
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Properties
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Dec
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Map
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Def
open import Algebra.Construct.Free.Semilattice.Relation.Unary
open import Algebra.Construct.Free.Semilattice.Direct
open import Algebra.Construct.Free.Semilattice.FromList
open import Algebra.Construct.Free.Semilattice.Eliminators
open import Algebra.Construct.Free.Semilattice.Homomorphism
open import Algebra.Construct.Free.Semilattice.Extensionality
open import Algebra.Construct.Free.Semilattice.Union
open import Algebra.Construct.Free.Semilattice.Definition
open import Algebra.Construct.OrderedMonoid
