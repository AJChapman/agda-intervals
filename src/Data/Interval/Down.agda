open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsDecTotalOrder)
open import Algebra using (Op₂)
open import Algebra.Structures using (IsSemigroup)

-- A one-sided interval, adapted from Timely Computation to add the possibility of closed intervals.
module Data.Interval.Down
  {a ℓ : Level}
  {A : Set a}
  (_≈_ : Rel A ℓ)
  (_≤_ : Rel A ℓ)
  (isDTO : IsDecTotalOrder _≈_ _≤_)
  (_+_ : Op₂ A)
  (isSemigroup : IsSemigroup _≈_ _+_)
  where

open IsDecTotalOrder isDTO using (_≤?_)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Nullary.Decidable using (yes; no)

open import Relation.Binary.Properties.Poset
  (record { isPartialOrder = IsDecTotalOrder.isPartialOrder isDTO })
  using (_<_)
open import Algebra.Construct.NaturalChoice.Min
  (DecTotalOrder.totalOrder (record { isDecTotalOrder = isDTO }))
  using (_⊓_)

infix 9 _⟩
infix 9 _]
data I↓ : Set a where
  _] : A → I↓ -- Inclusive (closed interval)
  _⟩ : A → I↓ -- Exclusive (open interval)
  +∞ : I↓

infix 4 _∈_
_∈_ : A → I↓ → Set ℓ
t ∈ x ] = t ≤ x
t ∈ x ⟩ = t < x
t ∈ +∞ = ⊤

infixl 6 _∩_
_∩_ : Op₂ I↓
x ] ∩ y ] = (x ⊓ y) ]
x ] ∩ y ⟩ with y ≤? x
... | yes y≤x = y ⟩
... | no  y>x = x ]
x ⟩ ∩ y ] with x ≤? y
... | yes x≤y = x ⟩
... | no  x>y = y ]
x ⟩ ∩ y ⟩ = (x ⊓ y) ⟩
x ⟩ ∩  +∞ = x ⟩
x ] ∩  +∞ = x ]
+∞  ∩ y ] = y ]
+∞  ∩ y ⟩ = y ⟩
+∞  ∩  +∞ = +∞

infixl 7 _✶_
_✶_ : Op₂ I↓
x ] ✶ y ] = (x + y) ]
x ] ✶ y ⟩ = (x + y) ⟩
x ⟩ ✶ y ] = (x + y) ⟩
x ⟩ ✶ y ⟩ = (x + y) ⟩
x   ✶  +∞ = +∞
+∞  ✶ y   = +∞
