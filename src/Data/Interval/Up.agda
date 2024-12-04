open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsDecTotalOrder)
open import Algebra using (Op₂)
open import Algebra.Structures using (IsSemigroup)

-- A one-sided interval, adapted from Timely Computation to add the possibility of closed intervals.
module Data.Interval.Up
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
open import Algebra.Construct.NaturalChoice.Max
  (DecTotalOrder.totalOrder (record { isDecTotalOrder = isDTO }))
  using (_⊔_)

infix 9 [_
infix 9 ⟨_
data I↑ : Set a where
  -∞ : I↑
  ⟨_ : A → I↑ -- Exclusive (open interval)
  [_ : A → I↑ -- Inclusive (closed interval)

infix 4 _∈_
_∈_ : A → I↑ → Set ℓ
t ∈ -∞ = ⊤
t ∈ ⟨ x = x < t
t ∈ [ x = x ≤ t

infixl 6 _∩_
_∩_ : Op₂ I↑
-∞  ∩ -∞ = -∞
-∞  ∩  y = y
x   ∩ -∞ = x
⟨ x ∩ ⟨ y = ⟨ (x ⊔ y)
⟨ x ∩ [ y with y ≤? x
... | yes y≤x = ⟨ x
... | no  x<y = [ y
[ x ∩ ⟨ y with x ≤? y
... | yes x≤y = ⟨ y
... | no  y<x = [ x
[ x ∩ [ y = [ (x ⊔ y)

infixl 7 _✶_
_✶_ : Op₂ I↑
-∞  ✶  -∞ = -∞
-∞  ✶   y = -∞
x   ✶  -∞ = -∞
⟨ x ✶ ⟨ y = ⟨ (x + y)
⟨ x ✶ [ y = ⟨ (x + y)
[ x ✶ ⟨ y = ⟨ (x + y)
[ x ✶ [ y = [ (x + y)
