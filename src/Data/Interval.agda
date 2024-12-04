open import Level
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsDecTotalOrder)
open import Algebra using (Op₂)
open import Algebra.Structures using (IsSemigroup)

-- From Timely Computation
module Data.Interval
  {a ℓ : Level}
  {A : Set a}
  (_≈_ : Rel A ℓ)
  (_≤_ : Rel A ℓ)
  (isDTO : IsDecTotalOrder _≈_ _≤_)
  (_+_ : Op₂ A)
  (isSemigroup : IsSemigroup _≈_ _+_)
  where

open import Data.Product using (_×_; _,_; ∃)
open import Data.Unit.Polymorphic using (tt)
open IsDecTotalOrder isDTO using (refl)

open import Data.Interval.Up   _≈_ _≤_ isDTO _+_ isSemigroup as ↑ using (I↑; ⟨_; [_; -∞)
open import Data.Interval.Down _≈_ _≤_ isDTO _+_ isSemigroup as ↓ using (I↓; _⟩; _]; +∞)

I : Set a
I = I↑ × I↓

infix 4 _∈_
_∈_ : A → I → Set ℓ
x ∈ (l , u) = x ↑.∈ l × x ↓.∈ u

U : I
U = -∞ , +∞

-- x\inU
x∈U : ∀ {x} → x ∈ U
x∈U = tt , tt

-- \<<_\>>
⟪_⟫ : A → I
⟪ x ⟫ = [ x , x ]

x∈⟪x⟫ : ∀ {x} → x ∈ ⟪ x ⟫
x∈⟪x⟫ = refl , refl

-- _\i_
infixl 6 _∩_
_∩_ : Op₂ I
(l₁ , u₁) ∩ (l₂ , u₂) = l₁ ↑.∩ l₂ , u₁ ↓.∩ u₂

-- _\st6_
infixl 7 _✶_
_✶_ : Op₂ I
(l₁ , u₁) ✶ (l₂ , u₂) = l₁ ↑.✶ l₂ , u₁ ↓.✶ u₂

overlaps : I → I → Set (a ⊔ ℓ)
overlaps i₁ i₂ = ∃ λ t → t ∈ i₁ ∩ i₂
