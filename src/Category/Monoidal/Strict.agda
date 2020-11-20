{-# OPTIONS --exact-split --safe --prop #-}
module Category.Monoidal.Strict where

open import Universes
open import Operation.Binary
open import Structure.Monoid

open import Category.Definition hiding (ℂ)

record StrictMonoidalCategory (𝒰 𝒱 : Universe) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ˙ where
  field
    ⦃ ℂ ⦄ : Category 𝒰 𝒱
    ⦃ ⊗-monoid ⦄ : Monoid obj

