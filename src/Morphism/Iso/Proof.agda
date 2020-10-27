{-# OPTIONS --exact-split --safe --prop #-}
open import Category
open import PropUniverses hiding (X; Y)

module Morphism.Iso.Proof ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Morphism.Iso.Definition
open import Morphism.Iso.Property

open import Proof

module Composable-≅ where
  open MakeTransComposable _≅_ ⦃ Transitive≅ ⦄ public
