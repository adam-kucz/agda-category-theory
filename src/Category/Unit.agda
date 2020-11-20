{-# OPTIONS --safe --exact-split --prop  #-}
module Category.Unit where

open import Universes
open import Category

open import Proposition.Identity
open import Type.Unit renaming (𝟙 to Unit)

𝟙 : Category 𝒰 𝒱
obj ⦃ 𝟙 ⦄ = Lift𝒰 Unit
_~>_ ⦃ 𝟙 ⦄ _ _ = Lift𝒰 Unit
id ⦃ 𝟙 ⦄ _ = ↑type ⋆
_∘_ ⦃ 𝟙 ⦄ _ _ = ↑type ⋆
left-unit ⦃ 𝟙 ⦄ _ = refl _
right-unit ⦃ 𝟙 ⦄ _ = refl _
assoc ⦃ 𝟙 ⦄ _ _ _ = refl _
