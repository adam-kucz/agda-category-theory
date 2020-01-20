{-# OPTIONS --safe --exact-split --prop  #-}
module Category.Unit where

open import Universes
open import Category

open import Proposition.Identity
open import Type.Unit renaming (𝟙 to Unit)

𝟙 : Category 𝒰₀ 𝒰₀
obj ⦃ 𝟙 ⦄ = Unit
_~>_ ⦃ 𝟙 ⦄ _ _ = Unit
id ⦃ 𝟙 ⦄ _ = ⋆
_∘_ ⦃ 𝟙 ⦄ _ _ = ⋆
left-unit ⦃ 𝟙 ⦄ ⋆ = refl ⋆
right-unit ⦃ 𝟙 ⦄ ⋆ = refl ⋆
assoc ⦃ 𝟙 ⦄ _ _ _ = refl ⋆
