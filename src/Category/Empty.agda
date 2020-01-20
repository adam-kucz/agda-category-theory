{-# OPTIONS --safe --exact-split --prop  #-}
module Category.Empty where

open import Universes
open import Category

open import Type.Empty renaming (𝟘 to Empty)

𝟘 : Category 𝒰₀ 𝒰₀
obj ⦃ 𝟘 ⦄ = Empty
_~>_ ⦃ 𝟘 ⦄ ()
id ⦃ 𝟘 ⦄ ()
_∘_ ⦃ 𝟘 ⦄ {()}
left-unit ⦃ 𝟘 ⦄ {()}
right-unit ⦃ 𝟘 ⦄ {()}
assoc ⦃ 𝟘 ⦄ {()}
