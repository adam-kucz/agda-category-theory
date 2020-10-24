{-# OPTIONS --exact-split --safe --prop #-}
module Category.Cat.Definition where

open import Category.Definition
open import Functor renaming (Id to FunctorId)

open import Universes
open import Proof

CatCategory : Category (𝒰 ⁺ ⊔ 𝒱 ⁺) (𝒰 ⊔ 𝒱)
obj ⦃ CatCategory {𝒰} {𝒱} ⦄ = Category 𝒰 𝒱
_~>_ ⦃ CatCategory ⦄ = Functor
id ⦃ CatCategory ⦄ = FunctorId
_∘_ ⦃ CatCategory ⦄ = _o_
left-unit ⦃ CatCategory ⦄ f = refl f
right-unit ⦃ CatCategory ⦄ f = refl f
assoc ⦃ CatCategory ⦄ h g f = refl (h o (g o f))
