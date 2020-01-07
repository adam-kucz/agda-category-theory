{-# OPTIONS --exact-split --safe --prop #-}
module CategoryTheory.Category.Cat where

open import CategoryTheory.Category.Definition
open import CategoryTheory.Functor

open import Universes
open import Proposition.Identity

CatCategory : Category (𝒰 ⁺ ⊔ 𝒱 ⁺) (𝒰 ⊔ 𝒱)
obj ⦃ CatCategory {𝒰} {𝒱} ⦄ = Category 𝒰 𝒱
_~>_ ⦃ CatCategory ⦄ = Functor
id ⦃ CatCategory ⦄ = Id
_∘_ ⦃ CatCategory ⦄ = _o_
left-unit ⦃ CatCategory ⦄ f = refl f
right-unit ⦃ CatCategory ⦄ f = refl f
assoc ⦃ CatCategory ⦄ h g f = refl (h o (g o f))

