{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category

module Construction.Cone.Definition ⦃ ℂ : Category 𝒰 𝒱 ⦄ (𝕀 : Category 𝒲 𝒯) where

open import Functor
open import NaturalTransformation

Diagram : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
Diagram = Functor 𝕀 ℂ

Cone : (D : Diagram) (U : obj) → 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
Cone D U = Const 𝕀 U ⟹ D

