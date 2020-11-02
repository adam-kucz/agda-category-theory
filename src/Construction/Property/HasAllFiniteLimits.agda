{-# OPTIONS --exact-split --safe --prop #-}
open import Universes
open import Category

module Construction.Property.HasAllFiniteLimits ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Category.Discrete
open import Construction.Equalizer
open import Construction.Limit
open import Construction.Product.Definition

HasAllFiniteProducts∧HasEqualizers→HasAllFiniteLimits :
  (fp : HasAllFiniteProducts ℂ)
  (eq : HasEqualizers ℂ)
  → ----------------------------------------
  HasAllFiniteLimits ℂ
HasAllFiniteProducts∧HasEqualizers→HasAllFiniteLimits fp eq 𝕀 fin𝕀 D = {!!}
