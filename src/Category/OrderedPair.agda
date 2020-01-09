{-# OPTIONS --exact-split --safe --prop #-}

open import Category.Definition

open import Universes

module Category.OrderedPair
  (ℂ : Category 𝒰 𝒱)
  (𝔻 : Category 𝒲 𝒯)
  where

private
  instance
    _ = ℂ
    _ = 𝔻

open import Type.Sum renaming (_×_ to _x_)

_×_ : Category (𝒰 ⊔ 𝒲) (𝒱 ⊔ 𝒯)
obj ⦃ _×_ ⦄ = obj ⦃ ℂ ⦄ x obj ⦃ 𝔻 ⦄
_~>_ ⦃ _×_ ⦄ (X , X') (Y , Y') = X ~> Y x X' ~> Y'
id ⦃ _×_ ⦄ (X , X') = id X , id X'
_∘_ ⦃ _×_ ⦄ (g , g') (f , f') = g ∘ f , g' ∘ f'
left-unit ⦃ _×_ ⦄ (f , f') = Σ== (left-unit f) (left-unit f')
right-unit ⦃ _×_ ⦄ (f , f') = Σ== (right-unit f) (right-unit f')
assoc ⦃ _×_ ⦄ (h , h') (g , g') (f , f') = Σ== (assoc h g f) (assoc h' g' f')

