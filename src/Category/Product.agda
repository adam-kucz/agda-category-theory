{-# OPTIONS --safe --exact-split --prop  #-}
module Category.Product where

open import Category.Definition

open import Universes
open import Type.Sum renaming (_×_ to _x_)
open import Proposition.Identity

infixl 153 _×_
_×_ : (ℂ : Category 𝒰 𝒱)(𝔻 : Category 𝒲 𝒯) → Category (𝒰 ⊔ 𝒲) (𝒱 ⊔ 𝒯)
ℂ × 𝔻 = record
  { obj = obj ⦃ ℂ ⦄ x obj ⦃ 𝔻 ⦄
  ; _~>_ = λ { (X , X') (Y , Y') → X ~> Y x X' ~> Y' }
  ; id = λ { (X , X') → id X , id X' }
  ; _∘_ = λ { (g , g') (f , f') → g ∘ f , g' ∘ f' }
  ; left-unit = λ { (f , f') → Σ== (left-unit f) (left-unit f') }
  ; right-unit = λ { (f , f') → Σ== (right-unit f) (right-unit f') }
  ; assoc = λ { (h , h') (g , g') (f , f') →
      Σ== (assoc h g f) (assoc h' g' f') }
  }
  where instance _ = ℂ; _ = 𝔻
