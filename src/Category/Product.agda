{-# OPTIONS --safe --exact-split --prop  #-}
module Category.Product where

open import Category.Definition

open import Universes
open import Type.Sum renaming (_×_ to _x_)
open import Proof

infixl 153 _×_
_×_ : (ℂ : Category 𝒰 𝒱)(𝔻 : Category 𝒲 𝒯) → Category (𝒰 ⊔ 𝒲) (𝒱 ⊔ 𝒯)
ℂ × 𝔻 = record
  { obj = obj ⦃ ℂ ⦄ x obj ⦃ 𝔻 ⦄
  ; _~>_ = λ { (X , X') (Y , Y') → X ~> Y x X' ~> Y' }
  ; id = λ { (X , X') → id X , id X' }
  ; _∘_ = λ { (g , g') (f , f') → g ∘ f , g' ∘ f' }
  ; left-unit = λ { (f , f') → Σ== (left-unit f) (subrel $ left-unit f') }
  ; right-unit = λ { (f , f') → Σ== (right-unit f) (subrel $ right-unit f') }
  ; assoc = λ { (h , h') (g , g') (f , f') →
      Σ== (assoc h g f) (subrel $ assoc h' g' f') }
  }
  where instance _ = ℂ; _ = 𝔻

open import Functor

pi₁ :
  (ℂ : Category 𝒰 𝒱)(𝔻 : Category 𝒲 𝒯)
  → -----------------------
  Functor (ℂ × 𝔻) ℂ
pi₁ ℂ 𝔻 =
  [F₀= pr₁ ,F₁= pr₁
  ,id-pres= (λ { (X , _) → Id.refl (id X)})
  ,∘-pres= (λ { (g , _) (f , _) → Id.refl (g ∘ f)})
  ]
  where instance _ = ℂ

pi₂ :
  (ℂ : Category 𝒰 𝒱)(𝔻 : Category 𝒲 𝒯)
  → -----------------------
  Functor (ℂ × 𝔻) 𝔻
pi₂ ℂ 𝔻 =
  [F₀= pr₂ ,F₁= pr₂
  ,id-pres= (λ { (_ , X) → Id.refl (id X)})
  ,∘-pres= (λ { (_ , g) (_ , f) → Id.refl (g ∘ f)})
  ]
  where instance _ = 𝔻
