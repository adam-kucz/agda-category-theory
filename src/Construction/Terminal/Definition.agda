{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category

module Construction.Terminal.Definition ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Proposition.Sum
open import Proposition.Identity
open import Logic

IsTerminal : (𝟙 : obj) → 𝒰 ⊔ 𝒱 ᵖ
IsTerminal 𝟙 = ∀(X : obj) → ∃!-of-type (X ~> 𝟙)

Terminal : 𝒰 ⊔ 𝒱 ˙
Terminal = Σₚ IsTerminal

𝟙 : ⦃ T : Terminal ⦄ → obj
𝟙 ⦃ T ⦄ = elem T

global-element-of point-of constant-of : ⦃ T : Terminal ⦄ (X : obj) → 𝒱 ˙
global-element-of = 𝟙 ~>_
point-of = global-element-of
constant-of = global-element-of
