{-# OPTIONS --exact-split --safe --prop #-}
module Category.Pointed where

open import Category
open import Construction.Terminal

open import PropUniverses

Point GlobalElement :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  ⦃ T : Terminal ⦄
  (X : obj)
  → ----------------------
  𝒱 ˙
Point X = 𝟙 ~> X

GlobalElement = Point

open import Proposition.Identity

well-pointed :
  (ℂ : Category 𝒰 𝒱)
  ⦃ T : Terminal ⦃ ℂ ⦄ ⦄
  → ----------------------
  𝒰 ⊔ 𝒱 ᵖ
well-pointed ℂ =
  {A B : obj}
  (f g : A ~> B)
  (p : ∀ (a : Point A) → f ∘ a == g ∘ a)
  → --------------------------------------------
  f == g
  where instance _ = ℂ
