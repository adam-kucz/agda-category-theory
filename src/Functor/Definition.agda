{-# OPTIONS --exact-split --safe --prop #-}
module CategoryTheory.Functor.Definition where

open import CategoryTheory.Category

open import Universes
open import Proposition.Identity

record Functor
  (ℂ : Category 𝒰 𝒱)
  (𝔻 : Category 𝒲 𝒯)
  : ----------------------------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  where

  field
    F₀ : (X : obj ⦃ ℂ ⦄) → obj ⦃ 𝔻 ⦄
    -- F₁ : {X Y : obj} (f : X ~> Y) → F₀ X ~> F₀ Y
    F₁ : {X Y : obj ⦃ ℂ ⦄} (f : mor ⦃ ℂ ⦄ X Y) → mor ⦃ 𝔻 ⦄ (F₀ X) (F₀ Y)
    id-preserv : ∀ X → F₁ (id ⦃ ℂ ⦄ X) == id ⦃ 𝔻 ⦄ (F₀ X)
    ∘-preserv : {X Y Z : obj ⦃ ℂ ⦄}
      (g : mor ⦃ ℂ ⦄ Y Z)
      (f : mor ⦃ ℂ ⦄ X Y)
      → --------------------------
      F₁ (_∘_ ⦃ ℂ ⦄ g f) == _∘_ ⦃ 𝔻 ⦄ (F₁ g) (F₁ f)

open Functor ⦃ … ⦄ public
