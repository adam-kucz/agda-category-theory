{-# OPTIONS --exact-split --safe --prop #-}
module Functor.Definition where

open import Category

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
    F₁ : {X Y : obj ⦃ ℂ ⦄} (f : mor ℂ X Y) → mor 𝔻 (F₀ X) (F₀ Y)
    id-preserv : ∀ X → F₁ (id ⦃ ℂ ⦄ X) == id ⦃ 𝔻 ⦄ (F₀ X)
    ∘-preserv : {X Y Z : obj ⦃ ℂ ⦄}
      (g : mor ℂ Y Z)
      (f : mor ℂ X Y)
      → --------------------------
      F₁ (_∘_ ⦃ ℂ ⦄ g f) == _∘_ ⦃ 𝔻 ⦄ (F₁ g) (F₁ f)

open Functor ⦃ … ⦄ public

{-# DISPLAY Functor.F₀ F X = F X #-}
{-# DISPLAY Functor.F₁ F f = F f #-}

Functor== :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F G : Functor ℂ 𝔻)
  (p₁ : F₀ ⦃ F ⦄ == F₀ ⦃ G ⦄)
  (p₂ : (λ {X Y} → F₁ ⦃ F ⦄ {X} {Y}) == (λ {X Y} → F₁ ⦃ G ⦄ {X} {Y}))
  → -------------------------------------------------------------
  F == G
Functor== F G (refl _) (refl _) = refl F
