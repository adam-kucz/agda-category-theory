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
  constructor [F₀=_,F₁=_,id-pres=_,∘-pres=_]
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

EndoFunctor : (ℂ : Category 𝒰 𝒱) → 𝒰 ⊔ 𝒱 ˙
EndoFunctor ℂ = Functor ℂ ℂ

Functor== :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F G : Functor ℂ 𝔻)
  (p₁ : F₀ ⦃ F ⦄ == F₀ ⦃ G ⦄)
  (p₂ : (λ {X Y} → F₁ ⦃ F ⦄ {X} {Y}) Het.== (λ {X Y} → F₁ ⦃ G ⦄ {X} {Y}))
  → -------------------------------------------------------------------------
  F == G
Functor== F F (refl _) (Het.refl _) = refl F
