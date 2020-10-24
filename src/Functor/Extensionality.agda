{-# OPTIONS --exact-split --prop #-}
module Functor.Extensionality where

open import Functor.Definition
open import Category

open import Universes
open import Proposition.Identity
open import Proof

open import Axiom.FunctionExtensionality

funct-ext :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F G : Functor ℂ 𝔻)
  (p₁ : ∀ X → F₀ ⦃ F ⦄ X == F₀ ⦃ G ⦄ X)
  (p₂ : ∀ {X Y} (f : mor ℂ X Y) → F₁ ⦃ F ⦄ f Het.== F₁ ⦃ G ⦄ f)
  → -------------------------------------------------------------
  F == G
funct-ext F G p₁ p₂ = Functor== F G
  (subrel $ fun-ext λ x → subrel $ p₁ x)
  (fun-ext-implicit λ X → fun-ext-implicit λ Y → fun-ext λ f → p₂ f)
