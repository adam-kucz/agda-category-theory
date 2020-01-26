{-# OPTIONS --exact-split --prop --safe #-}
module Functor.Construction.Property where

open import Functor.Construction.Definition

open import Universes
open import Proof

open import Category
open import Functor.Definition

o-Const :
  (ℂ : Category 𝒰 𝒱)
  {𝔻 : Category 𝒲 𝒯}
  {𝔼 : Category 𝒮 𝒵}
  (X : obj ⦃ 𝔻 ⦄)
  (F : Functor 𝔻 𝔼)
  → --------------------
  let instance _ = F in
  F o Const ℂ X == Const ℂ {𝔼} (F₀ X)
o-Const ℂ {_}{𝔼} X F =
  Functor== (F o Const ℂ X) (Const ℂ {𝔼} (F₀ X))
    (refl (λ _ → F₀ X))
    (ap (λ — → λ {_}{_} _ → —) (id-preserv X))
  where instance _ = F
