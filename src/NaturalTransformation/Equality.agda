{-# OPTIONS --exact-split --safe --prop #-}
module NaturalTransformation.Equality where

open import Universes
open import Category
open import Functor
open import NaturalTransformation.Definition

NaturalTransformation== :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F G : Functor ℂ 𝔻}
  (θ ϕ : NaturalTransformation F G)
  (p : at == top ◻₂)
  → -----------------------------
  θ == ϕ
NaturalTransformation== = ?

