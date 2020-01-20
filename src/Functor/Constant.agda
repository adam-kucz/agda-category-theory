{-# OPTIONS --exact-split --safe --prop #-}
module Functor.Constant where

open import Universes
open import Category
open import Functor.Definition

open import Proposition.Identity
open import Relation.Binary using (sym)

Const :
  (ℂ : Category 𝒰 𝒱)
  {𝔻 : Category 𝒲 𝒯}
  (X : obj ⦃ 𝔻 ⦄)
  → --------------------
  Functor ℂ 𝔻
Const ℂ {𝔻} X = record
  { F₀ = λ _ → X
  ; F₁ = λ _ → id X
  ; id-preserv = λ _ → refl (id X)
  ; ∘-preserv = λ _ _ → sym (left-unit (id X))
  }
  where private instance _ = 𝔻
