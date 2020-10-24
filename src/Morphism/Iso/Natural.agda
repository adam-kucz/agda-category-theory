{-# OPTIONS --exact-split --prop #-}
module Morphism.Iso.Natural where

open import Morphism.Iso.Definition

open import PropUniverses
open import Category
open import Functor
open import Category.FunCategory

private
  instance
    functor-category :
      {ℂ : Category 𝒰 𝒱}
      {𝔻 : Category 𝒲 𝒯}
      → -------------------------------------------
      Category (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯) (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯)
    functor-category {ℂ = ℂ}{𝔻} = FunCategory ℂ 𝔻

nat-iso :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F G : Functor ℂ 𝔻}
  (f : F ~> G)
  → --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
nat-iso f = iso f

open import Logic

_nat-≅_ :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F G : Functor ℂ 𝔻)
  → --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
F nat-≅ G = ∃ λ (f : F ~> G) → nat-iso f

_nat-≅-unique_ :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F G : Functor ℂ 𝔻)
  → --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
F nat-≅-unique G = ∃! λ (f : F ~> G) → nat-iso f

