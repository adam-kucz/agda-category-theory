{-# OPTIONS --exact-split --prop #-}
module Category.Cat.Terminal where

open import Category.Cat.Definition

open import Universes
open import Type.Unit hiding (𝟙)
open import Logic
open import Proof

open import Functor
open import Category.Unit
open import Construction.Terminal hiding (𝟙)

open import Functor.Extensionality

CatTerminal : Terminal ⦃ CatCategory {𝒰}{𝒱} ⦄
CatTerminal = 𝟙 , λ X → Const X (↑type ⋆) ,
  λ F → funct-ext F (Const X (↑type ⋆))
    (λ X' → (_== ↑type ⋆) for F₀ ⦃ F ⦄ X' by-case λ {(↑type ⋆) → refl _})
    λ f → (Het._== ↑type ⋆) for F₁ ⦃ F ⦄ f by-case λ { (↑type ⋆) → refl _}
