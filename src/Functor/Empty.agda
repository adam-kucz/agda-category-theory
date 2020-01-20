{-# OPTIONS --exact-split --safe --prop #-}
module Functor.Empty where

open import Universes
open import Category
open import Functor.Definition

open import Category.Empty

EmptyFunctor : 
  (ℂ : Category 𝒰 𝒱)
  → --------------------
  Functor 𝟘 ℂ
EmptyFunctor ℂ = record
  { F₀ = λ ()
  ; F₁ = λ { {()} }
  ; id-preserv = λ ()
  ; ∘-preserv = λ { {()} }
  }
