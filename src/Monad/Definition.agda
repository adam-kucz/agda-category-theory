{-# OPTIONS --exact-split --safe --prop #-}
module Monad.Definition where

open import Category
open import Functor
open import NaturalTransformation renaming (
  Composition to _O_; Identity to 𝟙;
  HorizontalComposition to _::_;
  left-compose to _<:_;
  right-compose to _:>_)

open import Universes hiding (Type)
open import Proposition.Identity

record Monad (ℂ : Category 𝒰 𝒱) : 𝒰 ⊔ 𝒱 ˙ where

  field
    T : EndoFunctor ℂ

  Type : (F : EndoFunctor ℂ) → 𝒰 ⊔ 𝒱 ˙
  Type = _⟹ T

  field
    μ : Type (T o T)
    η : Type (Id ℂ)

  infixl 212 _×_
  _×_ : ∀ {F G}(θ : Type F)(ϕ : Type G) → Type (F o G)
  θ × ϕ = μ O (θ :: ϕ)

  field
    right-unit : 𝟙 T × η == 𝟙 T
    left-unit : η × 𝟙 T == 𝟙 T
    assoc : 𝟙 T × μ == μ × 𝟙 T

open Monad ⦃ … ⦄ public

{-# DISPLAY Monad.T M = T #-}
{-# DISPLAY Monad.μ M = μ #-}
{-# DISPLAY Monad.η M = η #-}
