{-# OPTIONS --exact-split --prop #-}
module CategoryTheory.Functor.Representable where

open import Universes
open import CategoryTheory.Category
open import CategoryTheory.Functor.Definition
open import CategoryTheory.Example.Set'

open import Axiom.FunctionExtensionality

open import Relation.Binary.Property using (sym)
import Proposition.Identity

RepresentableFunctor :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  (X : obj)
  → -------------------
  Functor ℂ Set'
F₀ ⦃ RepresentableFunctor X ⦄ Y = X ~> Y
F₁ ⦃ RepresentableFunctor X ⦄ f g = f ∘ g
id-preserv ⦃ RepresentableFunctor X ⦄ Y = fun-ext left-unit
∘-preserv ⦃ RepresentableFunctor X ⦄ g f = fun-ext λ h → sym (assoc g f h)
