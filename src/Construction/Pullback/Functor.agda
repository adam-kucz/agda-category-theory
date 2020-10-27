{-# OPTIONS --exact-split --prop #-}
module Construction.Pullback.Functor where

open import Universes
open import Type.Sum renaming (_,_ to _Σ,_)

open import Category
open import Functor
open import Category.Slice
open import Construction.Pullback.Definition
open import Construction.Pullback.Syntax

PullbackFunctor : ⦃ ℂ : Category 𝒰 𝒱 ⦄
  ⦃ pull : HasPullbacks ℂ ⦄
  {C' C : obj}
  (h : C' ~> C)
  → --------------------------------------
  Functor (ℂ ╱ C) (ℂ ╱ C')
PullbackFunctor ⦃ pull = pull ⦄{C'}{C} h =
  [F₀= (λ { (A Σ, α) → C' ×[ h ~> C <~ α ] A Σ, p₁})
  ,F₁= {!!}
  ,id-pres= {!!}
  ,∘-pres= {!!} ]
