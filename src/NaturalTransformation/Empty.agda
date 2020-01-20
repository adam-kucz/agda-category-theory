{-# OPTIONS --exact-split --safe --prop #-}
module NaturalTransformation.Empty where

open import Universes
open import Category
open import Category.Empty
open import Functor
open import Functor.Empty
open import NaturalTransformation.Definition

EmptyNatTrans :
  {ℂ : Category 𝒰 𝒱}
  (F : Functor 𝟘 ℂ)
  → --------------------
  F ⟹ EmptyFunctor ℂ
EmptyNatTrans F at ()
naturality ⦃ EmptyNatTrans F ⦄ {()}
