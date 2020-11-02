{-# OPTIONS --exact-split --safe --prop #-}
module Category.Discrete where

open import Universes
open import Type.Identity
open import Proposition.Identity

open import Category

Discrete : (X : 𝒰 ˙) → Category 𝒰 𝒰
Discrete X = record
  { obj = X
  ; _~>_ = _≡_
  ; id = Id.refl
  ; _∘_ = λ { (Id.refl _) f → f}
  ; left-unit = Id.refl
  ; right-unit = λ { (Id.refl _) → Id.refl _}
  ; assoc = λ { (Id.refl _) g f → Id.refl _}
  }
