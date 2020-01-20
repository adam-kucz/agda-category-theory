{-# OPTIONS --exact-split --prop --safe #-}
open import PropUniverses
open import Category

module Construction.Simple.Coproduct.Definition
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  where

open import Logic
open import Proposition.Identity

open import Category.Opposite
open import Construction.Simple.Product.Definition

IsCoproduct = IsCoproduct' ℂ
  where IsCoproduct' = dual (λ ℂ → IsProduct ⦃ ℂ ⦄)

Coproduct = Coproduct' ℂ
  where Coproduct' = dual (λ ℂ → Product ⦃ ℂ ⦄)

infixl 180 _+_
_+_ = _×_ ⦃ ℂ ᵒᵖ ⦄
inl = π₁ ⦃ ℂ ᵒᵖ ⦄
inr = π₂ ⦃ ℂ ᵒᵖ ⦄
[_,_] = 〈_,_〉 ⦃ ℂ ᵒᵖ ⦄
