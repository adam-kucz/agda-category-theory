{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Category
open import Construction.Product

module Construction.Exponential.Definition
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  ⦃ P : HasProducts ℂ ⦄
  where

open import Construction.Product
open import Proposition.Identity
open import Logic

record IsExponential
    (X Y : obj)
    (P : obj)
    (app : P × X ~> Y)
    : -------------------
    𝒰 ⊔ 𝒱 ᵖ
  where
  field
    curry :
      (Z : obj)
      (f : Z × X ~> Y)
      → ----------------
      ∃! λ (g : Z ~> P) → app ∘ (g ⊠ id X) == f

record Exponential (X Y : obj) : 𝒰 ⊔ 𝒱 ˙ where
  field
    exp : obj
    app : exp × X ~> Y
    ⦃ exp-def ⦄ : IsExponential X Y exp app

open Exponential ⦃ … ⦄ public

infixl 190 _^_
_^_ : (Y X : obj) ⦃ E : Exponential X Y ⦄ → obj
Y ^ X = exp

open import Axiom.UniqueChoice
open import Proposition.Sum using (elem)

cur :
  {X Y Z : obj}
  ⦃ E : Exponential X Y ⦄
  (f : Z × X ~> Y)
  → ----------------
  Z ~> Y ^ X
cur {Z = Z} f = elem (!choice (IsExponential.curry exp-def Z f))
