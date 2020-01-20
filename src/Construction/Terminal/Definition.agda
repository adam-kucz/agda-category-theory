{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category

module Construction.Terminal.Definition ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Category.Empty
open import Functor.Empty
open import Functor.Constant
open import NaturalTransformation.Empty

open import Construction.Cone.Universal ⦃ ℂ ⦄ 𝟘

IsTerminal : (𝟙 : obj) → 𝒰 ⊔ 𝒱 ᵖ
IsTerminal 𝟙 =
  IsUniversalCone {D = EmptyFunctor ℂ} 𝟙 (EmptyNatTrans (Const 𝟘 𝟙))

record Terminal : 𝒰 ⊔ 𝒱 ˙ where
  field
    𝟙 : obj
    ⦃ def ⦄ : IsTerminal 𝟙

open Terminal ⦃ … ⦄ public
