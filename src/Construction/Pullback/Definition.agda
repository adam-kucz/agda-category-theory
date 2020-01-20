{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Category hiding (compose)

module Construction.Pullback.Definition ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Type.Empty
open import Type.Unit
open import Type.BinarySum
open import Proposition.Identity
open import Data.Nat hiding (_⊔_)
open import Data.FinNat
open import Category.Finite

𝕀 : Category 𝒰₀ 𝒰₀
𝕀 = Finite 3 f compose p
  where f : (x y : Finℕ 3) → 𝒰₀ ˙
        f _ (_ +1) = 𝟘
        f ₀ ₀ = 𝟘
        f ₁ ₀ = 𝟙
        f ₂ ₀ = 𝟙
        compose : {X Y Z : Finℕ 3}
          (h : f Y Z)
          (g : f X Y)
          → --------------------
          f+id f X Z
        compose {X}{₀}{₀} ()
        compose {X}{₀}{Z +1} ()
        p : {X Y Z W : Finℕ 3}(h : f Z W)(g : f Y Z)(f₀ : f X Y) →
          ([ f , compose ] inr h o compose g f₀) ==
          ([ f , compose ] compose h g o inr f₀)
        p {X}{₀}{₀}{₀} ()
        p {X}{₀}{Z +1}{₀} _ ()

open import Construction.Cone.Definition ⦃ ℂ ⦄ 𝕀
open import Construction.Cone.Universal ⦃ ℂ ⦄ 𝕀

IsPullback : (D : Diagram)(U : obj)(cone : Cone D U) → 𝒰 ⊔ 𝒱 ᵖ
IsPullback D = IsUniversalCone

record Pullback (D : Diagram) : 𝒰 ⊔ 𝒱 ˙ where
  field
    U : obj
    cone : Cone D U
    ⦃ def ⦄ : IsPullback D U cone

open Pullback ⦃ … ⦄ public
