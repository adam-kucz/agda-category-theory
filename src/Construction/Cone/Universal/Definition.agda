{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category

module Construction.Cone.Universal.Definition
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  (𝕀 : Category 𝒲 𝒯)
  where

open import NaturalTransformation
open import Construction.Cone.Definition 𝕀

open import Proposition.Identity hiding (refl)
open import Logic

record IsUniversalCone
    {D : Diagram}
    (U : obj)
    (cone : Cone D U)
    : ----------------------
    𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
    where
  field
    to-universal : ∀ {V} (c : Cone D V)
      → ------------------------------
      ∃! λ (f : V ~> U) → ∀ X →
        c at X == cone at X ∘ f

open IsUniversalCone ⦃ … ⦄ public

record UniversalCone D : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙ where
  field
    U : obj
    cone : Cone D U
    ⦃ universality ⦄ : IsUniversalCone U cone

open UniversalCone ⦃ … ⦄ public

-- open import Function using (Bijection)

-- record Limit (D : Diagram) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙ where
--   field
--     U : obj
--     cone : Cone D U
--     bijection : ∀ V → Bijection (V ~> U) (Cone D V)
--     naturality : {!!}
