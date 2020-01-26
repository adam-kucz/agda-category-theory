{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category
open import Construction.Cone.Definition

module Construction.Cone.Universal.Instance
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  (𝕀 : Category 𝒰₀ 𝒰₀)
  (A : 𝒲 ˙ → 𝒯 ˙)
  (D : A (Diagram 𝕀))
  where

TerminalCone : (𝟙 : obj) → Cone TerminalDiagram 𝟙
TerminalCone 𝟙 = EmptyNatTrans (Const 𝕀 𝟙)
  where open import Functor.Constant
        open import NaturalTransformation.Empty

open import Construction.Cone.Universal.Definition ⦃ ℂ ⦄ 𝕀

IsTerminal : (𝟙 : obj) → 𝒰 ⊔ 𝒱 ᵖ
IsTerminal 𝟙 = IsUniversalCone 𝟙 (TerminalCone 𝟙)

Terminal : 𝒰 ⊔ 𝒱 ˙
Terminal = UniversalCone TerminalDiagram

𝟙 : ⦃ _ : Terminal ⦄ → obj
𝟙 = U
