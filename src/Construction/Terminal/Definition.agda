{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category

module Construction.Terminal.Definition ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

𝕀 : Category 𝒰₀ 𝒰₀
𝕀 = 𝟘
  where open import Category.Empty

open import Construction.Cone.Definition 𝕀

TerminalDiagram : Diagram
TerminalDiagram = EmptyFunctor ℂ
  where open import Functor.Empty

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

global-element-of point-of constant-of : ⦃ _ : Terminal ⦄ (X : obj) → 𝒱 ˙
global-element-of = 𝟙 ~>_
point-of = global-element-of
constant-of = global-element-of
