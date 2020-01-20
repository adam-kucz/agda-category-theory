{-# OPTIONS --exact-split --safe --prop #-}
open import Universes
open import Category

module Construction.Cone.Definition (𝕀 : Category 𝒲 𝒯) where

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  open import Functor
  open import NaturalTransformation
  
  Diagram : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  Diagram = Functor 𝕀 ℂ
  
  Cone : (D : Diagram) (U : obj) → 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  Cone D U = Const 𝕀 U ⟹ D

  open import Proof

  compose-cone-vertex :
    {D : Diagram}{U V : obj}
    (cone : Cone D U)
    (f : V ~> U)
    → ------------------
    Cone D V
  compose-cone-vertex cone f at X = cone at X ∘ f
  naturality ⦃ compose-cone-vertex {D}{U}{V} cone f ⦄ {X}{Y} f₁ =
    proof cone at Y ∘ f ∘ id V
      === cone at Y ∘ f                 :by: right-unit _
      === cone at Y ∘ id U ∘ f           :by: ap (_∘ f) $ sym $ right-unit _
      === F₁ ⦃ D ⦄ f₁ ∘ cone at X ∘ f   :by: ap (_∘ f) $ naturality ⦃ cone ⦄ f₁
      === F₁ ⦃ D ⦄ f₁ ∘ (cone at X ∘ f) :by: sym $ assoc _ _ f
    qed

  compose-cone-diagram :
    {D D' : Diagram}{U : obj}
    (cone : Cone D U)
    (θ : D ⟹ D')
    → ------------------
    Cone D' U
  compose-cone-diagram = flip Composition
    where open import Function using (flip)

open WithFixedCategory public

open import Category.Opposite

Cocone :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  (D : Diagram ⦃ ℂ ᵒᵖ ⦄)
  (U : obj ⦃ ℂ ᵒᵖ ⦄)
   → --------------------
   𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
Cocone ⦃ ℂ ⦄ D U = Cone D U
  where instance _ = ℂ ᵒᵖ
