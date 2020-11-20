{-# OPTIONS --exact-split --safe --prop #-}
open import Universes
open import Category

module Construction.Cone.Definition (𝕀 : Category 𝒲 𝒯) where

open import Functor.Definition
open import Functor.Construction
open import NaturalTransformation
open import Proof
  
module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  Diagram : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  Diagram = Functor 𝕀 ℂ
  
  Cone : (D : Diagram) (U : obj) → 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  Cone D U = Const 𝕀 U ⟹ D

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

F-cone : ⦃ ℂ : Category 𝒰 𝒱 ⦄
         ⦃ 𝔻 : Category 𝒳 𝒴 ⦄
         {D : Diagram}{U : obj}
         ⦃ F : Functor ℂ 𝔻 ⦄
         (cone : Cone D U)
         → ----------------------------------------
         Cone (F o D) (F₀ U)
F-cone {D = D}{U} ⦃ F ⦄ cone =
  [at= (λ X → F₁ (cone at X))
  ,naturality= (λ {X}{Y} f →
    proof F₁ (cone at Y) ∘ id (F₀ U)
      === F₁ (cone at Y) ∘ F₁ (id U)
        :by: ap (F₁ (cone at Y) ∘_) $ sym $ id-preserv U
      === F₁ (cone at Y ∘ id U)
        :by: sym $ ∘-preserv (cone at Y) (id U)
      === F₁ (F₁ ⦃ D ⦄ f ∘ cone at X)
        :by: ap F₁ $ naturality ⦃ cone ⦄ f
      === F₁ (F₁ ⦃ D ⦄ f) ∘ F₁ (cone at X)
        :by: ∘-preserv (F₁ ⦃ D ⦄ f)(cone at X)
    qed ) ]

open import Category.Opposite
Cocone :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  (D : Diagram ⦃ ℂ ᵒᵖ ⦄)
  (U : obj ⦃ ℂ ᵒᵖ ⦄)
   → --------------------
   𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
Cocone ⦃ ℂ ⦄ D U = Cone D U
  where instance _ = ℂ ᵒᵖ
