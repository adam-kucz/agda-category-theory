{-# OPTIONS --exact-split --prop #-}
module Construction.Coproduct.Definition where

import Construction.Product.Definition as Prod
open Prod using (𝕀) public

open import Universes
open import Category

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

  open import Logic
  open import Proposition.Identity

  open import Construction.Cone.Definition 𝕀
    using (Diagram; Cocone)
  open import Category.Opposite
  open Prod
    using (ProductDiagram; ProductCone; IsProduct
          ; Product; _×_; π₁; π₂; 〈_,_〉)
  
  CoproductDiagram : (A B : obj) → Diagram ⦃ ℂ ᵒᵖ ⦄
  CoproductDiagram = ProductDiagram ⦃ ℂ ᵒᵖ ⦄

  CoproductCocone :
    {A B : obj}
    {X : obj}
    (f : A ~> X)
    (g : B ~> X)
    → -------------------------
    Cocone (CoproductDiagram A B) X
  CoproductCocone = CorpoductCocone' ℂ
    where CorpoductCocone' = dual (λ ℂ {A}{B}{X} → ProductCone ⦃ ℂ ⦄{A}{B}{X})
  
  IsCoproduct = IsCoproduct' ℂ
    where IsCoproduct' = dual (λ ℂ → IsProduct ⦃ ℂ ⦄)
  
  Coproduct = Coproduct' ℂ
    where Coproduct' = dual (λ ℂ → Product ⦃ ℂ ⦄)
  
  infixl 180 _+_
  _+_ : (A B : obj) ⦃ P : Coproduct A B ⦄ → obj
  _+_ = _×_ ⦃ ℂ ᵒᵖ ⦄
  inl : {A B : obj} ⦃ P : Coproduct A B ⦄ → A ~> A + B
  inl = π₁ ⦃ ℂ ᵒᵖ ⦄
  inr : {A B : obj} ⦃ P : Coproduct A B ⦄ → B ~> A + B
  inr = π₂ ⦃ ℂ ᵒᵖ ⦄
  [_,_] :
    {A B X : obj}
    (f : A ~> X)
    (g : B ~> X)
    ⦃ P : Coproduct A B ⦄
    → --------------------
    ∃! λ (h : A + B ~> X) → f == h ∘ inl ∧ g == h ∘ inr
  [_,_] = 〈_,_〉 ⦃ ℂ ᵒᵖ ⦄

  open import NaturalTransformation

  module Display where
    {-# DISPLAY _at_ P ₀ = inl #-}
    {-# DISPLAY _at_ P ₁ = inr #-}
  
open WithFixedCategory public

