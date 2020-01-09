{-# OPTIONS --exact-split --prop --safe #-}
open import Category
open import PropUniverses

module Construction.Product.Definition ⦃ C : Category 𝒰 𝒱 ⦄ where

open import Proposition.Identity
open import Logic

record IsProduct
    (A B : obj)
    (P : obj)
    (π₁ : P ~> A)
    (π₂ : P ~> B)
    : ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  where
  field
    to-product :
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → -------------------------------------------
      ∃! λ (h : X ~> P) → π₁ ∘ h == f ∧ π₂ ∘ h == g

record Product (A B : obj) : 𝒰 ⊔ 𝒱 ˙ where
  field
    object : obj
    π₁ : object ~> A
    π₂ : object ~> B
    ⦃ def ⦄ : IsProduct A B object π₁ π₂

open Product ⦃ … ⦄ public

infixl 180 _×_
_×_ : (A B : obj) ⦃ _ : Product A B ⦄ → obj
A × B = object
  
〈_,_〉 :
  {A B X : obj}
  (f : X ~> A)
  (g : X ~> B)
  ⦃ P : Product A B ⦄
  → ------------------
  ∃! λ (h : X ~> A × B) → π₁ ∘ h == f ∧ π₂ ∘ h == g
〈 f , g 〉 = IsProduct.to-product def f g

