{-# OPTIONS --exact-split --safe --prop #-}
module Construction.Product.Definition where

open import PropUniverses
open import Type.Sum renaming (_,_ to _Σ,_; _×_ to _x_) hiding (〈_,_〉)
open import Logic

open import Category

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  open import Proposition.Sum
  open import Proposition.Identity
  
  IsProduct :
    (A B : obj)
    (P : obj)
    (π₁ : P ~> A)
    (π₂ : P ~> B)
    → ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  IsProduct A B P π₁ π₂ =
    ∀{X : obj}(f : X ~> A)(g : X ~> B) →
    ∃! λ (〈f,g〉 : X ~> P) →
    π₁ ∘ 〈f,g〉 == f ∧
    π₂ ∘ 〈f,g〉 == g
  
  Product : (A B : obj) → 𝒰 ⊔ 𝒱 ˙
  Product A B = Σₚ {X = Σ λ (P : obj) → P ~> A x P ~> B }
                   λ { (P Σ, (π₁ Σ, π₂)) → IsProduct A B P π₁ π₂}
  
  infixl 181 _×_ 
  _×_ : (A B : obj) ⦃ P : Product A B ⦄ → obj
  (A × B) ⦃ P Σ, _ , _ ⦄ = P
  
  π₁ : {A B : obj} ⦃ P : Product A B ⦄ → A × B ~> A
  π₁ ⦃ _ Σ, (π₁ Σ, _) , _ ⦄ = π₁
  π₂ : {A B : obj} ⦃ P : Product A B ⦄ → A × B ~> B
  π₂ ⦃ _ Σ, (_ Σ, π₂) , _ ⦄ = π₂
  
  〈_,_〉 :
    {A B X : obj}
    (f : X ~> A)
    (g : X ~> B)
    ⦃ P : Product A B ⦄
    → ------------------
    ∃! λ (h : X ~> A × B) → π₁ ∘ h == f  ∧ π₂ ∘ h == g
  〈 f , g 〉 ⦃ _ , p ⦄ = p f g

open WithFixedCategory public

HasProducts : (ℂ : Category 𝒲 𝒯) → 𝒲 ⊔ 𝒯 ˙
HasProducts ℂ = ∀ {A B : obj} → Product A B
  where instance _ = ℂ

open import Construction.Terminal

HasAllFiniteProducts : (ℂ : Category 𝒲 𝒯) → 𝒲 ⊔ 𝒯 ˙
HasAllFiniteProducts ℂ = Terminal x HasProducts ℂ
  where instance _ = ℂ

