{-# OPTIONS --exact-split --prop #-}
module Construction.Product.Definition where

open import PropUniverses
open import Category hiding (compose)

open import Type.Empty
import Data.Nat.Syntax using (Natℕ)
open import Data.FinNat
open import Category.Finite

𝕀 : Category 𝒰₀ 𝒰₀
𝕀 = Finite 2 (λ _ _ → 𝟘) (λ ()) (λ ())

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

  open import Proposition.Identity
    renaming (Idₚ to Id) hiding (refl)
  open import Construction.Cone.Definition 𝕀
    
  open import Functor
  open import Type.BinarySum
  open import Type.Unit
  open import Proposition.Sum
  open import Proof
  
  ProductDiagram : (A B : obj) → Diagram
  F₀ ⦃ ProductDiagram A B ⦄ ₀ = A
  F₀ ⦃ ProductDiagram A B ⦄ ₁ = B
  F₁ ⦃ ProductDiagram A B ⦄ {₀}{₀}(inl _) = id A
  F₁ ⦃ ProductDiagram A B ⦄ {₁}{₁}(inl _) = id B
  id-preserv ⦃ ProductDiagram A B ⦄ ₀ = refl (id A)
  id-preserv ⦃ ProductDiagram A B ⦄ ₁ = refl (id B)
  ∘-preserv ⦃ ProductDiagram A B ⦄ {₀}{₀}{₀}
    f@(inl (⋆ , Id.refl ₀))f@(inl (⋆ , Id.refl ₀)) =
      let F1 = F₁ ⦃ ProductDiagram A B ⦄ in
      proof F1 (f ∘ f)
        〉 _==_ 〉 id A        :by: ap F1 $ left-unit f
        〉 _==_ 〉 id A ∘ id A :by: sym $ left-unit (id A)
      qed
    where instance _ = 𝕀
  ∘-preserv ⦃ ProductDiagram A B ⦄ {₁}{₁}{₁}
    f@(inl (⋆ , Id.refl ₁))f@(inl (⋆ , Id.refl ₁)) =
      let F1 = F₁ ⦃ ProductDiagram A B ⦄ in
      proof F1 (f ∘ f)
        〉 _==_ 〉 id B        :by: ap F1 $ left-unit f
        〉 _==_ 〉 id B ∘ id B :by: sym $ left-unit (id B)
      qed
    where instance _ = 𝕀
  
  open import NaturalTransformation
  
  ProductCone :
    {A B : obj}
    {X : obj}
    (f : X ~> A)
    (g : X ~> B)
    → -------------------------
    Cone (ProductDiagram A B) X
  ProductCone f g at ₀ = f
  ProductCone f g at ₁ = g
  naturality ⦃ ProductCone f g ⦄ (inl (_ , Id.refl ₀)) = sym $ bi-unit f
  naturality ⦃ ProductCone f g ⦄ (inl (_ , Id.refl ₁)) = sym $ bi-unit g
  
  open import Construction.Cone.Universal.Definition ⦃ ℂ ⦄ 𝕀
  
  IsProduct :
    (A B : obj)
    (P : obj)
    (π₁ : P ~> A)
    (π₂ : P ~> B)
    → ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  IsProduct _ _ P π₁ π₂ = IsUniversalCone P (ProductCone π₁ π₂)
  
  Product : (A B : obj) → 𝒰 ⊔ 𝒱 ˙
  Product A B = UniversalCone (ProductDiagram A B)
  
  infixl 181 _×_ 
  _×_ : (A B : obj) ⦃ P : Product A B ⦄ → obj
  (A × B) = U
  
  π₁ : {A B : obj} ⦃ P : Product A B ⦄ → A × B ~> A
  π₁ = cone at ₀
  π₂ : {A B : obj} ⦃ P : Product A B ⦄ → A × B ~> B
  π₂ = cone at ₁
  
  module Display where
    {-# DISPLAY _at_ P ₀ = π₁ #-}
    {-# DISPLAY _at_ P ₁ = π₂ #-}
  
  open import Logic
  
  〈_,_〉 :
    {A B X : obj}
    (f : X ~> A)
    (g : X ~> B)
    ⦃ P : Product A B ⦄
    → ------------------
    ∃! λ (h : X ~> A × B) → f == π₁ ∘ h ∧ g == π₂ ∘ h
  〈_,_〉 {A}{B}{X} f g ⦃ P ⦄ with to-universal (ProductCone f g)
  〈_,_〉 {A} {B} {X} f g ⦃ P ⦄ | h , (nat , uniq) =
    h ,
    (nat ₀ , nat ₁ ,
     λ { h' (f==π₁∘h' , g==π₂∘h') →
       uniq h' λ { ₀ → f==π₁∘h' ; ₁ → g==π₂∘h'}})

open WithFixedCategory public
