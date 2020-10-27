{-# OPTIONS --exact-split --prop #-}
module Construction.Product.AsUniversalCone where

import Construction.Product.Definition as P

open import PropUniverses
open import Category hiding (compose)

open import Type.Empty
import Data.Nat.Syntax using (Natℕ)
open import Data.FinNat
open import Category.Finite

𝕀 : Category 𝒰₀ 𝒰₀
𝕀 = Finite 2 (λ _ _ → 𝟘) (λ ()) (λ ())

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
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

  PProduct→Product : {A B : obj}(P : P.Product A B) → Product A B
  PProduct→Product {A}{B} P@(_ , p) =
    record { U = A P.× B ; cone = cone' ; universality = univ p }
    where instance _ = P
          cone' = ProductCone P.π₁ P.π₂
          univ : P.IsProduct A B (A P.× B) P.π₁ P.π₂
                 → ----------------------------------------
                 IsUniversalCone (A P.× B) cone'
          to-universal ⦃ univ q ⦄ c
            with f , (p₁ , p₂ , !f) ← q (c at ₀)(c at ₁) =
            f , ((λ { ₀ → sym p₁ ; ₁ → sym p₂}) ,
                 λ f' p' → !f f' (sym (p' ₀) , sym (p' ₁)))

  open import Type.Sum renaming (_,_ to _Σ,_) hiding (_×_)

  Product→PProduct : {A B : obj}(P : Product A B) → P.Product A B
  Product→PProduct {A}{B} P =
    V Σ, (π₁ Σ, π₂) , λ f g → go f g  $ to-universal (c f g)
    where instance _ = P
          V = A × B
          c = ProductCone
          go : {V' : obj}(f' : V' ~> A)(g' : V' ~> B)
               (p : ∃! λ (f : V' ~> V) → ∀ X → c f' g' at X == cone at X ∘ f)
               → ----------------------------------------------------------
               ∃! λ (!f : V' ~> V) → π₁ ∘ !f == f' ∧ π₂ ∘ !f == g'
          go f' g' (f , (p , !f)) =
            f , (sym (p ₀) , sym (p ₁) ,
                 λ { f″ (p₀″ , p₁″) → !f f″ λ { ₀ → sym p₀″ ; ₁ → sym p₁″}})

          
  
  open import Morphism.Iso
  
  Product≅ : {A B : obj}
    (P : Product A B)
    (P' : P.Product A B)
    → --------------------
    let instance _ = P; _ = P' in
    A × B ≅ A P.× B
  Product≅ P P'@(_ Σ, (π₁' Σ, π₂') , p)
    with p π₁ π₂ | to-universal (ProductCone P.π₁ P.π₂)
       | p P.π₁ P.π₂ | to-universal (ProductCone π₁ π₂)
    where instance _ = P; _ = P'
  ... | f , (pf₁ , pf₂ , !f) | f⁻¹ , (pf⁻¹ , !f⁻¹) | !id | !id' =
    f , (f⁻¹ , (
    ∃!== !id
      ((proof π₁' ∘ (f ∘ f⁻¹)
          === π₁' ∘ f ∘ f⁻¹ :by: assoc π₁' f f⁻¹
          === π₁ ∘ f⁻¹      :by: ap (_∘ f⁻¹) pf₁
          === π₁'           :by: sym $ pf⁻¹ ₀
        qed) ,
       (proof π₂' ∘ (f ∘ f⁻¹)
          === π₂' ∘ f ∘ f⁻¹ :by: assoc π₂' f f⁻¹
          === π₂ ∘ f⁻¹      :by: ap (_∘ f⁻¹) pf₂
          === π₂'           :by: sym $ pf⁻¹ ₁
        qed))
      (right-unit _ , right-unit _) ,
    ∃!== !id' (λ { ₀ → proof π₁
                         === π₁' ∘ f        :by: sym pf₁
                         === π₁ ∘ f⁻¹ ∘ f   :by: ap (_∘ f) $ pf⁻¹ ₀
                         === π₁ ∘ (f⁻¹ ∘ f) :by: sym $ assoc π₁ f⁻¹ f
                       qed
                 ; ₁ → proof π₂
                         === π₂' ∘ f        :by: sym pf₂
                         === π₂ ∘ f⁻¹ ∘ f   :by: ap (_∘ f) $ pf⁻¹ ₁
                         === π₂ ∘ (f⁻¹ ∘ f) :by: sym $ assoc π₂ f⁻¹ f
                       qed})
              λ { ₀ → sym $ right-unit π₁
                ; ₁ → sym $ right-unit π₂}))
    where instance _ = P; _ = P'

open WithFixedCategory public

HasProducts : (ℂ : Category 𝒲 𝒯) → 𝒲 ⊔ 𝒯 ˙
HasProducts ℂ = ∀ {A B : obj} → Product A B
  where instance _ = ℂ

