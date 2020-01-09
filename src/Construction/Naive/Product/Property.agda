{-# OPTIONS --exact-split --prop --safe #-}
open import PropUniverses
open import Category

module Construction.Product.Property where

import Construction.Product.Definition as Prod

HasProducts : (ℂ : Category 𝒲 𝒯) → 𝒲 ⊔ 𝒯 ˙
HasProducts ℂ = ∀ {A B : obj} → Product A B
  where open Prod
        instance _ = ℂ

open import Proposition.Identity
open import Logic
open import Proof

module UniqueIso ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  open Prod ⦃ ℂ ⦄

  products-unique-upto-unique-iso :
    {A B : obj}
    (P P' : Product A B)
    → ----------------------------
    ∃! λ (f : (A × B) ⦃ P ⦄ ~> (A × B) ⦃ P' ⦄) →
      iso f ∧
      π₁ ⦃ P' ⦄ ∘ f == π₁ ⦃ P ⦄ ∧
      π₂ ⦃ P' ⦄ ∘ f == π₂ ⦃ P ⦄
  products-unique-upto-unique-iso P P'
    with 〈 π₁ ⦃ P ⦄ , π₂ ⦃ P ⦄ 〉 ⦃ P ⦄
       | 〈 π₁ ⦃ P ⦄ , π₂ ⦃ P ⦄ 〉 ⦃ P' ⦄
       | 〈 π₁ ⦃ P' ⦄ , π₂ ⦃ P' ⦄ 〉 ⦃ P ⦄
       | 〈 π₁ ⦃ P' ⦄ , π₂ ⦃ P' ⦄ 〉 ⦃ P' ⦄
  products-unique-upto-unique-iso {A} {B} P P'
    | P→P , (π₁∘h₀ , π₂∘h₀ , uniq₀)
    | P→P' , (π₁∘h₁ , π₂∘h₁ , uniq₁)
    | P'→P , (π₁∘h₂ , π₂∘h₂ , uniq₂)
    | P'→P' , (π₁∘h₃ , π₂∘h₃ , uniq₃) =
    P→P' ,
    ((P'→P ,
      ((proof P→P' ∘ P'→P
          〉 _==_ 〉 P'→P'
            :by: uniq₃ (P→P' ∘ P'→P) (
              (proof π1' ∘ (P→P' ∘ P'→P)
                 〉 _==_ 〉 π1' ∘ P→P' ∘ P'→P :by: assoc π1' P→P' P'→P
                 〉 _==_ 〉 π1 ∘ P'→P        :by: ap (_∘ P'→P) π₁∘h₁
                 〉 _==_ 〉 π1'              :by: π₁∘h₂
               qed) ,
              (proof π2' ∘ (P→P' ∘ P'→P)
                 〉 _==_ 〉 π2' ∘ P→P' ∘ P'→P :by: assoc π2' P→P' P'→P
                 〉 _==_ 〉 π2 ∘ P'→P        :by: ap (_∘ P'→P) π₂∘h₁
                 〉 _==_ 〉 π2'              :by: π₂∘h₂
               qed))
          〉 _==_ 〉 ID'
            :by: sym $ uniq₃ ID' (right-unit π1' , right-unit π2')
        qed) ,
       (proof P'→P ∘ P→P'
          〉 _==_ 〉 P→P
            :by: uniq₀ (P'→P ∘ P→P') (
              (proof π1 ∘ (P'→P ∘ P→P')
                 〉 _==_ 〉 π1 ∘ P'→P ∘ P→P' :by: assoc π1 P'→P P→P'
                 〉 _==_ 〉 π1' ∘ P→P'       :by: ap (_∘ P→P') π₁∘h₂
                 〉 _==_ 〉 π1              :by: π₁∘h₁
               qed) ,
              (proof π2 ∘ (P'→P ∘ P→P')
                 〉 _==_ 〉 π2 ∘ P'→P ∘ P→P' :by: assoc π2 P'→P P→P'
                 〉 _==_ 〉 π2' ∘ P→P'       :by: ap (_∘ P→P') π₂∘h₂
                 〉 _==_ 〉 π2               :by: π₂∘h₁
               qed))
          〉 _==_ 〉 ID
            :by: sym $ uniq₀ ID (right-unit π1 , right-unit π2)
        qed)) ,
      π₁∘h₁ , π₂∘h₁) ,
     λ { f (_ , p₀ , p₁) → uniq₁ f (p₀ , p₁) })
    where π1  = π₁ ⦃ P ⦄
          π1' = π₁ ⦃ P' ⦄
          π2  = π₂ ⦃ P ⦄
          π2' = π₂ ⦃ P' ⦄
          ID = id ((A × B) ⦃ P ⦄)
          ID' = id ((A × B) ⦃ P' ⦄)

open UniqueIso public
