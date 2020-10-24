{-# OPTIONS --exact-split --prop #-}
module Construction.Property.HasPullbacks where

open import Universes
open import Type.BinarySum
open import Data.FinNat
open import Logic
open import Proof

open import Category
open import NaturalTransformation
open import Construction.Property.PullbackIsEqualizer
open import Construction.Cone.Universal

import Construction.Product as Prod
import Construction.Equalizer as Equal
import Construction.Pullback as Pull
open Prod
open Equal
open Pull hiding (〈_,_〉; p₁; p₂)

has-products-and-equalizers→has-pullbacks :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  ⦃ prods : HasProducts ℂ ⦄
  ⦃ equals : HasEqualizers ℂ ⦄
  → --------------------------------------------------
  HasPullbacks ℂ
has-products-and-equalizers→has-pullbacks
  ⦃ ℂ = ℂ ⦄ ⦃ prods ⦄ ⦃ equals ⦄ {A}{B}{C}{f}{g}
  with record { U = E ; cone = c ; universality = u } ←
    equals {A × B}{C}{f ∘ π₁}{g ∘ π₂} =
  record { U = E
         ; cone = PullbackCone p₁ p₂ fp₁==gp₂
         ; universality = ∧right p }
  where p₁ = π₁ ∘ c at ₀
        p₂ = π₂ ∘ c at ₀
        p : IsPullback f g E p₁ p₂
        fp₁==gp₂ : f ∘ p₁ == g ∘ p₂
        fp₁==gp₂ =
          proof f ∘ p₁
            === f ∘ π₁ ∘ c at ₀   :by: assoc f π₁ (c at ₀)
            === c at ₁ ∘ id E     :by: sym $ naturality ⦃ c ⦄ (inr ₀)
            === g ∘ π₂ ∘ c at ₀   :by: naturality ⦃ c ⦄ (inr ₁)
            === g ∘ p₂            :by: sym $ assoc g π₂ (c at ₀)
          qed
        c₀==〈p₁,p₂〉 : c at ₀ == 〈 p₁ , p₂ 〉
        c₀==〈p₁,p₂〉 =
          proof c at ₀
            === id (A × B) ∘ c at ₀
              :by: sym $ left-unit (c at ₀)
            === 〈 π₁ , π₂ 〉 ∘ c at ₀
              :by: ap (_∘ c at ₀) $ sym 〈π₁,π₂〉==id
            === 〈 π₁ ∘ c at ₀ , π₂ ∘ c at ₀ 〉
              :by: product-compose π₁ π₂ (c at ₀)
          qed
        open import Axiom.FunctionExtensionality
        p = ⟶ (equalizer-pullback f g E p₁ p₂) (
          (proof f ∘ π₁ ∘ 〈 p₁ , p₂ 〉
             === f ∘ (π₁ ∘ 〈 p₁ , p₂ 〉) :by: sym $ assoc f π₁ _
             === f ∘ p₁                :by: ap (f ∘_) $ sym $ π₁-prop p₁ p₂
             === g ∘ p₂                :by: fp₁==gp₂
             === g ∘ (π₂ ∘ 〈 p₁ , p₂ 〉) :by: ap (g ∘_) $ π₂-prop p₁ p₂
             === g ∘ π₂ ∘ 〈 p₁ , p₂ 〉   :by: assoc g π₂ _
           qed) ,
          Id.coe (ap (IsUniversalCone Equal.𝕀 E) $
                  ⟹== c _ $ subrel $ fun-ext λ
                  { ₀ → subrel c₀==〈p₁,p₂〉
                  ; ₁ → subrel (
                  proof c at ₁
                    === c at ₁ ∘ id E   :by: sym $ right-unit (c at ₁)
                    === f ∘ π₁ ∘ c at ₀ :by: naturality ⦃ c ⦄ (inr ₀)
                    === f ∘ π₁ ∘ 〈 p₁ , p₂ 〉
                      :by: ap (f ∘ π₁ ∘_) c₀==〈p₁,p₂〉 [: _==_ ]
                  qed)}) u)
        
