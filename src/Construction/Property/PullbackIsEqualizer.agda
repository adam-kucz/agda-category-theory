{-# OPTIONS --exact-split --prop #-}
module Construction.Property.PullbackIsEqualizer where

import Construction.Product as Prod
import Construction.Equalizer as Equal
import Construction.Pullback as Pull
open Prod
open Equal
open Pull hiding (〈_,_〉)

open import Universes
open import Type.BinarySum
open import Type.Unit
open import Data.FinNat
open import Logic
open import Proof

open import Category
open import NaturalTransformation
open import Construction.Cone
open import Construction.Cone.Universal

equalizer-pullback : ⦃ ℂ : Category 𝒰 𝒱 ⦄
  {A B C : obj}
  (f : A ~> C)
  (g : B ~> C)
  ⦃ P : Product A B ⦄
  (E : obj)
  (p₀ : E ~> A)
  (p₁ : E ~> B)
  → ----------------------------------------
  IsEqualizer (f ∘ π₁) (g ∘ π₂) E 〈 p₀ , p₁ 〉 ↔ IsPullback f g E p₀ p₁
⟶ (equalizer-pullback f g E p₀ p₁) (q , ucone) =
  fp₀==gp₁ , record { to-universal = ump }
  where fp₀==gp₁ : f ∘ p₀ == g ∘ p₁
        fp₀==gp₁ =
          proof f ∘ p₀
            === f ∘ (π₁ ∘ 〈 p₀ , p₁ 〉) :by: ap (f ∘_) $ π₁-prop p₀ p₁
            === f ∘ π₁ ∘ 〈 p₀ , p₁ 〉   :by: assoc f π₁ _
            === g ∘ π₂ ∘ 〈 p₀ , p₁ 〉   :by: q
            === g ∘ (π₂ ∘ 〈 p₀ , p₁ 〉) :by: sym $ assoc g π₂ _
            === g ∘ p₁                :by: ap (g ∘_) $ sym $ π₂-prop p₀ p₁
          qed
        pbcone = PullbackCone p₀ p₁ fp₀==gp₁
        ump :  ∀ {V : obj}(c : Cone Pull.𝕀 (PullbackDiagram f g) V)
          → ------------------------------
          ∃! λ (f : V ~> E) → ∀ X →
          c at X == pbcone at X ∘ f
        ump {V} c = go (to-universal ⦃ r = ucone ⦄ c')
          where c' : Cone Equal.𝕀 (EqualizerDiagram (f ∘ π₁) (g ∘ π₂)) V
                go :
                  (∃! λ f' → ∀ X →
                   c' at X == EqualizerCone 〈 p₀ , p₁ 〉 q at X ∘ f')
                  → -------------------------------------------------
                  ∃! λ (f' : V ~> E) → ∀ X →
                  c at X == pbcone at X ∘ f'
                c' = [at= (λ { ₀ → 〈 c at ₁ , c at ₂ 〉
                             ; ₁ → c at ₀})
                     ,naturality= (λ
                     { {₀} {₁} (inr ₀) →
                       proof c at ₀ ∘ id V
                         === f ∘ c at ₁    :by: naturality ⦃ c ⦄ (inr ⋆)
                         === f ∘ (π₁ ∘ 〈 c at ₁ , c at ₂ 〉)
                           :by: ap (f ∘_) $ π₁-prop (c at ₁)(c at ₂)
                         === f ∘ π₁ ∘ 〈 c at ₁ , c at ₂ 〉
                           :by: assoc f π₁ _
                       qed
                     ; {₀} {₁} (inr ₁) →
                       proof c at ₀ ∘ id V
                         === g ∘ c at ₂    :by: naturality ⦃ c ⦄ (inr ⋆)
                         === g ∘ (π₂ ∘ 〈 c at ₁ , c at ₂ 〉)
                           :by: ap (g ∘_) $ π₂-prop (c at ₁)(c at ₂)
                         === g ∘ π₂ ∘ 〈 c at ₁ , c at ₂ 〉
                           :by: assoc g π₂ _
                       qed
                     ; {₀} {₀} _ → sym $ bi-unit 〈 c at ₁ , c at ₂ 〉
                     ; {₁} {₁} _ → sym $ bi-unit (c at ₀)
                     ; {₁} {₀} (inl ())
                     ; {₁} {₀} (inr ())
                     })]
                go = ⟶ (↔→∃!↔∃! λ f' →
                  (λ { p ₀ → proof c at ₀
                               === c' at ₁                  :by: Id.refl _
                               === f ∘ π₁ ∘ 〈 p₀ , p₁ 〉 ∘ f' :by: p ₁
                               === f ∘ (π₁ ∘ 〈 p₀ , p₁ 〉) ∘ f'
                                 :by: ap (_∘ f') $ sym $ assoc f π₁ _
                               === f ∘ p₀ ∘ f'
                                 :by: ap (λ — → f ∘ — ∘ f') $ sym $
                                      π₁-prop p₀ p₁
                             qed
                     ; p ₁ → proof c at ₁
                               === π₁ ∘ 〈 c at ₁ , c at ₂ 〉
                                 :by: π₁-prop (c at ₁)(c at ₂)
                               === π₁ ∘ (〈 p₀ , p₁ 〉 ∘ f')
                                 :by: ap (π₁ ∘_) $ p ₀
                               === π₁ ∘ 〈 p₀ , p₁ 〉 ∘ f' :by: assoc π₁ _ f'
                               === p₀ ∘ f'
                                 :by: ap (_∘ f') $ sym $ π₁-prop p₀ p₁
                             qed
                     ; p ₂ → proof c at ₂
                               === π₂ ∘ 〈 c at ₁ , c at ₂ 〉
                                 :by: π₂-prop (c at ₁)(c at ₂)
                               === π₂ ∘ (〈 p₀ , p₁ 〉 ∘ f')
                                 :by: ap (π₂ ∘_) $ p ₀
                               === π₂ ∘ 〈 p₀ , p₁ 〉 ∘ f' :by: assoc π₂ _ f'
                               === p₁ ∘ f'
                                 :by: ap (_∘ f') $ sym $ π₂-prop p₀ p₁
                             qed}) ,
                  λ { p ₀ → proof 〈 c at ₁ , c at ₂ 〉
                              === 〈 p₀ ∘ f' , p₁ ∘ f' 〉
                                :by: ap2 〈_,_〉 (p ₁) (p ₂)
                              === 〈 p₀ , p₁ 〉 ∘ f'
                                :by: sym $ product-compose p₀ p₁ f'
                            qed 
                    ; p ₁ → proof c at ₀
                              === f ∘ p₀ ∘ f'  :by: p ₀
                              === f ∘ (π₁ ∘ 〈 p₀ , p₁ 〉) ∘ f'
                                :by: ap (λ — → f ∘ — ∘ f') $ π₁-prop p₀ p₁
                              === f ∘ π₁ ∘ 〈 p₀ , p₁ 〉 ∘ f'
                                :by: ap (_∘ f') $ assoc f π₁ _
                            qed})
⟵ (equalizer-pullback f g E p₀ p₁) (q , ucone) =
  fπ〈〉==gπ〈〉 , record { to-universal = ump }
  where fπ〈〉==gπ〈〉 : f ∘ π₁ ∘ 〈 p₀ , p₁ 〉 == g ∘ π₂ ∘ 〈 p₀ , p₁ 〉
        fπ〈〉==gπ〈〉 = proof f ∘ π₁ ∘ 〈 p₀ , p₁ 〉
                     === f ∘ (π₁ ∘ 〈 p₀ , p₁ 〉) :by: sym $ assoc f π₁ _
                     === f ∘ p₀
                       :by: ap (f ∘_) $ sym $ π₁-prop p₀ p₁
                     === g ∘ p₁                :by: q
                     === g ∘ (π₂ ∘ 〈 p₀ , p₁ 〉)
                       :by: ap (g ∘_) $ π₂-prop p₀ p₁
                     === g ∘ π₂ ∘ 〈 p₀ , p₁ 〉   :by: assoc g π₂ _
                   qed
        eqcone = EqualizerCone 〈 p₀ , p₁ 〉 fπ〈〉==gπ〈〉
        ump :  ∀ {V : obj}
          (c : Cone Equal.𝕀 (EqualizerDiagram (f ∘ π₁) (g ∘ π₂)) V)
          → ------------------------------
          ∃! λ (f : V ~> E) → ∀ X →
          c at X == eqcone at X ∘ f
        ump {V} c = go (to-universal ⦃ r = ucone ⦄ c')
          where c' : Cone Pull.𝕀 (PullbackDiagram f g) V
                go :
                  (∃! λ f' → ∀ X →
                   c' at X == PullbackCone p₀ p₁ q at X ∘ f')
                  → -------------------------------------------------
                  ∃! λ (f' : V ~> E) → ∀ X →
                  c at X == eqcone at X ∘ f'
                c' = [at= (λ { ₀ → c at ₁
                             ; ₁ → π₁ ∘ c at ₀
                             ; ₂ → π₂ ∘ c at ₀})
                     ,naturality= (λ
                     { {₀} {₀} _ → sym $ bi-unit (c at ₁)
                     ; {₁} {₁} _ → sym $ bi-unit (π₁ ∘ c at ₀)
                     ; {₂} {₂} _ → sym $ bi-unit (π₂ ∘ c at ₀)
                     ; {₁} {₀} _ →
                       proof c at ₁ ∘ id V
                         === f ∘ π₁ ∘ c at ₀   :by: naturality ⦃ c ⦄ (inr ₀)
                         === f ∘ (π₁ ∘ c at ₀) :by: sym $ assoc f π₁ _
                       qed
                     ; {₂} {₀} _ →
                       proof c at ₁ ∘ id V
                         === g ∘ π₂ ∘ c at ₀   :by: naturality ⦃ c ⦄ (inr ₁)
                         === g ∘ (π₂ ∘ c at ₀) :by: sym $ assoc g π₂ _
                       qed
                     ; {₁} {₂} (inl ())
                     ; {₁} {₂} (inr ())
                     ; {₂} {₁} (inl ())
                     ; {₂} {₁} (inr ())
                     ; {₀} {_ +1} (inl ())
                     ; {₀} {_ +1} (inr ())
                     })]
                go = ⟶ (↔→∃!↔∃! λ f' →
                  (λ p → λ
                   { ₀ → proof c at ₀
                           === id _ ∘ c at ₀   :by: sym $ left-unit _
                           === 〈 π₁ , π₂ 〉 ∘ c at ₀
                             :by: ap (_∘ c at ₀) $ sym 〈π₁,π₂〉==id
                           === 〈 π₁ ∘ c at ₀ , π₂ ∘ c at ₀ 〉
                             :by: product-compose π₁ π₂ (c at ₀)
                           === 〈 p₀ ∘ f' , p₁ ∘ f' 〉
                             :by: ap2 〈_,_〉 (p ₁) (p ₂)
                           === 〈 p₀ , p₁ 〉 ∘ f'
                             :by: sym $ product-compose p₀ p₁ f'
                         qed
                   ; ₁ → proof c' at ₀
                           === f ∘ p₀ ∘ f'    :by: p ₀
                           === f ∘ (π₁ ∘ 〈 p₀ , p₁ 〉) ∘ f'
                             :by: ap (λ — → f ∘ — ∘ f') $ π₁-prop p₀ p₁
                           === f ∘ π₁ ∘ 〈 p₀ , p₁ 〉 ∘ f'
                             :by: ap (_∘ f') $ assoc f π₁ 〈 p₀ , p₁ 〉
                         qed}) ,
                  λ p → λ
                   { ₀ → proof c' at ₀
                           === f ∘ π₁ ∘ 〈 p₀ , p₁ 〉 ∘ f' :by: p ₁
                           === f ∘ (π₁ ∘ 〈 p₀ , p₁ 〉) ∘ f'
                             :by: ap (_∘ f') $ sym $ assoc f π₁ 〈 p₀ , p₁ 〉
                           === f ∘ p₀ ∘ f'
                             :by: ap (λ — → f ∘ — ∘ f') $ sym $
                                  π₁-prop p₀ p₁
                         qed
                   ; ₁ → proof π₁ ∘ c at ₀
                           === π₁ ∘ (〈 p₀ , p₁ 〉 ∘ f') :by: ap (π₁ ∘_) $ p ₀
                           === π₁ ∘ 〈 p₀ , p₁ 〉 ∘ f'   :by: assoc π₁ _ f'
                           === p₀ ∘ f' :by: ap (_∘ f') $ sym $ π₁-prop p₀ p₁
                         qed
                   ; ₂ → proof π₂ ∘ c at ₀
                           === π₂ ∘ (〈 p₀ , p₁ 〉 ∘ f') :by: ap (π₂ ∘_) $ p ₀
                           === π₂ ∘ 〈 p₀ , p₁ 〉 ∘ f'   :by: assoc π₂ _ f'
                           === p₁ ∘ f' :by: ap (_∘ f') $ sym $ π₂-prop p₀ p₁
                         qed})
