{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Category

module Construction.Pullback.AsUniversalCone.Equivalence
  ⦃ ℂ : Category 𝒰 𝒱 ⦄{A B C : obj} where

open import Type.BinarySum
open import Type.Unit
open import Data.FinNat
open import Proof

open import Construction.Pullback.AsUniversalCone.Definition
open import Construction.Cone.Definition 𝕀
open import Construction.Cone.Universal.Definition ⦃ ℂ ⦄ 𝕀
open import NaturalTransformation

ConePull-prop : {f : A ~> C}{g : B ~> C}{V : obj}
  (cone : Cone (PullbackDiagram f g) V)
  → -----------------------------------------------------
  f ∘ cone at ₁ == g ∘ cone at ₂
ConePull-prop {f}{g}{V} cone =
  proof f ∘ cone at ₁
    === cone at ₀ ∘ id V :by: sym $ naturality (inr ⋆)
    === g ∘ cone at ₂    :by: naturality (inr ⋆)
  qed
  where instance _ = cone

open import Logic

import Construction.Pullback.Definition as P
import Construction.Pullback.Syntax as SP

PIsPullback↔IsPullback :
  (f : A ~> C)
  (g : B ~> C)
  (P : obj)
  (p₀ : P ~> A)
  (p₁ : P ~> B)
  → ---------------------
  P.IsPullback f g P p₀ p₁ ↔ IsPullback f g P p₀ p₁
⟶ (PIsPullback↔IsPullback f g P p₀ p₁) (fp₀==gp₁ , ∃!〈p₀,p₁〉) =
  fp₀==gp₁ , record { to-universal = λ c →
  case ∃!〈p₀,p₁〉 (c at ₁)(c at ₂)(ConePull-prop c) of
  λ { (〈c₁,c₂〉 , (p₀〈c₁,c₂〉==c₁ , p₁〈c₁,c₂〉==c₂ , !〈c₁,c₂〉)) →
       〈c₁,c₂〉 , (
         (λ { ₀ → proof c at ₀
                    === c at ₀ ∘ id _     :by: sym $ right-unit (c at ₀) 
                    === f ∘ c at ₁        :by: naturality ⦃ c ⦄ (inr ⋆) 
                    === f ∘ (p₀ ∘ 〈c₁,c₂〉) :by: ap (f ∘_) $ sym p₀〈c₁,c₂〉==c₁
                    === f ∘ p₀ ∘ 〈c₁,c₂〉   :by: assoc f p₀ 〈c₁,c₂〉
                  qed
            ; ₁ → sym p₀〈c₁,c₂〉==c₁ 
            ; ₂ → sym p₁〈c₁,c₂〉==c₂}) ,
         λ u' pu → !〈c₁,c₂〉 u' (sym (pu ₁) , sym (pu ₂)))}}
⟵ (PIsPullback↔IsPullback f g P p₀ p₁) (fp₀==gp₁ , univ) =
  fp₀==gp₁ , λ p₀' p₁' q →
  case to-universal ⦃ univ ⦄ (PullbackCone p₀' p₁' q) of
  λ { (u , (p , !u)) → u , (sym (p ₁) , sym (p ₂) ,
    λ {u' (p₀u'==p₀' , p₁u'==p₁') → !u u' λ
      { ₀ → proof f ∘ p₀'
              === f ∘ (p₀ ∘ u') :by: ap (f ∘_) $ sym p₀u'==p₀'
              === f ∘ p₀ ∘ u'   :by: assoc f p₀ u'
            qed
      ; ₁ → sym p₀u'==p₀'
      ; ₂ → sym p₁u'==p₁'}})}

PPullback→Pullback : {f : A ~> C}{g : B ~> C}
  (P : P.Pullback f g) → Pullback f g
PPullback→Pullback {f}{g} P@(_ , p@(fp₁==gp₂ , _)) = record
  { U = A SP.×[ C ] B
  ; cone = PullbackCone SP.p₁ SP.p₂ fp₁==gp₂
  ; universality = ∧right $ ⟶ (
    PIsPullback↔IsPullback f g (A SP.×[ C ] B) SP.p₁ SP.p₂) p }
  where instance _ = P

open import Type.Sum renaming (_,_ to _Σ,_) hiding (_×_)

-- unfortunately cannot use PIsPullback↔IsPullback
-- because being a Pullback allows for arbitrary cone to be universal
-- and IsPullback requires the constructed PullbackCone to be universal
Pullback→PPullback : {f : A ~> C}{g : B ~> C}
  (P : Pullback f g) → P.Pullback f g
Pullback→PPullback {f}{g} P =
  V Σ, (cone at ₁ Σ, cone at ₂) , (ConePull-prop cone ,
  λ p₀' p₁' fp₀'==gp₁' → go p₀' p₁' fp₀'==gp₁' $
                         to-universal (c p₀' p₁' fp₀'==gp₁'))
  where instance _ = P
        V = U
        c = PullbackCone
        go : {V' : obj}
             (p₀' : V' ~> A)(p₁' : V' ~> B)
             (q : f ∘ p₀' == g ∘ p₁')
             (p : ∃! λ (f : V' ~> V) → ∀ X →
                  c p₀' p₁' q at X == cone at X ∘ f)
             → ----------------------------------------------------------
             ∃! λ (!f : V' ~> V) →
             cone at ₁ ∘ !f == p₀' ∧
             cone at ₂ ∘ !f == p₁'
        go p₀' p₁' fp₀'==gp₁' (z , (p , !z)) =
          z , ((sym (p ₁) , sym (p ₂)) ,
              λ {z' (c₁z'==p₀' , c₂z'==p₁') → !z z' λ
                { ₀ → proof f ∘ p₀'
                        === f ∘ (cone at ₁ ∘ z')
                          :by: ap (f ∘_) $ sym c₁z'==p₀'
                        === f ∘ cone at ₁ ∘ z' :by: assoc f (cone at ₁) z'
                        === (cone at ₀ ∘ id _) ∘ z'
                          :by: ap (_∘ z') $ sym $ naturality ⦃ cone ⦄ (inr ⋆)
                        === cone at ₀ ∘ z'
                          :by: ap (_∘ z') $ right-unit (cone at ₀)
                      qed
                ; ₁ → sym c₁z'==p₀'
                ; ₂ → sym c₂z'==p₁'}})

open import Morphism.Iso

Pullback≅ : {f : A ~> C}{g : B ~> C}
  (P : Pullback f g)
  (P' : P.Pullback f g)
  → --------------------
  let instance _ = P; _ = P' in
  U ≅ A SP.×[ C ] B
Pullback≅ {f}{g} P P'@(_ Σ, (p₁ Σ, p₂) , (fp₁==gp₂ , p))
  with p (cone at ₁)(cone at ₂)(ConePull-prop cone)
     | to-universal (PullbackCone p₁ p₂ fp₁==gp₂)
     | p p₁ p₂ fp₁==gp₂ | to-universal cone
  where instance _ = P; _ = P'
... | z , (pz₁ , pz₂ , !z) | z⁻¹ , (pz⁻¹ , !z⁻¹) | !id | !id' =
  z , (z⁻¹ , (
  ∃!== !id ((
    proof p₁ ∘ (z ∘ z⁻¹)
      === p₁ ∘ z ∘ z⁻¹    :by: assoc p₁ z z⁻¹
      === cone at ₁ ∘ z⁻¹ :by: ap (_∘ z⁻¹) pz₁
      === p₁              :by: sym $ pz⁻¹ ₁
    qed) , (
    proof p₂ ∘ (z ∘ z⁻¹)
      === p₂ ∘ z ∘ z⁻¹    :by: assoc p₂ z z⁻¹
      === cone at ₂ ∘ z⁻¹ :by: ap (_∘ z⁻¹) pz₂
      === p₂              :by: sym $ pz⁻¹ ₂
    qed))
    (right-unit p₁ , right-unit p₂) ,
  ∃!== !id' (
    λ { ₀ → proof cone at ₀
              === cone at ₀ ∘ id _      :by: sym $ right-unit (cone at ₀)
              === f ∘ cone at ₁         :by: naturality ⦃ cone ⦄ (inr ⋆)
              === f ∘ (p₁ ∘ z)          :by: ap (f ∘_) $ sym pz₁
              === f ∘ p₁ ∘ z            :by: assoc f p₁ z
              === cone at ₀ ∘ z⁻¹ ∘ z   :by: ap (_∘ z) $ pz⁻¹ ₀
              === cone at ₀ ∘ (z⁻¹ ∘ z) :by: sym $ assoc _ z⁻¹ z
            qed
      ; ₁ → proof cone at ₁
              === p₁ ∘ z                :by: sym pz₁
              === cone at ₁ ∘ z⁻¹ ∘ z   :by: ap (_∘ z) $ pz⁻¹ ₁
              === cone at ₁ ∘ (z⁻¹ ∘ z) :by: sym $ assoc _ z⁻¹ z
            qed
      ; ₂ → proof cone at ₂
              === p₂ ∘ z                :by: sym pz₂
              === cone at ₂ ∘ z⁻¹ ∘ z   :by: ap (_∘ z) $ pz⁻¹ ₂
              === cone at ₂ ∘ (z⁻¹ ∘ z) :by: sym $ assoc _ z⁻¹ z
            qed})
    λ { ₀ → sym $ right-unit (cone at ₀)
      ; ₁ → sym $ right-unit (cone at ₁)
      ; ₂ → sym $ right-unit (cone at ₂)}))
  where instance _ = P; _ = P'
