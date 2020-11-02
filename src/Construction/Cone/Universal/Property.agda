{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category

module Construction.Cone.Universal.Property
  (𝕀 : Category 𝒳 𝒵) ⦃ ℂ : Category 𝒲 𝒯 ⦄
  where

open import Morphism.Iso
open import Functor.Definition
open import NaturalTransformation
open import Construction.Cone.Definition 𝕀 
open import Construction.Cone.Category 𝕀 
open import Construction.Cone.Universal.Definition 𝕀 

open import Proposition.Sum
open import Type.Sum renaming (_,_ to _Σ,_)
open import Logic
open import Proof

universal-cone-uniq-upto-uniq-iso :
  {D : Diagram}
  (cone₁ cone₂ : UniversalCone D)
  → let instance _ = ConeCat D
  in --------------------------
  (let instance _ = cone₁ in U Σ, cone)
  ≅-unique
  (let instance _ = cone₂ in U Σ, cone)
universal-cone-uniq-upto-uniq-iso {D} ucone₁ ucone₂ =
  go (to-universal ⦃ universality ⦃ ucone₁ ⦄ ⦄ cone₁)
     (to-universal ⦃ universality ⦃ ucone₁ ⦄ ⦄ cone₂)
     (to-universal ⦃ universality ⦃ ucone₂ ⦄ ⦄ cone₁)
     (to-universal ⦃ universality ⦃ ucone₂ ⦄ ⦄ cone₂)
  where cone₁ = cone ⦃ ucone₁ ⦄
        cone₂ = cone ⦃ ucone₂ ⦄
        U₁ = U ⦃ ucone₁ ⦄
        U₂ = U ⦃ ucone₂ ⦄
        go : (p₁₁ : ∃! λ f → ∀ X → cone₁ at X == cone₁ at X ∘ f)
             (p₂₁ : ∃! λ f → ∀ X → cone₂ at X == cone₁ at X ∘ f)
             (p₁₂ : ∃! λ f → ∀ X → cone₁ at X == cone₂ at X ∘ f)
             (p₂₂ : ∃! λ f → ∀ X → cone₂ at X == cone₂ at X ∘ f)
             → let instance _ = ConeCat D
             in --------------------------------------------------
             (U₁ Σ, cone₁) ≅-unique (U₂ Σ, cone₂)
        go p₁₁ (f⁻¹ , (p⁻¹ , !f⁻¹)) (f , (p  , !f)) p₂₂ =
          f , (λ i → sym $ p i) , (
          (f⁻¹ , λ i → sym $ p⁻¹ i) ,
          (Σₚ== (∃!== p₂₂
            (λ X → proof cone₂ at X
                     === cone₁ at X ∘ f⁻¹       :by: p⁻¹ X
                     === cone₂ at X ∘ f ∘ f⁻¹   :by: ap (_∘ f⁻¹) $ p X
                     === cone₂ at X ∘ (f ∘ f⁻¹) :by: sym $ assoc _ f f⁻¹
                   qed)
            (λ X → sym $ right-unit (cone₂ at X) )) ,
           Σₚ== (∃!== p₁₁
             (λ X → proof cone₁ at X
                      === cone₂ at X ∘ f         :by: p X
                      === cone₁ at X ∘ f⁻¹ ∘ f   :by: ap (_∘ f) $ p⁻¹ X
                      === cone₁ at X ∘ (f⁻¹ ∘ f) :by: sym $ assoc _ f⁻¹ f
                    qed)
             (λ X → sym $ right-unit (cone₁ at X)))) ,
          λ {(f' , p') _ → Σₚ== $ !f f' λ i → sym $ p' i})

iso-to-universal-cone-is-universal-cone :
  {D : Diagram}
  (univ-cone : UniversalCone D)
  {X : obj}
  (U≅X : U ⦃ univ-cone ⦄ ≅ X)
  → ---------------------------------------------------
  ∃ λ (cone-X : Cone D X) → IsUniversalCone X (cone-X)
iso-to-universal-cone-is-universal-cone
  {D = D} univ-cone {X} (f , (f⁻¹ , (f∘f⁻¹==id , f⁻¹∘f==id))) =
    cone-X , universal-cone-X
  where instance _ = univ-cone
        cone-X : Cone D X
        cone-X at Y = cone at Y ∘ f⁻¹
        naturality ⦃ cone-X ⦄ {Y}{Z} f =
          proof cone at Z ∘ f⁻¹ ∘ id X
            === cone at Z ∘ f⁻¹
              :by: right-unit _
            === cone at Z ∘ id U ∘ f⁻¹
              :by: ap (_∘ f⁻¹) $ sym $ right-unit _
            === F₁ ⦃ D ⦄ f ∘ cone at Y ∘ f⁻¹
              :by: ap (_∘ f⁻¹) $ naturality ⦃ cone ⦄ f
            === F₁ ⦃ D ⦄ f ∘ (cone at Y ∘ f⁻¹)
              :by: sym $ assoc _ _ _
          qed
        universal-cone-X : IsUniversalCone X (cone-X)
        to-universal ⦃ universal-cone-X ⦄ cone' with to-universal cone'
        to-universal universal-cone-X cone'
          | V~>U , (cone'==cone-∘-V~>U , uniq) =
            f ∘ V~>U ,
            ((λ X₁ →
                proof cone' at X₁
                  === cone at X₁ ∘ V~>U
                    :by: cone'==cone-∘-V~>U X₁
                  === cone at X₁ ∘ id U ∘ V~>U
                    :by: ap (_∘ V~>U) $ sym $ right-unit (cone at X₁)
                  === cone at X₁ ∘ (f⁻¹ ∘ f) ∘ V~>U
                    :by: ap (λ — → cone at X₁ ∘ — ∘ V~>U) $
                         sym f⁻¹∘f==id
                  === cone at X₁ ∘ f⁻¹ ∘ f ∘ V~>U
                    :by: ap (_∘ V~>U) $ assoc _ f⁻¹ f
                  === cone at X₁ ∘ f⁻¹ ∘ (f ∘ V~>U)
                    :by: sym $ assoc _ f V~>U
                qed) ,
             λ V~>X p →
               proof V~>X
                 === id X ∘ V~>X
                   :by: sym $ left-unit V~>X
                 === f ∘ f⁻¹ ∘ V~>X
                   :by: ap (_∘ V~>X) $ sym f∘f⁻¹==id
                 === f ∘ (f⁻¹ ∘ V~>X)
                   :by: sym $ assoc f f⁻¹ V~>X
                 === f ∘ V~>U
                   :by: ap (f ∘_) $ uniq (f⁻¹ ∘ V~>X) λ X₁ → (
                     proof cone' at X₁
                       === cone at X₁ ∘ f⁻¹ ∘ V~>X
                         :by: p X₁
                       === cone at X₁ ∘ (f⁻¹ ∘ V~>X)
                         :by: sym $ assoc _ f⁻¹ V~>X
                     qed)
               qed)
