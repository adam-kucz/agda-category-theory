{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Category

module Construction.Cone.Universal.Property (𝕀 : Category 𝒳 𝒵) where

open import Functor
open import NaturalTransformation renaming (Composition to _O_)
    
open import Logic
open import Proof hiding (coe)

module General where
  open import Construction.Cone.Definition using (Diagram; Cone)
  open import Construction.Cone.Universal.Definition

  open import Proposition.Identity.Coercion

  left-compose-cone :
    {ℂ : Category 𝒰 𝒱}
    {𝔻 : Category 𝒲 𝒯}
    → let instance _ = ℂ; _ = 𝔻 in
    {D : Diagram 𝕀}
    {V : obj}
    (F : Functor ℂ 𝔻)
    (c : Cone 𝕀 D V)
    → ------------------------
    let instance _ = F in
    Cone 𝕀 (F o D) (F₀ V)
  left-compose-cone {D = D} {V} F c =
    coe (ap (_⟹ F o D) (o-Const 𝕀 V F))
        (left-compose F c)

  open import Type.Sum hiding (_,_)
  open import Function.Property

  open import Adjunction
  
  functor-universal-cone :
    {ℂ : Category 𝒰 𝒱}
    {𝔻 : Category 𝒲 𝒯}
    {D : Diagram 𝕀 ⦃ ℂ ⦄}
    (univ : UniversalCone ⦃ ℂ ⦄ 𝕀 D)
    (F : Functor ℂ 𝔻)
    (A : Σ λ G → G ⊣ F)
    → -----------------------------
    let instance _ = ℂ; _ = 𝔻; _ = F; _ = univ in
    IsUniversalCone 𝕀 (F₀ U) (left-compose-cone F cone)
  to-universal ⦃ functor-universal-cone {ℂ = ℂ}{_}{D} univ F (G Σ., A) ⦄ {V} c
    with to-universal ((right-compose ε D) O left-compose-cone G c)
    where instance _ = univ; _ = ℂ; _ = A
  to-universal (functor-universal-cone {ℂ = ℂ}{𝔻} univ F (G Σ., A)) {V} c
    | GV~>U , (comp , uniq) =
    f ,
    ((λ i → {!!}) ,
     λ f' p → {!!})
    where instance _ = univ; _ = ℂ; _ = 𝔻; _ = A
          A' = ⊣→-| A
          f : V ~> F₀ ⦃ F ⦄ U
          f = back ⦃ _-|_.bijection A' V U ⦄ GV~>U

open General public

module WithFixedCategory ⦃ ℂ : Category 𝒲 𝒯 ⦄ where
  open import Isomorphism

  open import Construction.Cone.Definition 𝕀 
  open import Construction.Cone.Universal.Definition 𝕀 

  -- TODO: strenghten to unique isomorphism
  universal-cone-unique-upto-iso :
    {D : Diagram}
    (cone₁ cone₂ : UniversalCone D)
    → --------------------------
    U ⦃ cone₁ ⦄ ≅ U ⦃ cone₂ ⦄
  universal-cone-unique-upto-iso cone₁ cone₂ with
    to-universal ⦃ universality ⦃ cone₁ ⦄ ⦄ (cone ⦃ cone₁ ⦄) |
    to-universal ⦃ universality ⦃ cone₁ ⦄ ⦄ (cone ⦃ cone₂ ⦄) |
    to-universal ⦃ universality ⦃ cone₂ ⦄ ⦄ (cone ⦃ cone₁ ⦄) |
    to-universal ⦃ universality ⦃ cone₂ ⦄ ⦄ (cone ⦃ cone₂ ⦄)
  universal-cone-unique-upto-iso cone₁ cone₂
    | U₁~>U₁ , (cone₁==cone₁-∘-U₁~>U₁ , uniq₁₁)
    | U₂~>U₁ , (cone₂==cone₁-∘-U₂~>U₁ , uniq₂₁)
    | U₁~>U₂ , (cone₁==cone₂-∘-U₁~>U₂ , uniq₁₂)
    | U₂~>U₂ , (cone₂==cone₂-∘-U₂~>U₂ , uniq₂₂) =
    U₁~>U₂ , (U₂~>U₁ ,
      ((proof U₁~>U₂ ∘ U₂~>U₁
           === U₂~>U₂
             :by: uniq₂₂ (U₁~>U₂ ∘ U₂~>U₁) (λ X →
               proof cone ⦃ cone₂ ⦄ at X
                 === cone ⦃ cone₁ ⦄ at X ∘ U₂~>U₁
                   :by: cone₂==cone₁-∘-U₂~>U₁ X
                 === cone ⦃ cone₂ ⦄ at X ∘ U₁~>U₂ ∘ U₂~>U₁
                   :by: ap (_∘ U₂~>U₁) $ cone₁==cone₂-∘-U₁~>U₂ X
                 === cone ⦃ cone₂ ⦄ at X ∘ (U₁~>U₂ ∘ U₂~>U₁)
                   :by: sym $ assoc _ _ _
               qed)
           === id (U ⦃ cone₂ ⦄)
             :by: sym $ uniq₂₂ (id (U ⦃ cone₂ ⦄)) λ _ → sym $ right-unit _
         qed) ,
        (proof U₂~>U₁ ∘ U₁~>U₂
           === U₁~>U₁
             :by: uniq₁₁ (U₂~>U₁ ∘ U₁~>U₂) (λ X →
               proof cone ⦃ cone₁ ⦄ at X
                 === cone ⦃ cone₂ ⦄ at X ∘ U₁~>U₂
                   :by: cone₁==cone₂-∘-U₁~>U₂ X
                 === cone ⦃ cone₁ ⦄ at X ∘ U₂~>U₁ ∘ U₁~>U₂
                   :by: ap (_∘ U₁~>U₂) $ cone₂==cone₁-∘-U₂~>U₁ X
                 === cone ⦃ cone₁ ⦄ at X ∘ (U₂~>U₁ ∘ U₁~>U₂)
                   :by: sym $ assoc _ _ _
               qed)
           === id (U ⦃ cone₁ ⦄)
             :by: sym $ uniq₁₁ (id (U ⦃ cone₁ ⦄)) λ _ → sym $ right-unit _
         qed)))
  
  isomorphic-to-universal-cone-is-universal-cone :
    {D : Diagram}
    (univ-cone : UniversalCone D)
    {X : obj}
    (U≅X : U ⦃ univ-cone ⦄ ≅ X)
    → ---------------------------------------------------
    ∃ λ (cone-X : Cone D X) → IsUniversalCone X (cone-X)
  isomorphic-to-universal-cone-is-universal-cone
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

open WithFixedCategory public
