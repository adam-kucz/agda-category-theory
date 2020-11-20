{-# OPTIONS --exact-split --prop #-}
module Morphism.Iso.Natural where

open import Morphism.Iso.Definition

open import PropUniverses
open import Category
open import Functor
open import Category.FunCategory

private
  instance
    functor-category :
      {ℂ : Category 𝒰 𝒱}
      {𝔻 : Category 𝒲 𝒯}
      → -------------------------------------------
      Category (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯) (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯)
    functor-category {ℂ = ℂ}{𝔻} = FunCategory ℂ 𝔻

nat-iso :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F G : Functor ℂ 𝔻}
  (f : F ~> G)
  → --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
nat-iso f = iso f

open import Logic

_nat-≅_ :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F G : Functor ℂ 𝔻)
  → --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
F nat-≅ G = ∃ λ (f : F ~> G) → nat-iso f

_nat-≅-unique_ :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F G : Functor ℂ 𝔻)
  → --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
F nat-≅-unique G = ∃! λ (f : F ~> G) → nat-iso f

open import Proposition.Sum
open import Proof

open import NaturalTransformation renaming (Composition to _O_)

open import Axiom.UniqueChoice
open import Axiom.FunctionExtensionality

nat-iso↔pointwise-iso : 
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F G : Functor ℂ 𝔻}
  (f : F ~> G)
  → let _at'_ = _⟹_._at_ {F = F}{G} in
  ----------------------------------------
  nat-iso f ↔ ∀(X : obj ⦃ ℂ ⦄) → iso ⦃ 𝔻 ⦄ (f at' X)
⟶ (nat-iso↔pointwise-iso f) (f⁻¹ , (f∘f⁻¹==id , f⁻¹∘f==id)) X =
  f⁻¹ at X , (ap (_at X) f∘f⁻¹==id , ap (_at X) f⁻¹∘f==id)
⟵ (nat-iso↔pointwise-iso {𝔻 = 𝔻}{F}{G} f) q =
  f⁻¹ , (
  ⟹== (f O f⁻¹)(Identity G)(subrel $ fun-ext λ x → subrel $ left $ p x) ,
  ⟹== (f⁻¹ O f)(Identity F)(subrel $ fun-ext λ x → subrel $ right $ p x))
  where instance _ = 𝔻
        f⁻¹ = [at= (λ X → elem (!choice (iso-uniq (f at X) $ q X)))
              ,naturality= (λ {X}{Y} f' →
                let f⁻¹X = !choice (iso-uniq (f at X) $ q X)
                    f⁻¹Y = !choice (iso-uniq (f at Y) $ q Y)
                    Ff' = F₁ ⦃ F ⦄ f'; Gf' = F₁ ⦃ G ⦄ f' in
                proof elem f⁻¹Y ∘ Gf'
                  === elem f⁻¹Y ∘ (Gf' ∘ id _)
                    :by: ap (elem f⁻¹Y ∘_) $ sym $ right-unit Gf'
                  === elem f⁻¹Y ∘ (Gf' ∘ (f at X ∘ elem f⁻¹X))
                    :by: ap (λ — → elem f⁻¹Y ∘ (Gf' ∘ —)) $
                         sym $ left $ left $ prop f⁻¹X
                  === elem f⁻¹Y ∘ (Gf' ∘ f at X ∘ elem f⁻¹X)
                    :by: ap (elem f⁻¹Y ∘_) $ assoc Gf' (f at X)(elem f⁻¹X)
                  === elem f⁻¹Y ∘ (f at Y ∘ Ff' ∘ elem f⁻¹X)
                    :by: ap (λ — → elem f⁻¹Y ∘ (— ∘ elem f⁻¹X)) $
                         sym $ naturality ⦃ f ⦄ f'
                  === elem f⁻¹Y ∘ (f at Y ∘ Ff') ∘ elem f⁻¹X
                    :by: assoc (elem f⁻¹Y) _ (elem f⁻¹X)
                  === elem f⁻¹Y ∘ f at Y ∘ Ff' ∘ elem f⁻¹X
                    :by: ap (_∘ elem f⁻¹X) $ assoc (elem f⁻¹Y)(f at Y) Ff'
                  === id _ ∘ Ff' ∘ elem f⁻¹X
                    :by: ap (λ — → — ∘ Ff' ∘ elem f⁻¹X) $
                         right $ left $ prop f⁻¹Y
                  === Ff' ∘ elem f⁻¹X
                    :by: ap (_∘ elem f⁻¹X) $ left-unit Ff'
                qed)
              ]
        p : ∀ X → f at X ∘ f⁻¹ at X == id _ ∧ f⁻¹ at X ∘ f at X == id _
        p X = left $ prop (!choice (iso-uniq (f at X) $ q X))
