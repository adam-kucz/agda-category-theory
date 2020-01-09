{-# OPTIONS --exact-split --prop #-}
module Category.FunCategory where

open import Category.Definition
open import Functor hiding (Id; _o_)
open import NaturalTransformation renaming (Identity to Id; Composition to _o_)
open import Category.ArrowCategory

open import Universes hiding (X; Y; Z)
open import Logic hiding (_,_)
open import Proof

open import Axiom.FunctionExtensionality

FunCategory :
  (ℂ : Category 𝒰 𝒱)
  (𝔻 : Category 𝒲 𝒯)
  → --------------------
  Category (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯) (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯)
FunCategory ℂ 𝔻 = record
  { obj = Functor ℂ 𝔻
  ; _~>_ = λ F G → F ⟹ G
  ; id = Id
  ; _∘_ = _o_
  ; left-unit = λ {X} {Y} θ →
    ⟹== (Id Y o θ) θ $ fun-ext λ _ → left-unit _
  ; right-unit = λ {F} {G} θ →
    ⟹== (θ o Id F) θ $ fun-ext λ _ → right-unit _
  ; assoc = λ ψ ϕ θ → 
    ⟹== (ψ o (ϕ o θ)) ((ψ o ϕ) o θ) $ fun-ext λ _ → assoc _ _ _
  }
  where instance _ = ℂ; _ = 𝔻

open import Category.Product
open import Type.Sum hiding (_×_)

App :
  (ℂ : Category 𝒰 𝒱)
  (𝔻 : Category 𝒲 𝒯)
  → ------------------------------
  Functor (FunCategory ℂ 𝔻 × ℂ) 𝔻
App ℂ 𝔻 = record
  { F₀ = λ { (F , X) → F₀ ⦃ F ⦄ X }
  ; F₁ = λ { {F , _}{_ , Y} (θ , f) → θ at Y ∘ F₁ ⦃ F ⦄ f }
  ; id-preserv = λ { (F , X) → let instance _ = F in
      proof id (F₀ _) ∘ F₁ (id X)
        〉 _==_ 〉 id (F₀ _) ∘ id (F₀ X)
          :by: ap (id (F₀ _) ∘_) $ id-preserv X
        〉 _==_ 〉 id (F₀ X) :by: left-unit (id (F₀ X))
      qed }
  ; ∘-preserv = λ { {F , X} {G , Y} {H , Z} (θ , g) (ψ , f) →
      let instance _ = F in
      proof (θ ∘ ψ) at Z ∘ F₁ (g ∘ f)
        〉 _==_ 〉 θ at Z ∘ ψ at Z ∘ (F₁ g ∘ F₁ f)
          :by: ap ((θ ∘ ψ) at Z ∘_) $ ∘-preserv g f
        〉 _==_ 〉 θ at Z ∘ ψ at Z ∘ F₁ g ∘ F₁ f
          :by: assoc _ _ _
        〉 _==_ 〉 θ at Z ∘ (ψ at Z ∘ F₁ g) ∘ F₁ f
          :by: ap (_∘ F₁ f) $ sym $ assoc _ _ _
        〉 _==_ 〉 θ at Z ∘ (F₁ ⦃ G ⦄ g ∘ ψ at Y) ∘ F₁ f
          :by: ap (λ — → θ at Z ∘ — ∘ F₁ f) $ naturality ⦃ ψ ⦄ g
        〉 _==_ 〉 θ at Z ∘ F₁ ⦃ G ⦄ g ∘ ψ at Y ∘ F₁ f
          :by: ap (_∘ F₁ f) $ assoc _ _ _
        〉 _==_ 〉 (θ at Z ∘ F₁ ⦃ G ⦄ g) ∘ (ψ at Y ∘ F₁ f)
          :by: sym $ assoc _ _ _
      qed}
  }
  where instance
          _ = ℂ
          _ = 𝔻
          _ = FunCategory ℂ 𝔻
