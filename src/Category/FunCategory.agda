{-# OPTIONS --exact-split --prop #-}
module Category.FunCategory where

open import Category.Definition
open import Functor hiding (Id) renaming (_o_ to _⊚_)
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
    ⟹== (Id Y o θ) θ $ subrel $ fun-ext λ Z → subrel $ left-unit (θ at Z)
  ; right-unit = λ {F} {G} θ →
    ⟹== (θ o Id F) θ $ subrel $ fun-ext λ Z → subrel $ right-unit (θ at Z)
  ; assoc = λ ψ ϕ θ → 
    ⟹== (ψ o (ϕ o θ)) ((ψ o ϕ) o θ) $
      subrel $ fun-ext λ Z → subrel $ assoc (ψ at Z) (ϕ at Z) (θ at Z)
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
        === id (F₀ _) ∘ id (F₀ X)
          :by: ap (id (F₀ _) ∘_) $ id-preserv X
        === id (F₀ X) :by: left-unit (id (F₀ X))
      qed }
  ; ∘-preserv = λ { {F , X} {G , Y} {H , Z} (θ , g) (ψ , f) →
      let instance _ = F in
      proof (θ ∘ ψ) at Z ∘ F₁ (g ∘ f)
        === θ at Z ∘ ψ at Z ∘ (F₁ g ∘ F₁ f)
          :by: ap ((θ ∘ ψ) at Z ∘_) $ ∘-preserv g f
        === θ at Z ∘ ψ at Z ∘ F₁ g ∘ F₁ f
          :by: assoc _ _ _
        === θ at Z ∘ (ψ at Z ∘ F₁ g) ∘ F₁ f
          :by: ap (_∘ F₁ f) $ sym $ assoc (θ at Z) (ψ at Z) (F₁ g)
        === θ at Z ∘ (F₁ ⦃ G ⦄ g ∘ ψ at Y) ∘ F₁ f
          :by: ap (λ — → θ at Z ∘ — ∘ F₁ f) $ naturality ⦃ ψ ⦄ g
        === θ at Z ∘ F₁ ⦃ G ⦄ g ∘ ψ at Y ∘ F₁ f
          :by: ap (_∘ F₁ f) $ assoc (θ at Z) (F₁ ⦃ G ⦄ g) (ψ at Y)
        === (θ at Z ∘ F₁ ⦃ G ⦄ g) ∘ (ψ at Y ∘ F₁ f)
          :by: sym $ assoc _ _ _
      qed}
  }
  where instance
          _ = ℂ
          _ = 𝔻
          _ = FunCategory ℂ 𝔻

Cur : (F : Functor (ℂ × 𝔻) 𝔼) → Functor ℂ (FunCategory 𝔻 𝔼)
Cur {ℂ = ℂ}{𝔻 = 𝔻}{𝔼 = 𝔼} F =
  [F₀= with-left
  ,F₁= nat-trans
  ,id-pres= (λ X → ⟹== (nat-trans (id X)) (Id (with-left X)) $
               subrel $ fun-ext λ Y → subrel $ id-preserv (X , Y))
  ,∘-pres= (λ g f → ⟹== (nat-trans (g ∘ f)) (nat-trans g o nat-trans f) $
              subrel $ fun-ext λ Y → subrel (
                proof F₁ (g ∘ f , id Y)
                  === F₁ (g ∘ f , id Y ∘ id Y)
                    :by: ap (λ — → F₁ (g ∘ f , —)) $
                         sym $ left-unit (id ⦃ 𝔻 ⦄ Y)
                  === F₁ (g , id Y) ∘ F₁ (f , id Y)
                    :by: ∘-preserv (g , id Y) (f , id Y) [: _==_ ]
                qed)) ]
  where instance _ = ℂ; _ = 𝔻; _ = 𝔼; _ = F
        with-left : (X : obj ⦃ ℂ ⦄) → Functor 𝔻 𝔼
        with-left X =
          [F₀= (λ X₁ → F₀ (X , X₁))
          ,F₁= (λ f → F₁ (id X , f))
          ,id-pres= (λ X₁ → id-preserv (X , X₁))
          ,∘-pres= (λ g f →
            proof F₁ (id X , g ∘ f)
              === F₁ (id X ∘ id X , g ∘ f)
                :by: ap (λ — → F₁ (— , g ∘ f)) $ sym $ left-unit (id X)
              === F₁ (id X , g) ∘ F₁ (id X , f)
                :by: ∘-preserv (id X , g) (id X , f)
              qed)]
        nat-trans : ∀{X Y}(f : X ~> Y) → with-left X ⟹ with-left Y
        nat-trans {X}{Y} f = record
          { _at_ = λ X' → F₁ (f , id X')
          ; naturality = λ {X'}{Y'} f' →
            proof F₁ (f , id Y') ∘ F₁ ⦃ with-left X ⦄ f'
              === F₁ (f , id Y') ∘ F₁ (id X , f')
                :by: refl _
              === F₁ (f ∘ id X , id Y' ∘ f')
                :by: sym $ ∘-preserv (f , id Y') (id X , f')
              === F₁ (f , f')
                :by: ap2 (λ x y → F₁ (x , y)) (right-unit f) (left-unit f')
              === F₁ (id Y ∘ f , f' ∘ id X')
                :by: sym $ ap2 (λ x y → F₁ (x , y)) (left-unit f) (right-unit f')
              === F₁ (id Y , f') ∘ F₁ (f , id X')
                :by: ∘-preserv (id Y , f') (f , id X')
              === F₁ ⦃ with-left Y ⦄ f' ∘ F₁ (f , id X')
                :by: refl _
            qed }
