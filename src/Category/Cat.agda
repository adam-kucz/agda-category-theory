{-# OPTIONS --exact-split --prop #-}
module Category.Cat where

open import Category.Definition
open import Functor renaming (Id to FunctorId)

open import Universes
open import Proof

CatCategory : Category (𝒰 ⁺ ⊔ 𝒱 ⁺) (𝒰 ⊔ 𝒱)
obj ⦃ CatCategory {𝒰} {𝒱} ⦄ = Category 𝒰 𝒱
_~>_ ⦃ CatCategory ⦄ = Functor
id ⦃ CatCategory ⦄ = FunctorId
_∘_ ⦃ CatCategory ⦄ = _o_
left-unit ⦃ CatCategory ⦄ f = refl f
right-unit ⦃ CatCategory ⦄ f = refl f
assoc ⦃ CatCategory ⦄ h g f = refl (h o (g o f))

private
  instance
    _ = CatCategory

open import Type.Sum hiding (_×_; _,_)
open import Proposition.Identity hiding (refl)
open import Data.FinNat
open import Function hiding (_$_)
open import Logic
open import NaturalTransformation
open import Category.Product
open import Construction.Product.Definition hiding (_×_; 〈_,_〉)
open import Construction.Cone.Universal

open import Functor.Extensionality

private
  pi₁ :
    (ℂ : Category 𝒰 𝒱)
    (𝔻 : Category 𝒰 𝒱)
    → --------------------
    Functor (ℂ × 𝔻) ℂ
  pi₁ ℂ 𝔻 = [F₀= pr₁ ,F₁= pr₁ ,id-pres= (λ _ → refl _) ,∘-pres= (λ _ _ → refl _) ]
  pi₂ :
    (ℂ : Category 𝒰 𝒱)
    (𝔻 : Category 𝒰 𝒱)
    → --------------------
    Functor (ℂ × 𝔻) 𝔻
  pi₂ ℂ 𝔻 = [F₀= pr₂ ,F₁= pr₂ ,id-pres= (λ _ → refl _) ,∘-pres= (λ _ _ → refl _) ]

open import Axiom.FunctionExtensionality

CatProducts : HasProducts (CatCategory {𝒰}{𝒱})
U ⦃ CatProducts {A = ℂ}{𝔻} ⦄ = ℂ × 𝔻
cone ⦃ CatProducts {A = ℂ}{𝔻} ⦄ = ProductCone (pi₁ ℂ 𝔻) (pi₂ ℂ 𝔻)
to-universal ⦃ universality ⦃ CatProducts {A = ℂ} {𝔻} ⦄ ⦄ {𝔼} c =
  F ,
  ((λ { ₀ → Functor== (c at ₀) (pi₁ ℂ 𝔻 o F)
              (fun-ext λ _ → refl _)
              (fun-ext-implicit λ _ →
               fun-ext-implicit λ _ →
               fun-ext λ _ → refl _)
      ; ₁ → Functor== (c at ₁) (pi₂ ℂ 𝔻 o F)
              (fun-ext λ _ → refl _)
              (fun-ext-implicit λ _ →
               fun-ext-implicit λ _ →
               fun-ext λ _ → refl _)}) ,
   (λ F' p → Functor== F' F
               (fun-ext λ x → sym $ ap2 Σ._,_
                 (ap (λ — → F₀ ⦃ — ⦄ x) (p ₀))
                 (ap (λ — → F₀ ⦃ — ⦄ x) (p ₁)))
               (fun-ext-implicit λ X →
               fun-ext-implicit λ Y →
               fun-ext λ f → go
                 (Id.sym $ ap (λ — → F₁ ⦃ — ⦄ f) (p ₀))
                 (Id.sym $ ap (λ — → F₁ ⦃ — ⦄ f) (p ₁)))))
  where F : Functor 𝔼 (ℂ × 𝔻)
        F = [F₀= 〈 F₀ ⦃ c at ₀ ⦄ , F₀ ⦃ c at ₁ ⦄ 〉
            ,F₁= 〈 F₁ ⦃ c at ₀ ⦄ , F₁ ⦃ c at ₁ ⦄ 〉
            ,id-pres= (λ X → ap2 Σ._,_
              (id-preserv ⦃ c at ₀ ⦄ X)
              (id-preserv ⦃ c at ₁ ⦄ X))
            ,∘-pres= (λ g f → ap2 Σ._,_
              (∘-preserv ⦃ c at ₀ ⦄ g f)
              (∘-preserv ⦃ c at ₁ ⦄ g f)) ]
        go : {x : X}{x' : Z}{y : Y}{y' : W}
             (p₀ : x == x')
             (p₁ : y == y')
             → --------------------------------------------
             x Σ., y == x' Σ., y'
        go (Id.refl _) (Id.refl _) = Id.refl _
