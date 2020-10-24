{-# OPTIONS --exact-split --prop #-}
module Category.Cat.Property where

open import Category
open import Category.Cat.Definition
open import Functor renaming (Id to FunctorId)

open import Universes
open import Proof

private
  instance
    _ = CatCategory

open import Type.Sum hiding (_×_) renaming (_,_ to _Σ,_)
open import Proposition.Identity hiding (refl)
open import Data.FinNat
open import Function hiding (_$_)
open import Logic
open import NaturalTransformation
open import Category.Product
open import Construction.Product.Definition hiding (_×_; 〈_,_〉)
open import Construction.Cone.Universal

open import Functor.Extensionality

open import Axiom.FunctionExtensionality

CatProducts : HasProducts (CatCategory {𝒰}{𝒱})
U ⦃ CatProducts {A = ℂ}{𝔻} ⦄ = ℂ × 𝔻
cone ⦃ CatProducts {A = ℂ}{𝔻} ⦄ = ProductCone (pi₁ ℂ 𝔻) (pi₂ ℂ 𝔻)
to-universal ⦃ universality ⦃ CatProducts {A = ℂ} {𝔻} ⦄ ⦄ {𝔼} c =
  F ,
  ((λ { ₀ → Functor== (c at ₀) (pi₁ ℂ 𝔻 o F)
              (subrel $ fun-ext λ _ → refl _)
              (fun-ext-implicit λ _ →
               fun-ext-implicit λ _ →
               fun-ext λ _ → refl _)
      ; ₁ → Functor== (c at ₁) (pi₂ ℂ 𝔻 o F)
              (subrel $ fun-ext λ _ → refl _)
              (fun-ext-implicit λ _ →
               fun-ext-implicit λ _ →
               fun-ext λ _ → refl _)}) ,
   (λ F' p → Functor== F' F
               (subrel $ fun-ext λ x → sym $ subrel $
                Σ== (ap (λ — → F₀ ⦃ — ⦄ x) (p ₀))
                    (subrel $ ap (λ — → F₀ ⦃ — ⦄ x) (p ₁)))
               (fun-ext-implicit λ X →
               fun-ext-implicit λ Y →
               fun-ext λ f → isym $ go
                 (ap (λ — → F₁ ⦃ — ⦄ f) ⦃ Relating-all-==-het== ⦄ (p ₀))
                 (ap (λ — → F₁ ⦃ — ⦄ f) ⦃ Relating-all-==-het== ⦄ (p ₁)))))
  where F : Functor 𝔼 (ℂ × 𝔻)
        F = [F₀= 〈 F₀ ⦃ c at ₀ ⦄ , F₀ ⦃ c at ₁ ⦄ 〉
            ,F₁= 〈 F₁ ⦃ c at ₀ ⦄ , F₁ ⦃ c at ₁ ⦄ 〉
            ,id-pres= (λ X → ap2 _Σ,_
              (id-preserv ⦃ c at ₀ ⦄ X)
              (id-preserv ⦃ c at ₁ ⦄ X))
            ,∘-pres= (λ g f → ap2 _Σ,_
              (∘-preserv ⦃ c at ₀ ⦄ g f)
              (∘-preserv ⦃ c at ₁ ⦄ g f)) ]
        go : {x : X}{x' : Z}{y : Y}{y' : W}
             (p₀ : x Het.== x')
             (p₁ : y Het.== y')
             → --------------------------------------------
             x Σ, y Het.== x' Σ, y'
        go (Het.refl _)(Het.refl _) = refl _
