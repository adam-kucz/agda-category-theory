{-# OPTIONS --exact-split --prop #-}
module Functor.Slice where

open import Category
open import Functor
open import Category.Slice
open import Category.Cat

open import PropUniverses
open import Type.Sum renaming (_,_ to _Σ,_)
open import Proposition.Sum
open import Proof

open import Axiom.FunctionExtensionality

SliceFunctor : (ℂ : Category 𝒰 𝒱) → Functor ℂ CatCategory
SliceFunctor ℂ =
  [F₀= ℂ ╱_ ,F₁= CF
  ,id-pres= (λ X → Functor== (CF (id X)) (Id (ℂ ╱ X))
    (subrel $ fun-ext λ { (X Σ, f) →
     subrel $ ap (X Σ,_) $ left-unit f})
    (fun-ext-implicit λ {(Y Σ, f) →
     fun-ext-implicit λ {(Z Σ, g) →
     fun-ext λ {(i , p) → Σₚ==' (Id.refl i) $ subrel $
     fun-ext λ h → ap2 _==_ (subrel $ ap (_∘ h) $ left-unit g)
                            (subrel $ left-unit f)}}}))
  ,∘-pres= (λ g f → Functor== (CF (g ∘ f)) (CF g o CF f)
    (subrel $ fun-ext λ { (X Σ, h) → subrel $ ap (X Σ,_) $
     sym $ assoc g f h})
    (fun-ext-implicit λ {(Y Σ, f₀) →
     fun-ext-implicit λ {(Z Σ, f₁) →
     fun-ext λ {(i , p) → Σₚ==' (Id.refl i) $ subrel $
     fun-ext λ h → ap2 _==_ (subrel $ ap (_∘ h) $ sym $ assoc g f f₁)
                            (subrel $ sym $ assoc g f f₀ )}}})
  )]
  where instance _ = ℂ
        CF = CompositionFunctor {ℂ = ℂ}
        Σₚ==' :
          {𝐴 𝐵 : (x : X) → 𝒰 ᵖ}
          {σ : Σₚ 𝐴}{ρ : Σₚ 𝐵}
          (p : elem σ == elem ρ)
          (q : 𝐴 == 𝐵)
          → -------------------------------
          σ Het.== ρ
        Σₚ==' (Id.refl x)(Id.refl 𝐴) = Het.refl _

_/[-] = SliceFunctor

