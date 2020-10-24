{-# OPTIONS --exact-split --safe --prop #-}
module Example.Graphs where

open import Universes
open import Category

record Graph 𝒰 𝒱 : (𝒰 ⊔ 𝒱) ⁺ ˙ where
  field
    V : 𝒰 ˙
    _-E->_ : (s t : V) → 𝒱 ˙

  edge = _-E->_
  
open Graph using (edge) public
open Graph ⦃ … ⦄ hiding (edge)

record GraphHomomorphism
  (G₀ : Graph 𝒰 𝒱)
  (G₁ : Graph 𝒲 𝒯)
  : ----------------------------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  where
  constructor [Fv=_,Fe=_]
  instance _ = G₀; _ = G₁
  field
    Fv : (v : V ⦃ G₀ ⦄) → V ⦃ G₁ ⦄
    Fe : {s t : V ⦃ G₀ ⦄}(e : s -E-> t) → Fv s -E-> Fv t

open import Function renaming (id to id-fun; _∘_ to _∘'_) hiding (_$_)
open import Proposition.Identity

Graphs : (𝒰 𝒱 : Universe) → Category ((𝒰 ⊔ 𝒱) ⁺) (𝒰 ⊔ 𝒱)
Graphs 𝒰 𝒱 = record
  { obj = Graph 𝒰 𝒱
  ; _~>_ = GraphHomomorphism
  ; id = λ X → [Fv= id-fun ,Fe= id-fun ]
  ; _∘_ = λ { [Fv= Fv₀ ,Fe= Fe₀ ] [Fv= Fv₁ ,Fe= Fe₁ ] →
              [Fv= Fv₀ ∘' Fv₁ ,Fe= Fe₀ ∘' Fe₁ ]}
  ; left-unit = Id.refl
  ; right-unit = Id.refl
  ; assoc = λ h g f → Id.refl _
  }

open import Functor
open import Category.Cat.Definition

Forgetful-Cat→Graphs : Functor CatCategory (Graphs 𝒰 𝒱)
Forgetful-Cat→Graphs =
  [F₀= (λ C → record { V = obj ⦃ C ⦄ ; _-E->_ = mor C })
  ,F₁= (λ F → [Fv= F₀ ⦃ F ⦄  ,Fe= F₁ ⦃ F ⦄ ])
  ,id-pres= (λ X → refl _)
  ,∘-pres= (λ g f → refl _) ]
