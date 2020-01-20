{-# OPTIONS --exact-split --safe --prop #-}
module Functor.Property where

open import Functor.Definition

open import PropUniverses
open import Logic
open import Proof

open import Category

faithful :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F : Functor ℂ 𝔻)
  → --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒯 ᵖ
faithful {ℂ = ℂ} F = ∀ {X Y : obj}
  (f g : X ~> Y)
  (p : F₁ f == F₁ g)
  → ---------------------------
  f == g
  where instance _ = ℂ; _ = F

full : 
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F : Functor ℂ 𝔻)
  → --------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒯 ᵖ
full {ℂ = ℂ}{𝔻} F = ∀ {X Y : obj ⦃ ℂ ⦄}
  (h : F₀ X ~> F₀ Y)
  → ---------------------------
  ∃ λ (f : X ~> Y) → F₁ f == h
  where instance _ = ℂ; _ = 𝔻; _ = F

open import Isomorphism

F-iso-is-iso :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F : Functor ℂ 𝔻)
  → let instance _ = ℂ; _ = 𝔻; _ = F in
  {X Y : obj ⦃ ℂ ⦄}
  {f : X ~> Y}
  (p : iso f)
  → --------------------
  iso (F₁ f)
F-iso-is-iso {ℂ = ℂ}{𝔻} F {X}{Y}{f}(f⁻¹ , (f∘f⁻¹==id , f⁻¹∘f==id)) =
  F₁ f⁻¹ ,
  ((proof F₁ f ∘ F₁ f⁻¹
      === F₁ (f ∘ f⁻¹) :by: sym $ ∘-preserv f f⁻¹
      === F₁ (id Y)    :by: ap F₁ f∘f⁻¹==id
      === id (F₀ Y)    :by: id-preserv Y
    qed) ,
   (proof F₁ f⁻¹ ∘ F₁ f
      === F₁ (f⁻¹ ∘ f) :by: sym $ ∘-preserv f⁻¹ f
      === F₁ (id X)    :by: ap F₁ f⁻¹∘f==id
      === id (F₀ X)    :by: id-preserv X
    qed))
  where instance _ = F; _ = ℂ; _ = 𝔻

full-faithful-iso :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F : Functor ℂ 𝔻)
  (full-F : full F)
  (faith-F : faithful F)
  → let instance _ = ℂ; _ = 𝔻; _ = F in
  {X Y : obj ⦃ ℂ ⦄}
  {f : X ~> Y}
  (p : iso (F₁ f))
  → --------------------
  iso f
full-faithful-iso F full-F faith-F (Ff⁻¹ , _) with full-F Ff⁻¹
full-faithful-iso {ℂ = ℂ}{𝔻} F full-F faith-F
  {X}{Y}{f}(Ff⁻¹ , (Ff∘Ff⁻¹==id , Ff⁻¹∘Ff==id))
  | f⁻¹ , Id.refl _ =
    f⁻¹ ,
    (faith-F (f ∘ f⁻¹) (id Y) (
       proof F₁ (f ∘ f⁻¹)
         === F₁ f ∘ F₁ f⁻¹ :by: ∘-preserv f f⁻¹
         === id (F₀ Y)     :by: Ff∘Ff⁻¹==id
         === F₁ (id Y)     :by: sym $ id-preserv Y
       qed) ,
     faith-F (f⁻¹ ∘ f) (id X) (
       proof F₁ (f⁻¹ ∘ f)
         === F₁ f⁻¹ ∘ F₁ f :by: ∘-preserv f⁻¹ f
         === id (F₀ X)     :by: Ff⁻¹∘Ff==id
         === F₁ (id X)     :by: sym $ id-preserv X
       qed))
  where instance _ = ℂ; _ = 𝔻; _ = F
