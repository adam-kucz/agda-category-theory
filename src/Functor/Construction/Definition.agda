{-# OPTIONS --exact-split --safe --prop #-}
module Functor.Construction.Definition where

open import Universes
open import Category
open import Functor.Definition

open import Proposition.Identity
open import Relation.Binary using (sym)

open import Example.Simple using (𝟘)

Const :
  (ℂ : Category 𝒰 𝒱)
  {𝔻 : Category 𝒲 𝒯}
  (X : obj ⦃ 𝔻 ⦄)
  → --------------------
  Functor ℂ 𝔻
Const ℂ {𝔻} X = record
  { F₀ = λ _ → X
  ; F₁ = λ _ → id X
  ; id-preserv = λ _ → refl (id X)
  ; ∘-preserv = λ _ _ → sym (left-unit (id X))
  }
  where private instance _ = 𝔻

Id : (ℂ : Category 𝒰 𝒱) → Functor ℂ ℂ
F₀ ⦃ Id ℂ ⦄ X = X
F₁ ⦃ Id ℂ ⦄ f = f
id-preserv ⦃ Id ℂ ⦄ X = refl (id ⦃ ℂ ⦄ X)
∘-preserv ⦃ Id ℂ ⦄ g f = refl (g o f)
  where _o_ = _∘_ ⦃ ℂ ⦄

open import Proof

infixl 240 _o_
_o_ :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {𝔼 : Category 𝒵 𝒳}
  (G : Functor 𝔻 𝔼)
  (F : Functor ℂ 𝔻)
  → ----------------------
  Functor ℂ 𝔼
F₀ ⦃ G o F ⦄ X = F₀ ⦃ G ⦄ (F₀ ⦃ F ⦄ X)
F₁ ⦃ G o F ⦄ f = F₁ ⦃ G ⦄ (F₁ ⦃ F ⦄ f)
id-preserv ⦃ _o_ {ℂ = ℂ} {𝔻} {𝔼} G F ⦄ X =
  proof F₁ (F₁ (id X))
    〉 _==_ 〉 F₁ (id (F₀ X))
      :by: ap F₁ (id-preserv X)
    〉 _==_ 〉 id (F₀ (F₀ X))
      :by: id-preserv (F₀ X)
  qed
  where private instance _ = G; _ = F; _ = ℂ; _ = 𝔻; _ = 𝔼
∘-preserv ⦃ _o_ {ℂ = ℂ} {𝔻} {𝔼} G F ⦄ g f =
  proof F₁ (F₁ (g ∘ f))
    〉 _==_ 〉 F₁ (F₁ g ∘ F₁ f)
      :by: ap F₁ (∘-preserv g f)
    〉 _==_ 〉 F₁ (F₁ g) ∘ F₁ (F₁ f)
      :by: ∘-preserv (F₁ g) (F₁ f)
  qed
  where private instance _ = G; _ = F; _ = ℂ; _ = 𝔻; _ = 𝔼

