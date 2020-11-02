{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category

module Construction.Cone.Category
  ⦃ ℂ : Category 𝒰 𝒱 ⦄(𝕀 : Category 𝒲 𝒯) where

open import Construction.Cone.Definition 𝕀
open import NaturalTransformation
open import Type.Sum
open import Proposition.Identity
open import Proposition.Sum renaming (_,_ to _,,_)
open import Proof

ConeCat : (D : Diagram) → Category (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯) (𝒱 ⊔ 𝒲)
obj ⦃ ConeCat D ⦄ = Σ λ (U : obj) → Cone D U
_~>_ ⦃ ConeCat D ⦄ (U , θ) (V , ϕ) =
  Σₚ λ (f : U ~> V) → ∀ i → ϕ at i ∘ f == θ at i
id ⦃ ConeCat D ⦄ (U , θ) = id U ,, λ i → right-unit (θ at i)
_∘_ ⦃ ConeCat D ⦄ {(U , θ)}{(V , ϕ)}{(W , ψ)}(g ,, p₁)(f ,, p₂) =
  g ∘ f ,, λ i →
    proof ψ at i ∘ (g ∘ f)
      === ψ at i ∘ g ∘ f :by: assoc (ψ at i) g f
      === ϕ at i ∘ f     :by: ap (_∘ f) $ p₁ i
      === θ at i         :by: p₂ i
    qed
left-unit ⦃ ConeCat D ⦄ (f ,, _) = Σₚ== $ left-unit f
right-unit ⦃ ConeCat D ⦄ (f ,, _) = Σₚ== $ right-unit f
assoc ⦃ ConeCat D ⦄ (h ,, _) (g ,, _) (f ,, _) = Σₚ== $ assoc h g f
