{-# OPTIONS --exact-split --prop  #-}
module Example.Preord where

open import Category
open import Structure.Preorder

open import PropUniverses
open import Type.Sum hiding (_,_)
open import Proposition.Sum
open import Function
  renaming (id to id-fun; _∘_ to _o_) using (==→~)
open import Proof

Preord : Category (𝒰 ⁺ ⊔ 𝒱 ⁺) (𝒰 ⊔ 𝒱)
obj ⦃ Preord {𝒰}{𝒱} ⦄ = Σ λ (X : 𝒰 ˙) → Preorder 𝒱 X
_~>_ ⦃ Preord ⦄ X Y = Σₚ λ (f : (x : pr₁ X) → pr₁ Y) → monotone f
  where instance _ = pr₂ X; _ = pr₂ Y
id ⦃ Preord ⦄ _ =
  id-fun ,
  record { rel-preserv = λ a⊑b → a⊑b }
_∘_ ⦃ Preord ⦄ (g , mon-g) (f , mon-f) =
  g o f ,
  record { rel-preserv = λ a⊑b → ap g (ap f a⊑b) }
  where instance _ = mon-f; _ = mon-g
left-unit ⦃ Preord ⦄ = refl
right-unit ⦃ Preord ⦄ = refl
assoc ⦃ Preord ⦄ _ _ _ = Σₚ== (refl _)

module WithFixedUnvierse {𝒰}{𝒱} where
  open import Functor
  open import Example.Set'

  private
    Preord' = Preord {𝒰}{𝒱}
    Set'' = Set' {𝒰}

  forgetful : Functor Preord' Set''
  F₀ ⦃ forgetful ⦄ = pr₁
  F₁ ⦃ forgetful ⦄ = elem
  id-preserv ⦃ forgetful ⦄ _ = refl _
  ∘-preserv ⦃ forgetful ⦄ _ _ = refl _
  
  forgetful-faithful : faithful forgetful
  forgetful-faithful _ _ = Σₚ==

  open import Proposition.Identity using (_≠_)
  open import Data.Nat
  open import Data.FinNat
  open import Relation.Binary.Property
  open import Logic
  open import Function.Proof

  forgetful-not-full : ¬ full forgetful
  forgetful-not-full ful with ful {X = P₀}{P₁} id-fun
    where
      P₀ P₁ : Σ λ (X : 𝒰 ˙) → Preorder 𝒱 X
      pr₁ P₀ = Lift𝒰 (Finℕ 2)
      _⊑_ ⦃ pr₂ P₀ ⦄ (↑type m) (↑type n) = Lift𝒰ᵖ (m ≤ₛ n)
      def ⦃ pr₂ P₀ ⦄ =
        let
          _≼_ = _⊑_ ⦃ pr₂ P₀ ⦄
          instance
            r : Reflexive _≼_
            r = record { prop-name =
              λ { (↑type m) → ↑prop (refl m) }}
            t : Transitive _≼_
            t = record { prop-name =
              λ { (↑prop p) (↑prop q) → ↑prop (trans p q) }}
          in record {}
      pr₁ P₁ = Lift𝒰 (Finℕ 2)
      _⊑_ ⦃ pr₂ P₁ ⦄ (↑type m) (↑type n) = Lift𝒰ᵖ (m == n)
      def ⦃ pr₂ P₁ ⦄ =
        let
          _≼_ = _⊑_ ⦃ pr₂ P₁ ⦄
          instance
            r : Reflexive _≼_
            r = record { prop-name =
              λ { (↑type m) → ↑prop (refl m) }}
            t : Transitive _≼_
            t = record { prop-name =
              λ { (↑prop p) (↑prop q) → ↑prop (trans p q) }}
          in record {}
  forgetful-not-full ful | f , mon-f , p
    with rel-preserv ⦃ mon-f ⦄ (↑prop $ ∨right $ z<ₛs {a = ₀})
  forgetful-not-full ful | f , mon-f , p | ↑prop q =
    ₀≠₁ $ ap (↓type {𝒱 = 𝒰}) (
      proof ↑type ₀ 
        === f (↑type ₀) :by: sym $ ==→~ p (↑type ₀)
        === f (↑type ₁) :by: ap (↑type {𝒱 = 𝒰}) q
        === ↑type ₁     :by: ==→~ p (↑type ₁)
      qed)
    where ₀≠₁ : Finℕ.zero {1} ≠ Finℕ.suc (zero {0})
          ₀≠₁ ()
