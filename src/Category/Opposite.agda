{-# OPTIONS --safe --exact-split --prop  #-}
module Category.Opposite where

open import Category.Definition

open import PropUniverses
open import Proposition.Identity using (_==_; refl)
open import Relation.Binary using (sym)

infix 159 _ᵒᵖ
_ᵒᵖ : (ℂ : Category 𝒰 𝒱) → Category 𝒰 𝒱
ℂ ᵒᵖ = record
  { obj = obj
  ; _~>_ = λ X Y → Y ~> X
  ; id = id
  ; _∘_ = λ g f → f ∘ g
  ; left-unit = right-unit
  ; right-unit = left-unit
  ; assoc = λ h g f → sym (assoc f g h)
  }
  where instance _ = ℂ

-- open import Function.Property using (Involutive; mk-involutive)

-- instance
--   Involutiveᵒᵖ : Involutive (_ᵒᵖ {𝒰} {𝒱})
--   Involutiveᵒᵖ = mk-involutive refl

dual :
  {X : (ℂ : Category 𝒰 𝒱) → 𝒲 ˙}
  (A : (ℂ : Category 𝒰 𝒱) → X ℂ)
  → -------------------------------------
  (ℂ : Category 𝒰 𝒱) → X (ℂ ᵒᵖ)
dual A ℂ = A (ℂ ᵒᵖ)

dualₚ :
  {𝑋 : (ℂ : Category 𝒰 𝒱) → 𝒲 ᵖ}
  (𝐴 : (ℂ : Category 𝒰 𝒱) → 𝑋 ℂ)
  → -------------------------------------
  (ℂ : Category 𝒰 𝒱) → 𝑋 (ℂ ᵒᵖ)
dualₚ 𝐴 ℂ = 𝐴 (ℂ ᵒᵖ)

