{-# OPTIONS --exact-split --safe --prop #-}

open import CategoryTheory.Category.Definition 

open import PropUniverses

module CategoryTheory.Category.Monomorphism ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Proposition.Identity

mono : {X Y : obj} (p : X ~> Y) → 𝒰 ⊔ 𝒱 ᵖ
mono {X = X} p = {W : obj} {f g : W ~> X} → p ∘ f == p ∘ g → f == g

epi
