{-# OPTIONS --exact-split --safe --prop #-}
module Category.Property where

open import PropUniverses
open import Logic
open import Proof

open import Category.Definition

bi-unit :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  {X Y : obj}
  (f : X ~> Y)
  → --------------------
  id Y ∘ f == f ∘ id X
bi-unit f =
  proof id _ ∘ f
    〉 _==_ 〉 f        :by: left-unit f
    〉 _==_ 〉 f ∘ id _ :by: sym $ right-unit f
  qed

