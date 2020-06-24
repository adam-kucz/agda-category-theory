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

∘==∘ : 
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  {X Y Y' Z : obj}
  {g : Y ~> Z}{f : X ~> Y}
  {g' : Y' ~> Z}{f' : X ~> Y'}
  (p : Y == Y')
  (q : g Het.== g')
  (q' : f Het.== f')
  → --------------------
  g ∘ f == g' ∘ f'
∘==∘ (Id.refl Y)(Het.refl g)(Het.refl f) = Id.refl (g ∘ f)
