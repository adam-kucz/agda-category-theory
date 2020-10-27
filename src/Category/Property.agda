{-# OPTIONS --exact-split --safe --prop #-}
open import Universes
open import Category.Definition

module Category.Property ⦃ ℂ : Category 𝒰 𝒱 ⦄{X Y : obj} where

open import Logic
open import Proof

bi-unit : (f : X ~> Y) → id Y ∘ f == f ∘ id X
bi-unit f =
  proof id _ ∘ f
    〉 _==_ 〉 f        :by: left-unit f
    〉 _==_ 〉 f ∘ id _ :by: sym $ right-unit f
  qed

∘==∘ : 
  {Y' Z : obj}
  {g : Y ~> Z}{f : X ~> Y}
  {g' : Y' ~> Z}{f' : X ~> Y'}
  (p : Y == Y')
  (q : g Het.== g')
  (q' : f Het.== f')
  → --------------------
  g ∘ f == g' ∘ f'
∘==∘ (Id.refl Y)(Het.refl g)(Het.refl f) = Id.refl (g ∘ f)
