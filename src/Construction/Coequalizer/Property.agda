{-# OPTIONS --exact-split --prop #-}
module Construction.Coequalizer.Property where

open import Construction.Coequalizer.Definition
open import Construction.Equalizer

open import Universes
open import Logic

open import Category
open import Category.Opposite
open import Morphism

coequalizer-is-epi : ⦃ C : Category 𝒰 𝒱 ⦄
  {Q B : obj}
  {q : B ~> Q}
  (p : ∃ λ (A : obj) →
       ∃ λ (f : A ~> B) →
       ∃ λ (g : A ~> B) → IsCoequalizer f g Q q)
  → --------------------------------------------------
  epi q
coequalizer-is-epi ⦃ ℂ ⦄ =
  dualₚ (λ ℂ {E}{A}{e} → equalizer-is-mono ⦃ ℂ ⦄ {E}{A}{e}) ℂ
