{-# OPTIONS --exact-split --prop #-}
module Construction.Equalizer.Property where

open import Construction.Equalizer.Definition

open import Universes
open import Logic
open import Proof

open import Category
open import Morphism.Mono

equalizer-is-monic : ⦃ C : Category 𝒰 𝒱 ⦄
  {E A : obj}
  {e : E ~> A}
  (p : ∃ λ (B : obj) →
       ∃ λ (f : A ~> B) →
       ∃ λ (g : A ~> B) → IsEqualizer f g E e)
  → --------------------------------------------------
  monic e
equalizer-is-monic {e = e} (B , (f , (g , (fe==ge , ump))))
  {Z}{g₁}{h₁} eg₁==eh₁ = ∃!== uniq (refl (e ∘ g₁)) eg₁==eh₁
  where uniq = ump (e ∘ g₁) (
          proof f ∘ (e ∘ g₁)
            === f ∘ e ∘ g₁   :by: assoc f e g₁
            === g ∘ e ∘ g₁   :by: ap (_∘ g₁) fe==ge
            === g ∘ (e ∘ g₁) :by: sym $ assoc g e g₁
          qed)
