{-# OPTIONS --exact-split --prop #-}
module Construction.Equalizer.Property where

open import Construction.Equalizer.Definition

open import Universes
open import Data.FinNat
open import Logic
open import Proof

open import Category
open import Morphism.Mono
open import Construction.Cone.Definition 𝕀
open import Construction.Cone.Universal

equalizer-is-monic : ⦃ C : Category 𝒰 𝒱 ⦄
  {E A : obj}
  {e : E ~> A}
  (p : ∃ λ (B : obj) →
       ∃ λ (f : A ~> B) →
       ∃ λ (g : A ~> B) → IsEqualizer f g E e)
  → --------------------------------------------------
  monic e
equalizer-is-monic {e = e} (B , (f , (g , (f∘e==g∘e , ucone))))
  {Z}{g₁}{h₁} e∘g₁==e∘h₁ with to-universal econe
  where instance _ = ucone
        econe : Cone (EqualizerDiagram f g) Z
        econe = EqualizerCone (e ∘ g₁) (
          proof f ∘ (e ∘ g₁)
            === f ∘ e ∘ g₁   :by: assoc f e g₁
            === g ∘ e ∘ g₁   :by: ap (_∘ g₁) f∘e==g∘e
            === g ∘ (e ∘ g₁) :by: sym $ assoc g e g₁
          qed)
... | z , (_ , q) =
  proof g₁
    === z  :by: q g₁ (λ { ₀ → refl (e ∘ g₁) ; ₁ → assoc f e g₁})
    === h₁ :by: sym $ q h₁ (
      λ { ₀ → e∘g₁==e∘h₁
        ; ₁ → proof f ∘ (e ∘ g₁)
                === f ∘ (e ∘ h₁) :by: ap (f ∘_) e∘g₁==e∘h₁
                === f ∘ e ∘ h₁   :by: assoc f e h₁
              qed})
  qed
