{-# OPTIONS --exact-split --safe --prop #-}
open import Category
open import Universes hiding (X; Y)

module Morphism.Property ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Morphism.Iso
open import Morphism.Mono
open import Morphism.Epi

open import Logic
open import Proof

iso-is-split-mono :
  {X Y : obj}{f : X ~> Y}
  (p : iso f)
  → -----------------------
  split-mono f
iso-is-split-mono (f⁻¹ , (_ , left-inv)) = f⁻¹ , left-inv

iso-is-mono :
  {X Y : obj}{f : X ~> Y}
  (p : iso f)
  → -----------------------
  mono f
iso-is-mono p = split-mono-is-mono $ iso-is-split-mono p

iso-is-split-epi :
  {X Y : obj}{f : X ~> Y}
  (p : iso f)
  → -----------------------
  split-epi f
iso-is-split-epi  (f⁻¹ , (right-inv , _)) = f⁻¹ , right-inv

iso-is-epi :
  {X Y : obj}{f : X ~> Y}
  (p : iso f)
  → -----------------------
  epi f
iso-is-epi p = split-epi-is-epi $ iso-is-split-epi p

retract-of-projective-is-projective : {P R : obj}{s : R ~> P}
  (p : projective P)
  (q : split-mono s)
  → --------------------
  projective (retract-of P [ q ])
retract-of-projective-is-projective
  {P}{R}{s} p (s⁻¹ , s⁻¹∘s==id) {e = e} epi-e f
  with fbar , e∘fbar==f∘s⁻¹ ← p epi-e (f ∘ s⁻¹) =
  fbar ∘ s , (proof e ∘ (fbar ∘ s)
                === e ∘ fbar ∘ s   :by: assoc e fbar s
                === f ∘ s⁻¹ ∘ s    :by: ap (_∘ s) e∘fbar==f∘s⁻¹
                === f ∘ (s⁻¹ ∘ s)  :by: sym $ assoc f s⁻¹ s
                === f ∘ id R       :by: ap (f ∘_) s⁻¹∘s==id
                === f              :by: right-unit f
              qed)

open import Category.Opposite

dual-mono-epi : 
  {X Y : obj}(s : X ~> Y)
  → ----------------------
  mono s ↔ epi ⦃ ℂ ᵒᵖ ⦄ s
dual-mono-epi s = refl (mono s)
