{-# OPTIONS --exact-split --prop #-}
module Construction.Coequalizer.Definition where

import Construction.Equalizer.Definition as Equal
open Equal using (𝕀) public

open import PropUniverses
open import Category

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  open import Proposition.Identity

  open import Category.Opposite
  open import Construction.Cone.Definition 𝕀
    using (Diagram; Cocone)
  open Equal using (EqualizerDiagram; EqualizerCone; IsEqualizer; Equalizer)
  
  CoequalizerDiagram : {A B : obj}(f g : A ~> B) → Diagram ⦃ ℂ ᵒᵖ ⦄
  CoequalizerDiagram = EqualizerDiagram ⦃ ℂ ᵒᵖ ⦄

  CoequalizerCocone :
    {A B : obj}
    {f g : A ~> B}
    {Q : obj}
    (q : B ~> Q)
    (p : q ∘ f == q ∘ g)
    → -------------------------
    Cocone (CoequalizerDiagram f g) Q
  CoequalizerCocone = CoequalizerCocone' ℂ
    where CoequalizerCocone' =
            dual (λ ℂ {A}{B}{f}{g}{Q} → EqualizerCone ⦃ ℂ ⦄{A}{B}{f}{g}{Q})

  IsCoequalizer : 
    {A B : obj}
    (f g : A ~> B)
    (Q : obj)
    (q : B ~> Q)
    → ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  IsCoequalizer = IsCoequalizer' ℂ
    where IsCoequalizer' = dual λ ℂ {A B : obj ⦃ ℂ ⦄} →
                                IsEqualizer ⦃ ℂ ⦄ {A}{B}
  
  Coequalizer : {A B : obj}(f g : A ~> B) → 𝒰 ⊔ 𝒱 ˙
  Coequalizer = Coequalizer' ℂ
    where Coequalizer' = dual (λ ℂ {A}{B} → Equalizer ⦃ ℂ ⦄ {A}{B})

open WithFixedCategory public

