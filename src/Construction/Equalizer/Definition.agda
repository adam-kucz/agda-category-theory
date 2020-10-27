{-# OPTIONS --exact-split --prop #-}
module Construction.Equalizer.Definition where

open import PropUniverses
open import Category

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  open import Type.Sum renaming (_,_ to _Σ,_)
  open import Proposition.Identity
  open import Proposition.Sum
  open import Logic
  
  IsEqualizer :
    {A B : obj}
    (f g : A ~> B)
    (E : obj)
    (e : E ~> A)
    → ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  IsEqualizer {A}{B} f g E e =
    f ∘ e == g ∘ e ∧
    ∀{V : obj}(e' : V ~> A)(p : f ∘ e' == g ∘ e') →
    ∃! λ (z : V ~> E) → e' == e ∘ z

  Equalizer : {A B : obj}(f g : A ~> B) → 𝒰 ⊔ 𝒱 ˙
  Equalizer {A} f g = Σₚ {X = Σ λ (E : obj) → E ~> A }
                         λ { (E Σ, e) → IsEqualizer f g E e }

open WithFixedCategory public

HasEqualizers : (ℂ : Category 𝒲 𝒯) → 𝒲 ⊔ 𝒯 ˙
HasEqualizers ℂ = ∀{A B : obj}{f g : A ~> B} → Equalizer f g
  where instance _ = ℂ

