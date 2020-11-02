{-# OPTIONS --exact-split --prop #-}
module Construction.Pullback.Definition where

open import PropUniverses
open import Category

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  open import Type.Sum renaming (_,_ to _Σ,_)
  open import Proposition.Sum
  open import Proposition.Identity
  open import Logic

  IsPullback :
    {A B C : obj}
    (f : A ~> C)
    (g : B ~> C)
    (P : obj)
    (p₁ : P ~> A)
    (p₂ : P ~> B)
    → ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  IsPullback {A}{B}{C} f g P p₁ p₂ =
    f ∘ p₁ == g ∘ p₂ ∧
    ∀{X : obj}(p₁' : X ~> A)(p₂' : X ~> B)(q : f ∘ p₁' == g ∘ p₂') →
    ∃! λ (〈p₁',p₂'〉 : X ~> P) →
    p₁ ∘ 〈p₁',p₂'〉 == p₁' ∧ p₂ ∘ 〈p₁',p₂'〉 == p₂'

  Pullback : {A B C : obj}(f : A ~> C)(g : B ~> C) → 𝒰 ⊔ 𝒱 ˙
  Pullback {A}{B} f g =
    Σₚ {X = Σ λ (P : obj) → P ~> A × P ~> B }
       λ { (P Σ, (p₁ Σ, p₂)) → IsPullback f g P p₁ p₂}

open WithFixedCategory public

HasPullbacks : (ℂ : Category 𝒲 𝒯) → 𝒲 ⊔ 𝒯 ˙
HasPullbacks ℂ = ∀{A B C : obj}{f : A ~> C}{g : B ~> C} → Pullback f g
  where instance _ = ℂ

