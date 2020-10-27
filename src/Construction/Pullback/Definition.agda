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
    (p₀ : P ~> A)
    (p₁ : P ~> B)
    → ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  IsPullback {A}{B}{C} f g P p₀ p₁ =
    f ∘ p₀ == g ∘ p₁ ∧
    ∀{X : obj}(p₀' : X ~> A)(p₁' : X ~> B)(q : f ∘ p₀' == g ∘ p₁') →
    ∃! λ (〈p₀',p₁'〉 : X ~> P) →
    p₀ ∘ 〈p₀',p₁'〉 == p₀' ∧ p₁ ∘ 〈p₀',p₁'〉 == p₁'

  Pullback : {A B C : obj}(f : A ~> C)(g : B ~> C) → 𝒰 ⊔ 𝒱 ˙
  Pullback {A}{B} f g =
    Σₚ {X = Σ λ (P : obj) → P ~> A × P ~> B }
       λ { (P Σ, (p₀ Σ, p₁)) → IsPullback f g P p₀ p₁}

open WithFixedCategory public

HasPullbacks : (ℂ : Category 𝒲 𝒯) → 𝒲 ⊔ 𝒯 ˙
HasPullbacks ℂ = ∀{A B C : obj}{f : A ~> C}{g : B ~> C} → Pullback f g
  where instance _ = ℂ

