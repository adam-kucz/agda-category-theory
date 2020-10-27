{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Category
module Construction.Pullback.Syntax ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Type.Sum renaming (_,_ to _Σ,_) hiding (〈_,_〉)
open import Proposition.Sum

open import Axiom.UniqueChoice

open import Construction.Pullback.Definition as Pull

infixl 181 _×[_]_ explicit×
_×[_]_ : (A C B : obj){f : A ~> C}{g : B ~> C}⦃ P : Pullback f g ⦄ → obj
(A ×[ C ] B) ⦃ P Σ, _ , _ ⦄ = P

explicit× : (A B C : obj)(f : A ~> C)(g : B ~> C)⦃ P : Pullback f g ⦄ → obj
explicit× A B C f g ⦃ P Σ, _ , _ ⦄ = P

syntax explicit× A B C f g = A ×[ f ~> C <~ g ] B

private
  module Properties {A B C : obj}
                    {f : A ~> C}{g : B ~> C}
                    ⦃ P : Pullback f g ⦄
                    where
    open import Logic
    open import Proof

    p₁ : A ×[ C ] B ~> A
    p₁ = pr₁ (pr₂ (elem P))
    p₂ : A ×[ C ] B ~> B
    p₂ = pr₂ (pr₂ (elem P))

    get-mor :
      {Z : obj}
      (z₁ : Z ~> A)
      (z₂ : Z ~> B)
      (p : f ∘ z₁ == g ∘ z₂)
      → ------------------
      Σₚ λ (u : Z ~> A ×[ C ] B) → p₁ ∘ u == z₁ ∧ p₂ ∘ u == z₂  ∧
         ∀ (u' : Z ~> A ×[ C ] B) (p : p₁ ∘ u' == z₁  ∧ p₂ ∘ u' == z₂) →
         u' == u
    get-mor z₁ z₂ p = !choice (∧right (prop P) z₁ z₂ p)
    
    〈_,_〉 :
      {Z : obj}
      (z₁ : Z ~> A)
      (z₂ : Z ~> B)
      ⦃ p : f ∘ z₁ == g ∘ z₂ ⦄
      → ------------------
      Z ~> A ×[ C ] B
    〈 z₁ , z₂ 〉 = elem (get-mor z₁ z₂ from-instance)

open Properties hiding (get-mor) public
