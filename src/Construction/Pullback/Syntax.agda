{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Category
module Construction.Pullback.Syntax {ℂ : Category 𝒰 𝒱} where

open import Axiom.UniqueChoice

open import Construction.Pullback.Definition as Pull
open import Construction.Cone.Universal.Definition ⦃ ℂ ⦄ 𝕀

private
  instance _ = ℂ

infixl 181 _×[_]_ explicit×
_×[_]_ : (A C B : obj){f : A ~> C}{g : B ~> C}⦃ P : Pullback f g ⦄ → obj
A ×[ C ] B = U

explicit× : (A B C : obj)(f : A ~> C)(g : B ~> C)⦃ P : Pullback f g ⦄ → obj
explicit× A B C f g = U

syntax explicit× A B C f g = A ×[ f ~> C <~ g ] B

private
  module Properties {A B C : obj}
                    {f : A ~> C}{g : B ~> C}
                    ⦃ P : Pullback f g ⦄
                    where

    open import Type.Unit  
    open import Type.BinarySum  
    open import Proposition.Sum
    open import Data.FinNat  
    open import Logic
    open import Proof

    open import NaturalTransformation

    p₁ = cone at ₁
    p₂ = cone at ₂

    get-mor :
      {Z : obj}
      (z₁ : Z ~> A)
      (z₂ : Z ~> B)
      (p : f ∘ z₁ == g ∘ z₂)
      → ------------------
      Σₚ λ (u : Z ~> A ×[ C ] B) → z₁ == p₁ ∘ u ∧ z₂ == p₂ ∘ u ∧
        ∀ (u' : Z ~> A ×[ C ] B) (p : z₁ == p₁ ∘ u' ∧ z₂ == p₂ ∘ u') → u' == u
    get-mor z₁ z₂ p = !choice (⟶ (↔→∃!↔∃! λ u →
      (λ q → q ₁ , q ₂) ,
      (λ { (q₁ , q₂) ₀ →
        proof f ∘ z₁
          === f ∘ (cone at ₁ ∘ u)  :by: ap (f ∘_) q₁
          === f ∘ cone at ₁ ∘ u    :by: assoc f _ u
          === cone at ₀ ∘ id (A ×[ C ] B) ∘ u
            :by: ap (_∘ u) $ sym $ naturality ⦃ cone ⦄ {₁}{₀} (inr ⋆)
          === cone at ₀ ∘ u   :by: ap (_∘ u) $ right-unit (cone at ₀)
          qed 
         ; (q₁ , _) ₁ → q₁
         ; (_ , q₂) ₂ → q₂})
      ) p')
      where p' = to-universal (PullbackCone z₁ z₂ p)
    
    〈_,_〉 :
      {Z : obj}
      (z₁ : Z ~> A)
      (z₂ : Z ~> B)
      ⦃ p : f ∘ z₁ == g ∘ z₂ ⦄
      → ------------------
      Z ~> A ×[ C ] B
    〈 z₁ , z₂ 〉 = elem (get-mor z₁ z₂ from-instance)

open Properties hiding (get-mor) public
