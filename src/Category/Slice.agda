{-# OPTIONS --exact-split --safe --prop #-}
module Category.Slice where

open import Category.Definition

open import Universes
open import Type.Sum
open import Proposition.Sum renaming (_,_ to _,,_)
open import Proposition.Identity
open import Proof

_╱_ : (ℂ : Category 𝒰 𝒱) (A : obj ⦃ ℂ ⦄) → Category (𝒰 ⊔ 𝒱) 𝒱
ℂ ╱ A = record
  { obj = Σ λ (X : obj) → X ~> A
  ; _~>_ = λ { (X , f) (Y , g) → Σₚ λ (h : X ~> Y) → g ∘ h == f }
  ; id = λ { (X , f) → id X ,, right-unit f }
  ; _∘_ = λ { {(X , f)} {(Y , g)} {(Z , h)} (i₁ ,, p₁) (i₂ ,, p₂) → i₁ ∘ i₂ ,,
    (proof h ∘ (i₁ ∘ i₂)
      〉 _==_ 〉 h ∘ i₁ ∘ i₂ :by: assoc h i₁ i₂
      〉 _==_ 〉 g ∘ i₂     :by: ap (_∘ i₂) p₁
      〉 _==_ 〉 f         :by: p₂
    qed)}
  ; left-unit = λ { (i ,, _) → Σₚ== (left-unit i) }
  ; right-unit = λ { (i ,, _) → Σₚ== (right-unit i) }
  ; assoc = λ { (i₁ ,, p₁) (i₂ ,, p₂) (i₃ ,, p₃) → Σₚ== (assoc i₁ i₂ i₃) }
  }
  where instance _ = ℂ

open import Functor
open import Relation.Binary.Property using (sym)

CompositionFunctor :
  {ℂ : Category 𝒰 𝒱}
  → let instance _ = ℂ in
  {A B : obj}
  (f : A ~> B)
  → -----------------------
  Functor (ℂ ╱ A) (ℂ ╱ B)
CompositionFunctor {ℂ = ℂ} f₁ = record
  { F₀ = λ { (X , f) → X , f₁ ∘ f }
  ; F₁ = λ { {X , f} {Y , g} (i ,, p) → i ,,
    (proof f₁ ∘ g ∘ i
      === f₁ ∘ (g ∘ i) :by: sym (assoc f₁ g i)
      === f₁ ∘ f       :by: ap (f₁ ∘_) p
    qed) }
  ; id-preserv = λ { (X , _) → Σₚ== (Id.refl (id X)) }
  ; ∘-preserv = λ { (i₁ ,, p₁) (i₂ ,, p₂) → Σₚ== (Id.refl (i₁ ∘ i₂)) }
  }
  where instance _ = ℂ

