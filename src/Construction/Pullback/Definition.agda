{-# OPTIONS --exact-split --prop #-}
module Construction.Pullback.Definition where

open import Category
open import Category.Finite

open import PropUniverses
open import Type.Empty
open import Type.Unit
open import Type.BinarySum
import Data.Nat
open import Data.FinNat
open import Proof


𝕀 : Category 𝒰₀ 𝒰₀
𝕀 = Finite 3
  (λ { _ (_ +1) → 𝟘
     ; ₀ ₀ → 𝟘
     ; ₁ ₀ → 𝟙
     ; ₂ ₀ → 𝟙 })
  (λ { {_}{₀}{₀} ()
     ; {_}{₀}{_ +1} ()})
  λ { {Z = ₀}{₀} ()
    ; {Z = ₀}{_ +1} ()}

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  open import Type.Unit
  open import Proposition.Sum
  open import Proof

  open import Functor
  open import Construction.Cone.Definition 𝕀

  PullbackDiagram : {A B C : obj}(f : A ~> C)(g : B ~> C) → Diagram
  PullbackDiagram {A}{B}{C} f g =
    [F₀= F0
    ,F₁= F1
    ,id-pres= (λ { ₀ → refl (id C) ; ₁ → refl (id A) ; ₂ → refl (id B)})
    ,∘-pres= (λ { {₀}{₀}{₀} _ _ → sym $ left-unit (id C)
                ; {₁}{₁} g₁ f₁@(inl _) →
                  proof F1 (g₁ ∘[ 𝕀 ] f₁)
                    === F1 g₁        :by: ap F1 $ right-unit ⦃ 𝕀 ⦄ g₁
                    === F1 g₁ ∘ id A :by: sym $ right-unit (F1 g₁)
                  qed
                ; {₂}{₂} g₁ f₁@(inl _) →
                  proof F1 (g₁ ∘[ 𝕀 ] f₁)
                    === F1 g₁        :by: ap F1 $ right-unit ⦃ 𝕀 ⦄ g₁
                    === F1 g₁ ∘ id B :by: sym $ right-unit (F1 g₁)
                  qed
                ; {₁}{₀}{₀} _ _ → sym $ left-unit f
                ; {₂}{₀}{₀} _ _ → sym $ left-unit g
                ; {₀}{_ +1} _ (inl ())
                ; {₀}{_ +1} _ (inr ())
                ; {₀}{₀}{_ +1}(inl ())
                ; {₀}{₀}{_ +1}(inr ())
                ; {₁}{₀}{_ +1}(inl ())
                ; {₁}{₀}{_ +1}(inr ())
                ; {₂}{₀}{_ +1}(inl ())
                ; {₂}{₀}{_ +1}(inr ())
                ; {₁}{₂} _ (inl ())
                ; {₁}{₂} _ (inr ())
                ; {₂}{₁} _ (inl ())
                ; {₂}{₁} _ (inr ())
    })]
    where F0 : (X : obj ⦃ 𝕀 ⦄) → obj
          F0 ₀ = C
          F0 ₁ = A
          F0 ₂ = B
          F1 : ∀{X}{Y}(f : mor 𝕀 X Y) → F0 X ~> F0 Y
          F1 {₀}{₀} _ = id C
          F1 {₁} {₀} _ = f
          F1 {₁} {₁} _ = id A
          F1 {₂} {₀} _ = g
          F1 {₂} {₂} _ = id B
          F1 {₀} {_ +1} (inl ())
          F1 {₀} {_ +1} (inr ())
          F1 {₁} {₂} (inl ())
          F1 {₁} {₂} (inr ())
          F1 {₂} {₁} (inl ())
          F1 {₂} {₁} (inr ())

  open import NaturalTransformation

  PullbackCone :
    {A B C : obj}
    {f : A ~> C}
    {g : B ~> C}
    {P : obj}
    (p₀ : P ~> A)
    (p₁ : P ~> B)
    (fp₀==gp₁ : f ∘ p₀ == g ∘ p₁)
    → -------------------------
    Cone (PullbackDiagram f g) P
  PullbackCone {f = f} p₀ _ _ at ₀ = f ∘ p₀
  PullbackCone p₀ _ _ at ₁ = p₀
  PullbackCone _ p₁ _ at ₂ = p₁
  _⟹_.naturality (PullbackCone {f = f}{g}{P} p₀ p₁ fp₀==gp₁) {X}{Y} k =
    let PCat = PullbackCone p₀ p₁ fp₀==gp₁ at_ in
    proof PCat Y ∘ id P
      === PCat Y        :by: right-unit (PCat Y)
      === F₁ k ∘ PCat X :by: go X Y k
    qed
    where instance D = PullbackDiagram f g
          go : (X Y : obj ⦃ 𝕀 ⦄)(k : mor 𝕀 X Y) →
               let PCat = PullbackCone p₀ p₁ fp₀==gp₁ at_ in
               PCat Y == F₁ k ∘ PCat X
          go ₀ ₀ _ = sym $ left-unit (f ∘ p₀)
          go ₁ ₀ _ = refl (f ∘ p₀)
          go ₂ ₀ _ = fp₀==gp₁
          go ₁ ₁ _ = sym $ left-unit p₀
          go ₂ ₂ _ = sym $ left-unit p₁
          go ₀ (_ +1)(inl ())
          go ₀ (_ +1)(inr ())
          go ₁ ₂ (inl ())
          go ₁ ₂ (inr ())
          go ₂ ₁ (inl ())
          go ₂ ₁ (inr ())

  open import Construction.Cone.Universal.Definition ⦃ ℂ ⦄ 𝕀
  
  IsPullback :
    {A B C : obj}
    (f : A ~> C)
    (g : B ~> C)
    (P : obj)
    (p₀ : P ~> A)
    (p₁ : P ~> B)
    → ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  IsPullback f g P p₀ p₁ =
    f ∘ p₀ == g ∘ p₁ ∧ᵈ λ p → IsUniversalCone P (PullbackCone p₀ p₁ p)

  Pullback : {A B C : obj}(f : A ~> C)(g : B ~> C) → 𝒰 ⊔ 𝒱 ˙
  Pullback f g = UniversalCone (PullbackDiagram f g)

open WithFixedCategory public
