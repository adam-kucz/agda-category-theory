{-# OPTIONS --exact-split --prop #-}
module Construction.Equalizer.Definition where

open import Category
open import Category.Finite

open import PropUniverses
open import Type.Empty
import Data.Nat
open import Data.FinNat

𝕀 : Category 𝒰₀ 𝒰₀
𝕀 = Finite 2
      (λ { ₀ ₀ → 𝟘 ; ₀ ₁ → Finℕ 2 ; ₁ ₀ → 𝟘 ; ₁ ₁ → 𝟘})
      (λ { {₀}{₁}{₁} () ; {₁}{₁} _ () })
      λ { {₀} {₁} {₁} _ () ; {₁} {₁} _ _ () }

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  open import Type.BinarySum
  open import Type.Unit
  open import Proposition.Sum
  open import Proof

  open import Functor
  open import Construction.Cone.Definition 𝕀

  EqualizerDiagram : {A B : obj}(f g : A ~> B) → Diagram
  EqualizerDiagram {A} {B} f g =
    [F₀= F0 ,F₁= F1
    ,id-pres= (λ { ₀ → refl (id A) ; ₁ → refl (id B)})
    ,∘-pres= (λ { {₀} {₀} {₀} _ _ → sym $ left-unit (id A)
                ; {₁} {₁} {₁} _ _ → sym $ left-unit (id B)
                ; {₀} {₀} {₁} (inr ₀) f₁@(inl _) →
                  proof F1 (inr ₀ ∘[ 𝕀 ] f₁)
                    === F1 (inr ₀)
                      :by: ap F1 $ right-unit ⦃ 𝕀 ⦄ (inr ₀)
                    === f ∘ id A
                      :by: sym $ right-unit f
                  qed
                ; {₀} {₀} {₁} (inr ₁) f₁@(inl _) →
                  proof F1 (inr ₁ ∘[ 𝕀 ] f₁)
                    === F1 (inr ₁)
                      :by: ap F1 $ right-unit ⦃ 𝕀 ⦄ (inr ₁)
                    === g ∘ id A
                      :by: sym $ right-unit g
                  qed
                ; {₀} {₁} {₁} g₁@(inl _) (inr ₀) →
                  proof F1 (g₁ ∘[ 𝕀 ] inr ₀)
                    === F1 (inr ₀)
                      :by: ap F1 $ left-unit ⦃ 𝕀 ⦄ (inr ₀)
                    === id B ∘ f
                      :by: sym $ left-unit f
                  qed
                ; {₀} {₁} {₁} g₁@(inl _) (inr ₁) →
                  proof F1 (g₁ ∘[ 𝕀 ] inr ₁)
                    === F1 (inr ₁)
                      :by: ap F1 $ left-unit ⦃ 𝕀 ⦄ (inr ₁)
                    === id B ∘ g
                      :by: sym $ left-unit g
                  qed
                ; {₀} {₁} {₀} (inl ())
                ; {₀} {₁} {₀} (inr ())
                ; {₁} {₀} _ (inl ())
                ; {₁} {₀} _ (inr ())
                ; {₁} {₁} {₀} (inl ())}) ]
    where F0 : (X : obj ⦃ 𝕀 ⦄) → obj
          F0 ₀ = A
          F0 ₁ = B
          F1 : ∀{X}{Y}(f : mor 𝕀 X Y) → F0 X ~> F0 Y
          F1 {₀} {₀} _ = id A
          F1 {₁} {₁} _ = id B
          F1 {₀} {₁} (inr ₀) = f
          F1 {₀} {₁} (inr ₁) = g
          F1 {₁} {₀} (inl ())
          F1 {₁} {₀} (inr ())

  open import NaturalTransformation

  EqualizerCone :
    {A B : obj}
    {f g : A ~> B}
    {E : obj}
    (e : E ~> A)
    (p : f ∘ e == g ∘ e)
    → -------------------------
    Cone (EqualizerDiagram f g) E
  (EqualizerCone e _) at ₀ = e
  (EqualizerCone {f = f} e _) at ₁ = f ∘ e
  _⟹_.naturality (EqualizerCone e _) {₀} {₀} _ = sym $ bi-unit e
  _⟹_.naturality (EqualizerCone {f = f} e _) {₁} {₁} _ =
    sym $ bi-unit (f ∘ e)
  _⟹_.naturality (EqualizerCone {f = f} e _) {₀} {₁} (inr ₀) =
    right-unit (f ∘ e)
  _⟹_.naturality (EqualizerCone {f = f}{g}{E} e p) {₀} {₁} (inr ₁) =
    proof f ∘ e ∘ id E
      === f ∘ e        :by: right-unit (f ∘ e)
      === g ∘ e        :by: p
    qed
  _⟹_.naturality (EqualizerCone _ _) {₁} {₀} (inl ())
  _⟹_.naturality (EqualizerCone _ _) {₁} {₀} (inr ())

  open import Construction.Cone.Universal.Definition ⦃ ℂ ⦄ 𝕀
  
  IsEqualizer :
    {A B : obj}
    (f g : A ~> B)
    (E : obj)
    (e : E ~> A)
    → ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  IsEqualizer f g E e =
    f ∘ e == g ∘ e ∧ᵈ λ p → IsUniversalCone E (EqualizerCone e p)

  Equalizer : {A B : obj}(f g : A ~> B) → 𝒰 ⊔ 𝒱 ˙
  Equalizer f g = UniversalCone (EqualizerDiagram f g)

open WithFixedCategory public
