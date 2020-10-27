{-# OPTIONS --exact-split --prop #-}
module Construction.Equalizer.AsUniversalCone where

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
  EqualizerCone e _ at ₀ = e
  EqualizerCone {f = f} e _ at ₁ = f ∘ e
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

  ConeEq-prop : {A B : obj}{f g : A ~> B}{E : obj}
    (cone : Cone (EqualizerDiagram f g) E)
    → -----------------------------------------------------
    f ∘ cone at ₀ == g ∘ cone at ₀
  ConeEq-prop {f = f}{g}{E} cone =
    proof f ∘ cone at ₀
      === cone at ₁ ∘ id E :by: sym $ naturality (inr ₀)
      === g ∘ cone at ₀    :by: naturality (inr ₁)
    qed
    where instance _ = cone

  open import Type.Sum renaming (_,_ to _Σ,_)
  open import Proof

  import Construction.Equalizer.Definition as E

  EEqualizer→Equalizer : {A B : obj}{f g : A ~> B}
                         (E : E.Equalizer f g) → Equalizer f g
  EEqualizer→Equalizer {f = f}{g} E@(V Σ, e , p@(fg==ge , _)) =
    record { U = V ; cone = cone' ; universality = univ p }
    where cone' = EqualizerCone e fg==ge
          univ : E.IsEqualizer f g V e
                 → ----------------------------------------
                 IsUniversalCone V cone'
          to-universal ⦃ univ (fg==ge , q) ⦄ c
            with z , (c₀==ez , !z) ← q (c at ₀)(ConeEq-prop c) =
            z , ((λ { ₀ → c₀==ez
                    ; ₁ → proof c at ₁
                            === c at ₁ ∘ id _ :by: sym $ right-unit (c at ₁)
                            === f ∘ c at ₀    :by: naturality (inr ₀)
                            === f ∘ (e ∘ z)   :by: ap (f ∘_) c₀==ez
                            === f ∘ e ∘ z     :by: assoc f e z
                          qed}) ,
                 λ z' p' → !z z' $ p' ₀)
            where instance _ = c

  open import Logic

  Equalizer→EEqualizer : {A B : obj}{f g : A ~> B}
                         (E : Equalizer f g) → E.Equalizer f g
  Equalizer→EEqualizer {A}{B}{f}{g} E =
    V Σ, cone at ₀ , (
      (proof f ∘ cone at ₀
         === cone at ₁ ∘ id V :by: sym $ naturality ⦃ cone ⦄ (inr ₀)
         === g ∘ cone at ₀    :by: naturality ⦃ cone ⦄ (inr ₁)
       qed) ,
      λ e' p' → go e' p' $ to-universal (c e' p'))
    where instance _ = E
          V = U
          c = EqualizerCone
          go : {V' : obj}(e' : V' ~> A)(p' : f ∘ e' == g ∘ e')
               (p : ∃! λ (f : V' ~> V) → ∀ X → c e' p' at X == cone at X ∘ f)
               → ----------------------------------------------------------
               ∃! λ (!z : V' ~> V) → e' == cone at ₀ ∘ !z
          go e' p' (z , (p , !z)) =
            z , (p ₀ , λ z' pz → !z z' λ
              { ₀ → pz ; ₁ →
              proof f ∘ e'
                === f ∘ (cone at ₀ ∘ z') :by: ap (f ∘_) pz
                === f ∘ cone at ₀ ∘ z'   :by: assoc f (cone at ₀) z'
                === cone at ₁ ∘ id _ ∘ z'
                  :by: sym $ ap (_∘ z') $ naturality ⦃ cone ⦄ (inr ₀)
                === cone at ₁ ∘ z'
                  :by: ap (_∘ z') $ right-unit (cone at ₁)
              qed})
  
  open import Morphism.Iso
  
  Equalizer≅ : {A B : obj}{f g : A ~> B}
    (E : Equalizer f g)
    (E' : E.Equalizer f g)
    → --------------------
    U ⦃ E ⦄ ≅ pr₁ (elem E')
  Equalizer≅ {f = f}{g} E (V' Σ, e' , (p , !e'))
    with !e' (cone at ₀)(ConeEq-prop cone) | to-universal (EqualizerCone e' p)
       | !e' e' p | to-universal (EqualizerCone (cone at ₀)(ConeEq-prop cone))
    where instance _ = E
  ... | z , (pz , !z) | z⁻¹ , (pz⁻¹ , !z⁻¹) | !id | !id' =
    z , (z⁻¹ , (
    ∃!== !id (
      proof e'
        === cone at ₀ ∘ z⁻¹ :by: pz⁻¹ ₀
        === e' ∘ z ∘ z⁻¹    :by: ap (_∘ z⁻¹) pz
        === e' ∘ (z ∘ z⁻¹)  :by: sym $ assoc e' z z⁻¹
      qed)
      (sym $ right-unit e') ,
    ∃!== !id' (
      λ { ₀ → proof cone at ₀
                === e' ∘ z                :by: pz
                === cone at ₀ ∘ z⁻¹ ∘ z   :by: ap (_∘ z) $ pz⁻¹ ₀
                === cone at ₀ ∘ (z⁻¹ ∘ z) :by: sym $ assoc _ z⁻¹ z
              qed
        ; ₁ → proof f ∘ cone at ₀
                === f ∘ (e' ∘ z)          :by: ap (f ∘_) pz
                === f ∘ e' ∘ z            :by: assoc f e' z
                === cone at ₁ ∘ z⁻¹ ∘ z   :by: ap (_∘ z) $ pz⁻¹ ₁
                === cone at ₁ ∘ (z⁻¹ ∘ z) :by: sym $ assoc _ z⁻¹ z
              qed})
      λ { ₀ → sym $ right-unit (cone at ₀)
        ; ₁ → sym $ naturality ⦃ cone ⦄ (inr ₀)}))
    where instance _ = E

open WithFixedCategory public

HasEqualizers : (ℂ : Category 𝒲 𝒯) → 𝒲 ⊔ 𝒯 ˙
HasEqualizers ℂ = ∀{A B : obj}{f g : A ~> B} → Equalizer f g
  where instance _ = ℂ

