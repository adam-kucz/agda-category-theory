{-# OPTIONS --exact-split --prop #-}
module Construction.Pullback.AsUniversalCone where

open import Category
open import Category.Finite

open import PropUniverses
open import Type.Empty
open import Type.Unit
open import Type.BinarySum
import Data.Nat
open import Data.FinNat

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

module WithFixedCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄{A B C : obj} where
  open import Type.Unit
  open import Proposition.Sum
  open import Proof

  open import Functor
  open import Construction.Cone.Definition 𝕀

  PullbackDiagram : (f : A ~> C)(g : B ~> C) → Diagram
  PullbackDiagram f g =
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
    {f : A ~> C}
    {g : B ~> C}
    {P : obj}
    (p₀ : P ~> A)
    (p₁ : P ~> B)
    (fp₀==gp₁ : f ∘ p₀ == g ∘ p₁)
    → -------------------------
    Cone (PullbackDiagram f g) P
  PullbackCone {f} p₀ _ _ at ₀ = f ∘ p₀
  PullbackCone p₀ _ _ at ₁ = p₀
  PullbackCone _ p₁ _ at ₂ = p₁
  _⟹_.naturality (PullbackCone {f}{g}{P} p₀ p₁ fp₀==gp₁) {X}{Y} k =
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
    (f : A ~> C)
    (g : B ~> C)
    (P : obj)
    (p₀ : P ~> A)
    (p₁ : P ~> B)
    → ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  IsPullback f g P p₀ p₁ =
    f ∘ p₀ == g ∘ p₁ ∧ᵈ λ p → IsUniversalCone P (PullbackCone p₀ p₁ p)

  Pullback : (f : A ~> C)(g : B ~> C) → 𝒰 ⊔ 𝒱 ˙
  Pullback f g = UniversalCone (PullbackDiagram f g)

  ConePull-prop : {f : A ~> C}{g : B ~> C}{V : obj}
    (cone : Cone (PullbackDiagram f g) V)
    → -----------------------------------------------------
    f ∘ cone at ₁ == g ∘ cone at ₂
  ConePull-prop {f}{g}{V} cone =
    proof f ∘ cone at ₁
      === cone at ₀ ∘ id V :by: sym $ naturality (inr ⋆)
      === g ∘ cone at ₂    :by: naturality (inr ⋆)
    qed
    where instance _ = cone

  import Construction.Pullback.Definition as P
  import Construction.Pullback.Syntax as SP

  PPullback→Pullback : {f : A ~> C}{g : B ~> C}
    (P : P.Pullback f g) → Pullback f g
  PPullback→Pullback {f}{g} P@(_ , p@(fp₁==gp₂ , _)) =
    record { U = A SP.×[ C ] B ; cone = cone' ; universality = univ p }
    where instance _ = P
          cone' = PullbackCone SP.p₁ SP.p₂ fp₁==gp₂
          univ : P.IsPullback f g (A SP.×[ C ] B) SP.p₁ SP.p₂
                 → -------------------------------------------
                 IsUniversalCone (A SP.×[ C ] B) cone'
          to-universal ⦃ univ (q , ump) ⦄ c
            with u , (p₁u==c₁ , p₂u==c₂ , !u) ←
            ump (c at ₁)(c at ₂)(ConePull-prop c) =
            u , ((λ { ₀ → proof c at ₀
                            === c at ₀ ∘ id _ :by: sym $ right-unit (c at ₀)
                            === f ∘ c at ₁    :by: naturality ⦃ c ⦄ (inr ⋆)
                            === f ∘ (SP.p₁ ∘ u) :by: ap (f ∘_) $ sym p₁u==c₁
                            === f ∘ SP.p₁ ∘ u :by: assoc f SP.p₁ u
                          qed
                    ; ₁ → sym p₁u==c₁
                    ; ₂ → sym p₂u==c₂}) ,
                λ u' p' → !u u' (sym (p' ₁) , sym (p' ₂)))

  open import Type.Sum renaming (_,_ to _Σ,_) hiding (_×_)
  open import Logic
  
  Pullback→PPullback : {f : A ~> C}{g : B ~> C}
    (P : Pullback f g) → P.Pullback f g
  Pullback→PPullback {f}{g} P =
    V Σ, (cone at ₁ Σ, cone at ₂) , (ConePull-prop cone ,
    λ p₀' p₁' fp₀'==gp₁' → go p₀' p₁' fp₀'==gp₁' $
                           to-universal (c p₀' p₁' fp₀'==gp₁'))
    where instance _ = P
          V = U
          c = PullbackCone
          go : {V' : obj}
               (p₀' : V' ~> A)(p₁' : V' ~> B)
               (q : f ∘ p₀' == g ∘ p₁')
               (p : ∃! λ (f : V' ~> V) → ∀ X →
                    c p₀' p₁' q at X == cone at X ∘ f)
               → ----------------------------------------------------------
               ∃! λ (!f : V' ~> V) →
               cone at ₁ ∘ !f == p₀' ∧
               cone at ₂ ∘ !f == p₁'
          go p₀' p₁' fp₀'==gp₁' (z , (p , !z)) =
            z , ((sym (p ₁) , sym (p ₂)) ,
                λ {z' (c₁z'==p₀' , c₂z'==p₁') → !z z' λ
                  { ₀ → proof f ∘ p₀'
                          === f ∘ (cone at ₁ ∘ z')
                            :by: ap (f ∘_) $ sym c₁z'==p₀'
                          === f ∘ cone at ₁ ∘ z' :by: assoc f (cone at ₁) z'
                          === (cone at ₀ ∘ id _) ∘ z'
                            :by: ap (_∘ z') $ sym $ naturality ⦃ cone ⦄ (inr ⋆)
                          === cone at ₀ ∘ z'
                            :by: ap (_∘ z') $ right-unit (cone at ₀)
                        qed
                  ; ₁ → sym c₁z'==p₀'
                  ; ₂ → sym c₂z'==p₁'}})
  
  open import Morphism.Iso
  
  Pullback≅ : {f : A ~> C}{g : B ~> C}
    (P : Pullback f g)
    (P' : P.Pullback f g)
    → --------------------
    let instance _ = P; _ = P' in
    U ≅ A SP.×[ C ] B
  Pullback≅ {f}{g} P P'@(_ Σ, (p₁ Σ, p₂) , (fp₁==gp₂ , p))
    with p (cone at ₁)(cone at ₂)(ConePull-prop cone)
       | to-universal (PullbackCone p₁ p₂ fp₁==gp₂)
       | p p₁ p₂ fp₁==gp₂ | to-universal cone
    where instance _ = P; _ = P'
  ... | z , (pz₁ , pz₂ , !z) | z⁻¹ , (pz⁻¹ , !z⁻¹) | !id | !id' =
    z , (z⁻¹ , (
    ∃!== !id ((
      proof p₁ ∘ (z ∘ z⁻¹)
        === p₁ ∘ z ∘ z⁻¹    :by: assoc p₁ z z⁻¹
        === cone at ₁ ∘ z⁻¹ :by: ap (_∘ z⁻¹) pz₁
        === p₁              :by: sym $ pz⁻¹ ₁
      qed) , (
      proof p₂ ∘ (z ∘ z⁻¹)
        === p₂ ∘ z ∘ z⁻¹    :by: assoc p₂ z z⁻¹
        === cone at ₂ ∘ z⁻¹ :by: ap (_∘ z⁻¹) pz₂
        === p₂              :by: sym $ pz⁻¹ ₂
      qed))
      (right-unit p₁ , right-unit p₂) ,
    ∃!== !id' (
      λ { ₀ → proof cone at ₀
                === cone at ₀ ∘ id _      :by: sym $ right-unit (cone at ₀)
                === f ∘ cone at ₁         :by: naturality ⦃ cone ⦄ (inr ⋆)
                === f ∘ (p₁ ∘ z)          :by: ap (f ∘_) $ sym pz₁
                === f ∘ p₁ ∘ z            :by: assoc f p₁ z
                === cone at ₀ ∘ z⁻¹ ∘ z   :by: ap (_∘ z) $ pz⁻¹ ₀
                === cone at ₀ ∘ (z⁻¹ ∘ z) :by: sym $ assoc _ z⁻¹ z
              qed
        ; ₁ → proof cone at ₁
                === p₁ ∘ z                :by: sym pz₁
                === cone at ₁ ∘ z⁻¹ ∘ z   :by: ap (_∘ z) $ pz⁻¹ ₁
                === cone at ₁ ∘ (z⁻¹ ∘ z) :by: sym $ assoc _ z⁻¹ z
              qed
        ; ₂ → proof cone at ₂
                === p₂ ∘ z                :by: sym pz₂
                === cone at ₂ ∘ z⁻¹ ∘ z   :by: ap (_∘ z) $ pz⁻¹ ₂
                === cone at ₂ ∘ (z⁻¹ ∘ z) :by: sym $ assoc _ z⁻¹ z
              qed})
      λ { ₀ → sym $ right-unit (cone at ₀)
        ; ₁ → sym $ right-unit (cone at ₁)
        ; ₂ → sym $ right-unit (cone at ₂)}))
    where instance _ = P; _ = P'

open WithFixedCategory public

HasPullbacks : (ℂ : Category 𝒲 𝒯) → 𝒲 ⊔ 𝒯 ˙
HasPullbacks ℂ = ∀{A B C : obj}{f : A ~> C}{g : B ~> C} → Pullback f g
  where instance _ = ℂ

