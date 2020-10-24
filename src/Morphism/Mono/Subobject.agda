{-# OPTIONS --exact-split --safe --prop #-}
open import Category
open import PropUniverses hiding (X; Y)

module Morphism.Mono.Subobject where

open import Morphism.Mono.Definition

open import Proposition.Sum
open import Type.Sum renaming (_,_ to _Σ,_)

subobject-of : ⦃ ℂ : Category 𝒰 𝒱 ⦄ (X : obj) → 𝒰 ⊔ 𝒱 ˙
subobject-of X = Σ λ (M : obj) → Σₚ λ (m : M ~> X) → m ˸ M ⤚→ X

open import Proof

Sub_[_] : (ℂ : Category 𝒰 𝒱)(X : obj ⦃ ℂ ⦄) → Category (𝒰 ⊔ 𝒱) 𝒱
Sub ℂ [ X ] = record
  { obj = subobject-of X
  ; _~>_ = λ { (M Σ, (m , p)) (M' Σ, (m' , p')) →
    Σₚ λ (f : M ~> M') → m' ∘ f == m}
  ; id = λ { (M Σ, (m , p)) → id M , right-unit m}
  ; _∘_ = λ { {M Σ, (m , p)}{M' Σ, (m' , p')}{M″ Σ, (m″ , p″)}
              (g , m″∘g==m')(f , m'∘f==m) → g ∘ f , (
                proof m″ ∘ (g ∘ f)
                  === m″ ∘ g ∘ f :by: assoc m″ g f
                  === m' ∘ f     :by: ap (_∘ f) m″∘g==m'
                  === m          :by: m'∘f==m
                qed)}
  ; left-unit = λ { (f , _) → Σₚ== $ left-unit f}
  ; right-unit = λ { (f , _) → Σₚ== $ right-unit f}
  ; assoc = λ { (f , _)(g , _)(h , _) → Σₚ== $ assoc f g h}
  }
  where instance _ = ℂ

open import Proposition.Exists

_⊆_ _≡_ : ⦃ ℂ : Category 𝒰 𝒱 ⦄{X : obj}(m m' : subobject-of X) → 𝒱 ᵖ
_⊆_ ⦃ ℂ ⦄{X} m m' = Exists (mor Sub ℂ [ X ] m m')

m ≡ m' = m ⊆ m' ∧ m' ⊆ m

open import Morphism.Iso

≡-subobjects-have-≅-domains :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄{X : obj}{m m' : subobject-of X}
  (p : m ≡ m')
  → ------------------------------------------------------
  pr₁ m ≅ pr₁ m'
≡-subobjects-have-≅-domains {m = M Σ, (m , monic)}{M' Σ, (m' , monic')}
  (an (f , m'∘f==m) , an (f⁻¹ , m∘f⁻¹==m')) =
  f , (f⁻¹ , (
  monic' (proof m' ∘ (f ∘ f⁻¹)
            === m' ∘ f ∘ f⁻¹ :by: assoc m' f f⁻¹
            === m ∘ f⁻¹      :by: ap (_∘ f⁻¹) m'∘f==m
            === m'           :by: m∘f⁻¹==m'
            === m' ∘ id M'   :by: sym $ right-unit m'
          qed) ,
  monic (proof m ∘ (f⁻¹ ∘ f)
           === m ∘ f⁻¹ ∘ f :by: assoc m f⁻¹ f
           === m' ∘ f      :by: ap (_∘ f) m∘f⁻¹==m'
           === m           :by: m'∘f==m
           === m ∘ id M    :by: sym $ right-unit m
         qed)))

open import Proposition.Proof

Sub-mor-is-monic : ∀
  ⦃ ℂ : Category 𝒰 𝒱 ⦄{X : obj}{M M'}
  (f : mor Sub ℂ [ X ] M' M)
  → -----------------------------------------
  monic (elem f)
Sub-mor-is-monic {M = M Σ, (m , monic)}{M' Σ, (m' , monic')}
  (f , mf==m') {g = g}{h} fg==fh =
  monic' (proof m' ∘ g
            === m ∘ f ∘ g   :by: ap (_∘ g) $ sym mf==m'
            === m ∘ (f ∘ g) :by: sym $ assoc m f g
            === m ∘ (f ∘ h) :by: ap (m ∘_) fg==fh
            === m ∘ f ∘ h   :by: assoc m f h
            === m' ∘ h      :by: ap (_∘ h) mf==m'
          qed)

open import Functor

SubobjectFunctor : ∀
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  (X : obj)
  (M : obj ⦃ Sub ℂ [ X ] ⦄)
  → ---------------------------------------
  Functor Sub ℂ [ pr₁ M ] Sub ℂ [ X ]
SubobjectFunctor X (M Σ, (m , monic-m)) =
  [F₀= (λ { (M' Σ, (f , monic-f)) →
            M' Σ, (m ∘ f , ∘-monic-closed monic-m monic-f)})
  ,F₁= (λ { {M' Σ, (f' , monic-f')} {M″ Σ, (f″ , monic-f″)} (g , f″g==f') →
          g , (proof m ∘ f″ ∘ g
                 === m ∘ (f″ ∘ g) :by: sym $ assoc m f″ g
                 === m ∘ f'       :by: ap (m ∘_) f″g==f'
               qed)})
  ,id-pres= (λ _ → refl _)
  ,∘-pres= (λ _ _ → refl _) ]

local-membership : ⦃ ℂ : Category 𝒰 𝒱 ⦄{Z X : obj}
  (z : Z ~> X)(M : subobject-of X)
  → --------------------------------------------------
  𝒱 ᵖ
local-membership {Z = Z} z (M Σ, (m , _)) =
  ∃ λ (f : Z ~> M) → m ∘ f == z

local-membership-syntax : ⦃ ℂ : Category 𝒰 𝒱 ⦄{Z : obj}
  (X : obj)(z : Z ~> X)(M : subobject-of X)
  → --------------------------------------------------
  𝒱 ᵖ
local-membership-syntax _ z M = local-membership z M

syntax local-membership-syntax X z M = z ∈[ X ] M

