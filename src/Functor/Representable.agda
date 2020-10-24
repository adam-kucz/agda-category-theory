{-# OPTIONS --exact-split --prop #-}
module Functor.Representable where

open import Universes
open import Category
open import Functor.Definition
open import Example.Set'

open import Axiom.FunctionExtensionality

open import Relation.Binary.Property using (sym)
open import Proof

infix 245 _[_,—] _[—,_]
RepresentableFunctor-cov _[_,—] :
  (ℂ : Category 𝒰 𝒱)
  (X : obj ⦃ ℂ ⦄)
  → -------------------
  Functor ℂ (Set' {𝒱})
ℂ [ X ,—] = record
  { F₀ = λ Y → X ~> Y
  ; F₁ = λ g f → g ∘ f
  ; id-preserv = λ Y → subrel $ fun-ext λ x → subrel $ left-unit x
  ; ∘-preserv = λ g f → subrel $ fun-ext λ h → subrel $ sym $ assoc g f h
  }
  where instance _ = ℂ
RepresentableFunctor-cov = _[_,—]

Hom[_,—] : {ℂ : Category 𝒰 𝒱}(X : obj ⦃ ℂ ⦄) → Functor ℂ (Set' {𝒱})
Hom[_,—] {ℂ = ℂ} =  ℂ [_,—]

open import Category.Opposite

RepresentableFunctor-contrav _[—,_] :
  (ℂ : Category 𝒰 𝒱)
  (X : obj ⦃ ℂ ⦄)
  → -------------------
  Functor (ℂ ᵒᵖ) Set'
ℂ [—, X ] = record
  { F₀ = λ Y → Y ~> X
  ; F₁ = λ f g → g ∘ f
  ; id-preserv = λ Y → subrel $ fun-ext λ x → subrel $ right-unit x
  ; ∘-preserv = λ f g → subrel $ fun-ext λ h → subrel $ assoc h g f
  }
  where instance _ = ℂ
RepresentableFunctor-contrav = _[—,_]

open import Category.Product
open import Type.Sum hiding (_×_) renaming (_,_ to _Σ,_)

_[—,—] :
  (ℂ : Category 𝒰 𝒱)
  → ----------------------
  Functor (ℂ ᵒᵖ × ℂ) Set'
ℂ [—,—] = record
  { F₀ = λ { (X Σ, Y) → X ~> Y }
  ; F₁ = λ { (f Σ, f') g → f' ∘ g ∘ f }
  ; id-preserv = λ { (X Σ, X') → subrel $ fun-ext λ X~>X' → subrel (
      proof id X' ∘ X~>X' ∘ id X
        === X~>X' ∘ id X :by: ap (_∘ id X) $ left-unit X~>X'
        === X~>X'       :by: right-unit X~>X' [: _==_ ]
      qed)}
  ; ∘-preserv = λ { (g Σ, g') (f Σ, f') → subrel $ fun-ext λ h → subrel (
      proof (g' ∘ f') ∘ h ∘ (f ∘ g)
        === g' ∘ f' ∘ h ∘ f ∘ g   :by: assoc _ f g
        === g' ∘ (f' ∘ h) ∘ f ∘ g
          :by: ap (λ — → — ∘ f ∘ g) $ sym $ assoc g' f' h
        === g' ∘ (f' ∘ h ∘ f) ∘ g
          :by: ap (_∘ g) $ sym $ assoc g' (f' ∘ h) f [: _==_ ]
      qed)}
  }
  where instance _ = ℂ

open import Category.FunCategory

PresheavesCat :
  (𝒰 : Universe)
  (ℂ : Category 𝒱 𝒲)
  → ------------------------------------
  Category (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲) (𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲)
PresheavesCat 𝒰 ℂ = FunCategory (ℂ ᵒᵖ) (Set' {𝒰})

open import NaturalTransformation
open import Proof

YonedaFunctor :
  (ℂ : Category 𝒰 𝒱)
  → -----------------------------
  Functor ℂ (PresheavesCat 𝒱 ℂ)
YonedaFunctor {𝒰}{𝒱} ℂ = record
  { F₀ = λ X → ℂ [—, X ]
  ; F₁ = postcomp
  ; id-preserv = λ X → ⟹== (postcomp (id X)) (id (ℂ [—, X ])) $ 
      subrel $ fun-ext λ Y → fun-ext λ x → subrel $ left-unit x
  ; ∘-preserv = λ g f → ⟹== (postcomp (g ∘ f)) (postcomp g ∘ postcomp f) $
      subrel $ fun-ext λ X → fun-ext λ h → subrel $ sym $ assoc g f h 
  }
  where instance _ = ℂ; _ = PresheavesCat 𝒱 ℂ
        postcomp : ∀ {X Y}
          (f : X ~> Y)
          → -------------------------
          ℂ [—, X ] ⟹ ℂ [—, Y ]
        postcomp f = record
          { _at_ = λ _ → f ∘_
          ; naturality = λ g → subrel $ fun-ext λ h → subrel $ assoc f h g
          }

open import Function using (==→~; het==→~)
open import Logic
open import Functor.Property

Yoneda-full :
  (ℂ : Category 𝒰 𝒱)
  → -----------------------------
  full (YonedaFunctor ℂ)
Yoneda-full ℂ {X}{Y} h =
  f ,
  ⟹== (F₁ f) h (subrel $ fun-ext λ Z → fun-ext λ g → subrel (
    proof (h at X) (id X) ∘ g
      === (h at Z) (id X ∘ g)
        :by: sym $ subrel $ ==→~ (naturality ⦃ h ⦄ g) (id X)
      === (h at Z) g
        :by: ap (h at Z) $ left-unit g [: _==_ ]
    qed))
  where instance _ = ℂ; _ = YonedaFunctor ℂ; _ = h
        f = (h at X) (id X)

Yoneda-faithful :
  (ℂ : Category 𝒰 𝒱)
  → -----------------------------
  faithful (YonedaFunctor ℂ)
Yoneda-faithful ℂ {X}{Y} f g p =
  proof f
    === f ∘ id X :by: sym $ right-unit f
    === g ∘ id X :by: subrel $ het==→~ (==→~ (ap _at_ p) X) (id X)
    === g        :by: right-unit g
  qed
  where instance _ = ℂ

-- -- TODO: redesign universe level to be able to capture Nat[_[—,--],--]

-- open import Isomorphism.Natural

-- Nat[_[—,--],--] :
--   (ℂ : Category 𝒰 𝒱)
--   → ------------------------------
--   Functor (FunCategory (ℂ ᵒᵖ) (Set' {𝒱}) × ℂ ᵒᵖ) (Set' {𝒱})
-- Nat[ ℂ [—,--],--] = record
--   { F₀ = λ { (F , X) → {!ℂ [—, X ] ⟹ F!} }
--   ; F₁ = {!!}
--   ; id-preserv = {!!}
--   ; ∘-preserv = {!!}
--   }
--   where instance _ = ℂ

-- YonedaLemma-nat :
--   (ℂ : Category 𝒰 𝒱)
--   → ------------------------------------------
--   Nat[ ℂ [—,--],--] nat-≅ App (ℂ ᵒᵖ) (Set' {𝒱})
-- YonedaLemma-nat = {!!}

