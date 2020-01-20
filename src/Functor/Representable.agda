{-# OPTIONS --exact-split --prop #-}
module Functor.Representable where

open import Universes
open import Category
open import Functor.Definition
open import Example.Set'

open import Axiom.FunctionExtensionality

open import Relation.Binary.Property using (sym)
import Proposition.Identity

infix 245 _[_,—] _[—,_]
RepresentableFunctor-cov _[_,—] :
  (ℂ : Category 𝒰 𝒱)
  (X : obj ⦃ ℂ ⦄)
  → -------------------
  Functor ℂ (Set' {𝒱})
ℂ [ X ,—] = record
  { F₀ = λ Y → X ~> Y
  ; F₁ = λ g f → g ∘ f
  ; id-preserv = λ Y → fun-ext left-unit
  ; ∘-preserv = λ g f → fun-ext λ h → sym (assoc g f h)
  }
  where instance _ = ℂ
RepresentableFunctor = _[_,—]

open import Category.Opposite

RepresentableFunctor-contrav _[—,_] :
  (ℂ : Category 𝒰 𝒱)
  (X : obj ⦃ ℂ ⦄)
  → -------------------
  Functor (ℂ ᵒᵖ) Set'
ℂ [—, X ] = record
  { F₀ = λ Y → Y ~> X
  ; F₁ = λ f g → g ∘ f
  ; id-preserv = λ Y → fun-ext right-unit
  ; ∘-preserv = λ f g → fun-ext λ h → assoc h g f
  }
  where instance _ = ℂ
RepresentableFunctor-contrav = _[—,_]

open import Category.Product
open import Type.Sum hiding (_×_; _,_)
open import Proof

_[—,—] :
  (ℂ : Category 𝒰 𝒱)
  → ----------------------
  Functor (ℂ ᵒᵖ × ℂ) Set'
ℂ [—,—] = record
  { F₀ = λ { (X Σ., Y) → X ~> Y }
  ; F₁ = λ { (f Σ., f') g → f' ∘ g ∘ f }
  ; id-preserv = λ { (X Σ., X') → fun-ext λ X~>X' →
      proof id X' ∘ X~>X' ∘ id X
        〉 _==_ 〉 X~>X' ∘ id X :by: ap (_∘ id X) $ left-unit X~>X'
        〉 _==_ 〉 X~>X'       :by: right-unit X~>X'
      qed }
  ; ∘-preserv = λ { (g Σ., g') (f Σ., f') → fun-ext λ h →
      proof (g' ∘ f') ∘ h ∘ (f ∘ g)
        〉 _==_ 〉 g' ∘ f' ∘ h ∘ f ∘ g   :by: assoc _ f g
        〉 _==_ 〉 g' ∘ (f' ∘ h) ∘ f ∘ g
          :by: ap (λ — → — ∘ f ∘ g) $ sym $ assoc g' f' h
        〉 _==_ 〉 g' ∘ (f' ∘ h ∘ f) ∘ g
          :by: ap (_∘ g) $ sym $ assoc g' (f' ∘ h) f
      qed }
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

YonedaEmbedding YonedaFunctor :
  (ℂ : Category 𝒰 𝒱)
  → -----------------------------
  Functor ℂ (PresheavesCat 𝒱 ℂ)
YonedaEmbedding {𝒰}{𝒱} ℂ = record
  { F₀ = λ X → ℂ [—, X ]
  ; F₁ = postcomp
  ; id-preserv = λ X → ⟹== (postcomp (id X)) (id (ℂ [—, X ])) $ 
      fun-ext λ Y → fun-ext left-unit
  ; ∘-preserv = λ g f → ⟹== (postcomp (g ∘ f)) (postcomp g ∘ postcomp f) $
      fun-ext λ X → fun-ext λ h → sym $ assoc g f h 
  }
  where instance _ = ℂ; _ = PresheavesCat 𝒱 ℂ
        postcomp : ∀ {X Y}
          (f : X ~> Y)
          → -------------------------
          ℂ [—, X ] ⟹ ℂ [—, Y ]
        postcomp f = record
          { _at_ = λ _ → f ∘_
          ; naturality = λ g → fun-ext λ h → assoc f h g
          }
YonedaFunctor = YonedaEmbedding

open import Function using (==→~)
open import Logic
open import Functor.Property

Yoneda-full :
  (ℂ : Category 𝒰 𝒱)
  → -----------------------------
  full (YonedaFunctor ℂ)
Yoneda-full ℂ {X}{Y} h =
  f ,
  ⟹== (F₁ f) h (fun-ext λ Z → fun-ext λ g →
    proof (h at X) (id X) ∘ g
      === (h at Z) (id X ∘ g)
        :by: sym $ ==→~ (naturality ⦃ h ⦄ g) (id X)
      === (h at Z) g
        :by: ap (h at Z) $ left-unit g
    qed)
  where instance _ = ℂ; _ = YonedaFunctor ℂ; _ = h
        f = (h at X) (id X)

Yoneda-faithful :
  (ℂ : Category 𝒰 𝒱)
  → -----------------------------
  faithful (YonedaFunctor ℂ)
Yoneda-faithful ℂ {X}{Y} f g p =
  proof f
    === f ∘ id X :by: sym $ right-unit f
    === g ∘ id X :by: ==→~ (==→~ (ap _at_ p) X) (id X)
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

