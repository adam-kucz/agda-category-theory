{-# OPTIONS --exact-split --prop #-}
module Category.Cat.Exponential where

open import Category.Cat.Definition
open import Category.Cat.Product

open import Universes
open import Type.Sum hiding (_×_) renaming (_,_ to _Σ,_)
open import Logic
open import Proof

open import Category
open import Functor
open import NaturalTransformation
open import Category.FunCategory
open import Category.Product hiding (_×_)
open import Construction.Product as P hiding (〈_,_〉)
open import Construction.Exponential

open import Function.Extensionality
open import Functor.Extensionality

private
  instance _ = CatCategory

!Cur-F :
  (A B Z : Category 𝒰 𝒰)
  (F : Functor (Z × A) B)
  (Cur-F' : Functor Z (FunCategory A B))
  (p : App A B o (Cur-F' ⊠ Id A) == F)
  → --------------------------------------
  Cur-F' == Cur F
!Cur-F A B Z F Cur-F' p = funct-ext Cur-F' Cur-F ∀X→Cur-F'X==Cur-FX
  λ {X}{Y} f → ⟹het== (F₁ ⦃ Cur-F' ⦄ f)(F₁ ⦃ Cur-F ⦄ f)
    (refl A)(refl B)
    (subrel $ ∀X→Cur-F'X==Cur-FX X)
    (subrel $ ∀X→Cur-F'X==Cur-FX Y) $
    fun-ext λ x →
    proof F₁ ⦃ Cur-F' ⦄ f at x
      het== F₁ ⦃ App A B o (Cur-F' ⊠ Id A) ⦄ (f Σ, id ⦃ A ⦄ x)
        :by: {!App A B!}
      het== F₁ (f Σ, id ⦃ A ⦄ x)
        :by: ? -- ap (λ — → F₁ ⦃ — ⦄ (f Σ, id ⦃ A ⦄ x)) ⦃ Relating-all-==-het== ⦄ p
      het== F₁ ⦃ Cur-F ⦄ f at x  :by: Het.refl _
    qed
  where instance _ = F
        Cur-F = Cur F
        ∀X→Cur-F'X==Cur-FX : (X : obj ⦃ Z ⦄)
          → ----------------------------------------
          F₀ ⦃ Cur-F' ⦄ X == F₀ ⦃ Cur-F ⦄ X
        ∀X→Cur-F'X==Cur-FX z =
          funct-ext (F₀ ⦃ Cur-F' ⦄ z)(F₀ ⦃ Cur-F ⦄ z)
          (λ a → let x = z Σ, a in
            proof F₀ ⦃ F₀ ⦃ Cur-F' ⦄ z ⦄ a
              === F₀ ⦃ App A B ⦄ (F₀ ⦃ Cur-F' ⦄ z Σ, a) :by: Id.refl _
              === F₀ ⦃ App A B o (Cur-F' ⊠ id A) ⦄ x
                :by: ap (F₀ ⦃ App A B ⦄) $ sym $
                     ∧left (Cat-prod-prop (Cur-F' ∘ pi₁ Z A)(pi₂ Z A)) x
              === F₀ (z Σ, a) :by: ap (λ — → F₀ ⦃ — ⦄ x) p
            qed)
          λ f → {!!}

CatExponentials : HasExponentials (CatCategory {𝒰}{𝒰})
Exponential.exp (CatExponentials {A = A} {B}) = FunCategory A B
Exponential.app (CatExponentials {A = A} {B}) = App A B
IsExponential.curry (Exponential.exp-def (CatExponentials {A = A} {B})) Z F =
  Cur-F , (
  funct-ext (App A B o Cur⊠Id) F
    (λ {x@(z Σ, a) →
    proof F₀ ⦃ App A B o Cur⊠Id ⦄ x
      === F₀ ⦃ App A B ⦄ (F₀ ⦃ Cur-F ⦄ z Σ, a)
        :by: ap (F₀ ⦃ App A B ⦄) $
             ∧left (Cat-prod-prop (Cur-F ∘ pi₁ Z A)(pi₂ Z A)) x
      === F₀ x :by: Id.refl _
    qed})
    (λ { {x@(xz Σ, xa)}{y@(yz Σ, ya)} f@(fz Σ, fa) →
    proof F₁ ⦃ App A B o Cur⊠Id ⦄ f
      het== F₁ ⦃ App A B ⦄ (F₁ ⦃ Cur-F ⦄ fz Σ, fa)
        :by: Het.ap3
             (λ X Y (f : mor (FunCategory A B × A) X Y) → F₁ ⦃ App A B ⦄ f)
             (∧left (Cat-prod-prop (Cur-F ∘ pi₁ Z A)(pi₂ Z A)) x)
             (subrel $ ∧left (Cat-prod-prop (Cur-F ∘ pi₁ Z A)(pi₂ Z A)) y)
             (∧right (Cat-prod-prop (Cur-F ∘ pi₁ Z A)(pi₂ Z A)) f)
      === (F₁ ⦃ Cur-F ⦄ fz at ya) ∘[ B ] F₁ ⦃ F₀ ⦃ Cur-F ⦄ xz ⦄ fa
        :by: Id.refl _
      === F₁ (fz Σ, id ⦃ A ⦄ ya) ∘[ B ] F₁ (id ⦃ Z ⦄ xz Σ, fa)
        :by: Id.refl _
      === F₁ (fz ∘[ Z ] id ⦃ Z ⦄ xz Σ, id ⦃ A ⦄ ya ∘[ A ] fa)
        :by: sym $ ∘-preserv (fz Σ, id ⦃ A ⦄ ya)(id ⦃ Z ⦄ xz Σ, fa) 
      === F₁ (fz Σ, fa)
        :by: ap2 (λ a b → F₁ (a Σ, b)) (right-unit ⦃ Z ⦄ fz)
                                       (left-unit ⦃ A ⦄ fa)
    qed}) , (!Cur-F A B Z F))
  where instance _ = F
        Cur-F : Functor Z (FunCategory A B)
        Cur-F = Cur F
        Cur⊠Id = Cur-F ⊠ id A
