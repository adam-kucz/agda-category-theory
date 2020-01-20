{-# OPTIONS --exact-split --prop #-}
module Adjunction.Property where

open import Adjunction.Definition

open import Universes hiding (A)
open import Type.Sum hiding (_,_)
open import Proposition.Sum
open import Function
  renaming (id to id-fun; Bijection to Bij)
  using (_∘ₛ_; _~_; inverse-left; inverse-right; left-inv; right-inv)
open import Logic
open import Proof

open import Category
open import Functor
open import NaturalTransformation
  renaming (Composition to _O_;
            right-compose to rc;
            left-compose to lc)

open import Axiom.UniqueChoice
open import Axiom.FunctionExtensionality

char-left-adjoint :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  ⦃ 𝔻 : Category 𝒲 𝒯 ⦄
  {G : Functor 𝔻 ℂ}
  (p : ∀ (X : obj) →
       Σ λ (FX : obj) →
       Σₚ λ (ηX : X ~> F₀ ⦃ G ⦄ FX) →
       ∀ (Y : obj)(f : X ~> F₀ ⦃ G ⦄ Y) →
       ∃! λ (f-bar : FX ~> Y) →
       F₁ ⦃ G ⦄ f-bar ∘ ηX == f)
  → ---------------------
  ∃ λ (F : Functor ℂ 𝔻) →
  ∃ λ (A : F ⊣ G) →
    ⊤
char-left-adjoint ⦃ ℂ ⦄ ⦃ 𝔻 ⦄ {G} p = F , (-|→⊣ A , ⋆ₚ)
  where instance _ = G
        F' : (X : obj) → obj
        F' X = pr₁ (p X)
        η' : (X : obj) → X ~> F₀ (F' X)
        η' X = elem (pr₂ (p X))
        bar : {X : obj}{Y : obj}
          (f : X ~> F₀ Y)
          → -------------------------
          Σₚ λ (f-bar : F' X ~> Y) →
          F₁ f-bar ∘ η' X == f ∧
          ∀ (f-bar' : F' X ~> Y)
            (p : F₁ f-bar' ∘ η' X == f) →
            f-bar' == f-bar
        bar {X}{Y} f = !choice (prop (pr₂ (p X)) Y f)
        forw :
          {X : obj ⦃ ℂ ⦄}
          {Y : obj ⦃ 𝔻 ⦄}
          (f : X ~> F₀ Y)
          → F' X ~> Y
        forw f = elem (bar f)
        back : 
          {X : obj ⦃ ℂ ⦄}
          {Y : obj ⦃ 𝔻 ⦄}
          (f : F' X ~> Y)
          → X ~> F₀ Y
        back {X}{Y} f = F₁ f ∘ η' X
        back∘forw~id :
          {X : obj ⦃ ℂ ⦄}
          {Y : obj ⦃ 𝔻 ⦄}
          → back {X}{Y} ∘ₛ forw {X}{Y} ~ id-fun
        back∘forw~id f = ∧left (prop (bar f))
        forw∘back~id :
          {X : obj ⦃ ℂ ⦄}
          {Y : obj ⦃ 𝔻 ⦄}
          → forw {X}{Y} ∘ₛ back {X}{Y} ~ id-fun
        forw∘back~id {X}{Y} f =
          sym $ ∧right (prop (bar (F₁ f ∘ η' X))) f (refl _)
        F : Functor ℂ 𝔻
        F₀ ⦃ F ⦄ = F'
        F₁ ⦃ F ⦄ {X}{Y} f = forw (η' Y ∘ f)
        id-preserv ⦃ F ⦄ X =
          proof forw (η' X ∘ id X)
            === id (F' X)
              :by: sym $
                ∧right (prop (bar (η' X ∘ id X)))
                       (id (F' X)) (
                proof F₁ (id (F' X)) ∘ η' X
                  === id (F₀ (F' X)) ∘ η' X
                    :by: ap (_∘ η' X) $ id-preserv (F' X)
                  === η' X ∘ id X
                    :by: bi-unit (η' X)
                qed)
          qed
        ∘-preserv ⦃ F ⦄ {X}{Y}{Z} g f =
          proof forw (η' Z ∘ (g ∘ f))
            === forw (η' Z ∘ g) ∘ forw (η' Y ∘ f)
            :by: sym $
              ∧right (prop (bar (η' Z ∘ (g ∘ f))))
                     (forw (η' Z ∘ g) ∘ forw (η' Y ∘ f)) (
              proof back (forw (η' Z ∘ g) ∘ forw (η' Y ∘ f))
                === F₁ (forw (η' Z ∘ g)) ∘
                    F₁ (forw (η' Y ∘ f)) ∘
                    η' X
                  :by: ap (_∘ η' X) $
                       ∘-preserv (forw (η' Z ∘ g)) (forw (η' Y ∘ f))
                === F₁ (forw (η' Z ∘ g)) ∘
                    back (forw (η' Y ∘ f))
                  :by: sym $ assoc _ _ _
                === F₁ (forw (η' Z ∘ g)) ∘ (η' Y ∘ f)
                  :by: ap (F₁ (forw (η' Z ∘ g)) ∘_) $
                       back∘forw~id (η' Y ∘ f)
                === back (forw (η' Z ∘ g)) ∘ f
                  :by: assoc _ _ f
                === η' Z ∘ g ∘ f
                  :by: ap (_∘ f) $ back∘forw~id (η' Z ∘ g)
                === η' Z ∘ (g ∘ f)
                  :by: sym $ assoc _ g f
              qed)
          qed
        forw-id-comp : ∀ {X Y : obj ⦃ 𝔻 ⦄}
          (f : X ~> Y)
          → -----------------------------
          forw (id (F₀ Y)) ∘
          forw (η' (F₀ Y) ∘ F₁ f)
          ==
          forw (id (F₀ Y) ∘ F₁ f)
        forw-id-comp {X}{Y} f = ∧right
          (prop (bar (id (F₀ Y) ∘ F₁ f)))
          (forw (id (F₀ Y)) ∘ forw (η' (F₀ Y) ∘ F₁ f)) $
          (proof back (forw (id (F₀ Y)) ∘ forw (η' (F₀ Y) ∘ F₁ f))
             === F₁ (forw (id (F₀ Y))) ∘
                 F₁ (forw (η' (F₀ Y) ∘ F₁ f)) ∘
                 η' (F₀ X)
               :by: ap (_∘ η' (F₀ X)) $
                 ∘-preserv (forw (id (F₀ Y)))
                 (elem (bar (η' (F₀ Y) ∘ F₁ f)))
             === F₁ (forw (id (F₀ Y))) ∘
                 back (forw (η' (F₀ Y) ∘ F₁ f))
               :by: sym $ assoc _ _ _
             === F₁ (forw (id (F₀ Y))) ∘
                 (η' (F₀ Y) ∘ F₁ f)
               :by: ap (F₁ (forw (id (F₀ Y))) ∘_) $
                    back∘forw~id (η' (F₀ Y) ∘ F₁ f)
             === back (forw (id (F₀ Y))) ∘ F₁ f
               :by: assoc _ _ _
             === id (F₀ Y) ∘ F₁ f
               :by: ap (_∘ F₁ f) $ back∘forw~id (id (F₀ Y))
           qed)
        open import Adjunction.Equivalence
        A : F -| G
        Bij.forw (_-|_.bijection A X Y) = forw
        Bij.back (_-|_.bijection A X Y) = back
        left-inv ⦃
          inverse-left ⦃ Bij.bi-inverse (_-|_.bijection A X Y) ⦄ ⦄ =
          back∘forw~id
        right-inv ⦃
          inverse-right ⦃ Bij.bi-inverse (_-|_.bijection A X Y) ⦄ ⦄ =
          forw∘back~id
        _-|_.right-extend A {X}{Y}{Z} f g =
          proof g ∘ forw f
            === forw (back (g ∘ forw f))
              :by: sym $ forw∘back~id _
            === forw (back (forw (F₁ g ∘ f)))
              :by: ap forw (
                proof back (g ∘ forw f)
                  === F₁ g ∘ F₁ (forw f) ∘ η' X
                    :by: ap (_∘ η' _) $ ∘-preserv ⦃ G ⦄ g (forw f) 
                  === F₁ g ∘ back (forw f)
                    :by: sym $ assoc _ _ _
                  === F₁ g ∘ f
                    :by: ap (F₁ g ∘_) $ back∘forw~id f
                  === back (forw (F₁ g ∘ f))
                    :by: sym $ back∘forw~id _
                qed)
            === forw (F₁ g ∘ f)
              :by: forw∘back~id _
          qed
        _-|_.left-extend A {X'}{X}{Y} f g =
          proof forw f ∘ forw (η' X ∘ g)
            === forw (back (forw f ∘ forw (η' X ∘ g)))
              :by: sym $ forw∘back~id _
            === forw (back (forw (f ∘ g)))
              :by: ap forw (
                proof back (forw f ∘ forw (η' X ∘ g))
                  === F₁ (forw f) ∘ F₁ (forw (η' X ∘ g)) ∘ η' X'
                    :by: ap (_∘ η' X') $ ∘-preserv ⦃ G ⦄ (forw f) (forw (η' X ∘ g))
                  === F₁ (forw f) ∘ back (forw (η' X ∘ g))
                    :by: sym $ assoc _ _ _
                  === F₁ (forw f) ∘ (η' X ∘ g)
                    :by: ap (F₁ (forw f) ∘_) $ back∘forw~id (η' X ∘ g)
                  === back (forw f) ∘ g
                    :by: assoc _ _ g
                  === f ∘ g
                    :by: ap (_∘ g) $ back∘forw~id f
                  === back (forw (f ∘ g))
                    :by: sym $ back∘forw~id (f ∘ g)
                qed)
            === forw (f ∘ g)
              :by: forw∘back~id (forw (f ∘ g))
          qed
