{-# OPTIONS --exact-split --prop #-}
module Adjunction.Equivalence where

open import Universes
open import Category
open import Functor
open import NaturalTransformation renaming (Composition to _O_)
open import Adjunction.Definition

open import Axiom.FunctionExtensionality
open import Function
  using ( Bijection; forw; back; bi-inverse
        ; left-inv; right-inv; inverse-left; inverse-right)
open import Proof hiding (Id)

-|→⊣ :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F : Functor ℂ 𝔻}
  {G : Functor 𝔻 ℂ}
  (A : F -| G)
  → --------------------
  F ⊣ G
-|→⊣ {ℂ = ℂ}{𝔻}{F}{G} A = record
  { η = η₁
  ; ε = ε₁
  ; axiom-F = ⟹== (right-compose ε₁ F O left-compose F η₁) (Identity F) $
      fun-ext λ X →
        proof ε₀ (F0 X) ∘ F1 (η₀ X)
          〉 _==_ 〉 forw (id (G0 (F0 X))) ∘ F1 (η₀ X)
            :by: refl _
          〉 _==_ 〉 forw (id (G0 (F0 X)) ∘ η₀ X)
            :by: left-extend (id (G0 (F0 X))) (η₀ X)
          〉 _==_ 〉 forw (back (id (F0 X)))
            :by: ap forw $ left-unit _
          〉 _==_ 〉 id (F0 X)
            :by: right-inv _
        qed
  ; axiom-G = ⟹== (left-compose G ε₁ O right-compose η₁ G) (Identity G) $
      fun-ext λ Y →
        proof G1 (ε₀ Y) ∘ η₀ (G0 Y)
          〉 _==_ 〉 back (forw (G1 (ε₀ Y) ∘ η₀ (G0 Y)))
            :by: sym $ left-inv _
          〉 _==_ 〉 back (forw (id (G0 Y)))
            :by: ap back (
              proof forw (G1 (ε₀ Y) ∘ η₀ (G0 Y))
                〉 _==_ 〉 ε₀ Y ∘ forw (η₀ (G0 Y))
                  :by: sym $ right-extend (η₀ (G0 Y)) (ε₀ Y)
                〉 _==_ 〉 ε₀ Y ∘ id _
                  :by: ap (ε₀ Y ∘_) $ right-inv _
                〉 _==_ 〉 ε₀ Y
                  :by: right-unit _
              qed)
          〉 _==_ 〉 id (G0 Y)
            :by: left-inv _
        qed
  }
  where open _-|_ ⦃ … ⦄
        instance
          _ = ℂ; _ = 𝔻
          _ = F; _ = G
          _ = A
          bij = λ {X}{Y} → bijection ⦃ A ⦄ X Y
          _ = λ {X}{Y} → inverse-left ⦃ bi-inverse ⦃ bij {X}{Y} ⦄ ⦄
          _ = λ {X}{Y} → inverse-right ⦃ bi-inverse ⦃ bij {X}{Y} ⦄ ⦄
        F0 = F₀ ⦃ F ⦄
        F1 = F₁ ⦃ F ⦄
        G0 = F₀ ⦃ G ⦄
        G1 = F₁ ⦃ G ⦄
        η₀ : (X : obj) → X ~> G0 (F0 X)
        η₀ X = back (id (F0 X))
        η₁ : Id ℂ ⟹ G o F
        _at_ η₁ = η₀
        naturality ⦃ η₁ ⦄ {X}{Y} f =
          proof η₀ Y ∘ f
            〉 _==_ 〉 back (forw (η₀ Y ∘ f))
              :by: sym $ left-inv _
            〉 _==_ 〉 back (forw (G1 (F1 f) ∘ η₀ X))
              :by: ap back (
                proof forw (η₀ Y ∘ f)
                  〉 _==_ 〉 forw (η₀ Y) ∘ F1 f
                    :by: sym $ left-extend (η₀ Y) f
                  〉 _==_ 〉 id (F0 Y) ∘ F1 f
                    :by: ap (_∘ F1 f) $ right-inv _
                  〉 _==_ 〉 F1 f
                    :by: left-unit _
                  〉 _==_ 〉 F1 f ∘ id (F0 X)
                    :by: sym $ right-unit _
                  〉 _==_ 〉 F1 f ∘ forw (η₀ X)
                    :by: ap (F1 f ∘_) $ sym $ right-inv _
                  〉 _==_ 〉 forw (G1 (F1 f) ∘ η₀ X)
                    :by: right-extend (η₀ X) (F1 f)
                qed)
            〉 _==_ 〉 G1 (F1 f) ∘ η₀ X
              :by: left-inv _
          qed
        ε₀ : (Y : obj) → F0 (G0 Y) ~> Y
        ε₀ Y = forw (id (G0 Y))
        ε₁ : F o G ⟹ Id 𝔻
        _at_ ε₁ = ε₀
        naturality ⦃ ε₁ ⦄ {X}{Y} f =
          proof ε₀ Y ∘ F1 (G1 f)
            〉 _==_ 〉 forw (id (G0 Y)) ∘ F1 (G1 f)
              :by: refl _
            〉 _==_ 〉 forw (id (G0 Y) ∘ G1 f)
              :by: left-extend (id (G0 Y)) (G1 f)
            〉 _==_ 〉 forw (G1 f)
              :by: ap forw $ left-unit _
            〉 _==_ 〉 forw (G1 f ∘ id (G0 X))
              :by: ap forw $ sym $ right-unit _
            〉 _==_ 〉 f ∘ forw (id (G0 X))
              :by: sym $ right-extend (id (G0 X)) f
            〉 _==_ 〉 f ∘ ε₀ X
              :by: refl _
          qed

open import Isomorphism.Natural
open import Category.Opposite
open import Category.Product
open import Category.FunCategory
open import Example.Set'

open import Proposition.Sum

-- definition using natural isomorphism
-- _—|_ :
--   {ℂ : Category 𝒰 𝒱}
--   {𝔻 : Category 𝒲 𝒯}
--   (F : Functor ℂ 𝔻)
--   (G : Functor 𝔻 ℂ)
--   → ----------------------------------------
--   𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
-- _—|_ {ℂ = ℂ}{𝔻} F G = Σₚ λ (f : 𝔻 [ F —,—] ~> ℂ [—, G —]) → nat-iso f
--   where _ = FunCategory (ℂ ᵒᵖ × 𝔻) Set'
