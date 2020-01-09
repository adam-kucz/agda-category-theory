{-# OPTIONS --exact-split --safe --prop #-}
module NaturalTransformation.Construction where

open import NaturalTransformation.Definition

open import Universes
open import Category
open import Functor

open import Proof

Identity :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  ⦃ 𝔻 : Category 𝒲 𝒯 ⦄
  (F : Functor ℂ 𝔻)
  → -------------------------
  F ⟹ F
Identity F at X = id (F₀ X)
  where instance _ = F
naturality ⦃ Identity F ⦄ {X} {Y} f =
  proof id (F₀ Y) ∘ F₁ f
    〉 _==_ 〉 F₁ f             :by: left-unit (F₁ f)
    〉 _==_ 〉 F₁ f ∘ id (F₀ X) :by: sym $ right-unit (F₁ f)
  qed
  where instance _ = F

infixl 210 Composition
Composition :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F G H : Functor ℂ 𝔻}
  (ψ : G ⟹ H)
  (ϕ : F ⟹ G)
  → -----------------------------
  F ⟹ H
Composition {𝔻 = 𝔻} ψ ϕ at X = ψ at X ∘ ϕ at X
  where instance _ = 𝔻
naturality ⦃ Composition {ℂ = ℂ} {𝔻} {F} {G} {H} ψ ϕ ⦄ {X} {Y} f =
  proof ψ at Y ∘ ϕ at Y ∘ F₁ f
    〉 _==_ 〉 ψ at Y ∘ (ϕ at Y ∘ F₁ f) :by: sym $ assoc _ _ _
    〉 _==_ 〉 ψ at Y ∘ (F₁ f ∘ ϕ at X) :by: ap (ψ at Y ∘_) $ naturality ⦃ ϕ ⦄ f
    〉 _==_ 〉 ψ at Y ∘ F₁ f ∘ ϕ at X   :by: assoc _ _ _
    〉 _==_ 〉 F₁ f ∘ ψ at X ∘ ϕ at X   :by: ap (_∘ ϕ at X) $ naturality ⦃ ψ ⦄ f
    〉 _==_ 〉 F₁ f ∘ (ψ at X ∘ ϕ at X) :by: sym $ assoc _ _ _
  qed
  where instance _ = ℂ; _ = 𝔻; _ = F; _ = G; _ = H

HorizontalComposition :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {𝔼 : Category 𝒵 𝒳}
  {G G' : Functor 𝔻 𝔼}
  {F F' : Functor ℂ 𝔻}
  (ϕ : G ⟹ G')
  (ψ : F ⟹ F')
  → -----------------------------
  G o F ⟹ G' o F'
HorizontalComposition {𝔼 = 𝔼}{_}{G'}{F} ϕ ψ at X =
  F₁ (ψ at X) ∘ ϕ at F₀ X
  where instance _ = F; _ = G'; _ = 𝔼
naturality ⦃ HorizontalComposition {ℂ = ℂ}{𝔻}{𝔼}{G}{G'}{F}{F'} ϕ ψ ⦄ {X}{Y} f = 
  proof G'1 (ψ at Y) ∘ ϕ at F0 Y ∘ G1 (F1 f)
    〉 _==_ 〉 G'1 (ψ at Y) ∘ (ϕ at F0 Y ∘ G1 (F1 f))
      :by: sym $ assoc _ _ _
    〉 _==_ 〉 G'1 (ψ at Y) ∘ (G'1 (F1 f) ∘ ϕ at F0 X)
      :by: ap (G'1 (ψ at Y) ∘_) $ naturality ⦃ ϕ ⦄ (F1 f)
    〉 _==_ 〉 G'1 (ψ at Y) ∘ G'1 (F1 f) ∘ ϕ at F0 X
      :by: assoc _ _ _
    〉 _==_ 〉 G'1 (F'1 f) ∘ G'1 (ψ at X) ∘ ϕ at F0 X
      :by: ap (_∘ ϕ at F0 X) (
             proof G'1 (ψ at Y) ∘ G'1 (F1 f)
               〉 _==_ 〉 G'1 (ψ at Y ∘ F1 f)        :by: sym $ ∘-preserv _ _
               〉 _==_ 〉 G'1 (F'1 f ∘ ψ at X)       :by: ap G'1 $ naturality ⦃ ψ ⦄ f
               〉 _==_ 〉 G'1 (F'1 f) ∘ G'1 (ψ at X) :by: ∘-preserv _ _
             qed)
    〉 _==_ 〉 G'1 (F'1 f) ∘ (G'1 (ψ at X) ∘ ϕ at F0 X)
      :by: sym $ assoc _ _ _
  qed
  where instance _ = ℂ; _ = 𝔻; _ = 𝔼; _ = F; _ = F'; _ = G; _ = G'
        F0  = F₀ ⦃ F ⦄
        F1  = F₁ ⦃ F ⦄
        F'0 = F₀ ⦃ F' ⦄
        F'1 = F₁ ⦃ F' ⦄
        G0  = F₀ ⦃ G ⦄
        G1  = F₁ ⦃ G ⦄
        G'0 = F₀ ⦃ G' ⦄
        G'1 = F₁ ⦃ G' ⦄

HorizontalComposition==alternative :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {𝔼 : Category 𝒵 𝒳}
  {G G' : Functor 𝔻 𝔼}
  {F F' : Functor ℂ 𝔻}
  (ϕ : G ⟹ G')
  (ψ : F ⟹ F')
  (X : obj ⦃ ℂ ⦄)
  → -------------------------------------------------------
  let instance _ = 𝔼 in
  F₁ ⦃ G' ⦄ (ψ at X) ∘ ϕ at F₀ ⦃ F ⦄ X == ϕ at F₀ ⦃ F' ⦄ X ∘ F₁ ⦃ G ⦄ (ψ at X)
HorizontalComposition==alternative {𝔼 = 𝔼}{G}{G'}{F}{F'} ϕ ψ X =
  sym $ naturality ⦃ ϕ ⦄ (ψ at X)
  where instance _ = 𝔼
        F0 = F₀ ⦃ F ⦄
        F'0 = F₀ ⦃ F' ⦄
        G1 = F₁ ⦃ G ⦄
        G'1 = F₁ ⦃ G' ⦄


open import Proof

left-compose :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {𝔼 : Category 𝒮 𝒵}
  (F : Functor 𝔻 𝔼)
  {G H : Functor ℂ 𝔻}
  (θ : G ⟹ H )
  → -----------------------------------------
  F o G ⟹ F o H
left-compose F θ at X = F₁ (θ at X)
  where instance _ = F
naturality ⦃ left-compose {𝔻 = 𝔻}{𝔼} F {G}{H} θ ⦄ {X}{Y} f =
  proof F₁ (θ at Y) ∘ F₁ (F₁ f)
    〉 _==_ 〉 F₁ (θ at Y ∘ F₁ f)      :by: sym $ ∘-preserv (θ at Y) (F₁ f)
    〉 _==_ 〉 F₁ (F₁ f ∘ θ at X)      :by: ap F₁ $ naturality f
    〉 _==_ 〉 F₁ (F₁ f) ∘ F₁ (θ at X) :by: ∘-preserv (F₁ f) (θ at X) 
  qed
  where instance _ = 𝔻; _ = 𝔼; _ = F; _ = G; _ = H; _ = θ

right-compose :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {𝔼 : Category 𝒮 𝒵}
  {G H : Functor 𝔻 𝔼}
  (θ : G ⟹ H)
  (F : Functor ℂ 𝔻)
  → -----------------------------------------
  G o F ⟹ H o F
right-compose θ F at X = θ at F₀ X
  where instance _ = F
naturality ⦃ right-compose θ F ⦄ f = naturality (F₁ f)
  where instance _ = F; _ = θ
