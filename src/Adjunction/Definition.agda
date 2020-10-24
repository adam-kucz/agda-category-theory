{-# OPTIONS --exact-split --safe --prop #-}
module Adjunction.Definition where

open import Category
open import Functor
open import NaturalTransformation renaming (Composition to _O_)

open import Universes
open import Proposition.Identity hiding (refl)

infix 230 _⊣_
record _⊣_
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F : Functor ℂ 𝔻)
  (G : Functor 𝔻 ℂ)
  : ----------------------------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  where
  private
    instance _ = ℂ; _ = 𝔻
  field
    η : Id ℂ ⟹ G o F
    ε : F o G ⟹ Id 𝔻
    axiom-F : right-compose ε F O left-compose F η == Identity F
    axiom-G : left-compose G ε O right-compose η G == Identity G

open _⊣_ ⦃ … ⦄ public

{-# DISPLAY _⊣_.η A = η #-}
{-# DISPLAY _⊣_.ε A = ε #-}

Adjunction== :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F : Functor ℂ 𝔻}
  {G : Functor 𝔻 ℂ}
  (A B : F ⊣ G)
  (p : η ⦃ A ⦄ == η ⦃ B ⦄)
  (q : ε ⦃ A ⦄ == ε ⦃ B ⦄)
  → -----------------------------
  A == B
Adjunction== A A (Idₚ.refl _) (Idₚ.refl _) = Idₚ.refl A

open import Function hiding (id; _∘_; _$_)
open import Proof

-- alternative definition
infix 230 _-|_
record _-|_
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F : Functor ℂ 𝔻)
  (G : Functor 𝔻 ℂ)
  : ----------------------------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  where
  private
    instance _ = ℂ; _ = 𝔻
    F0 = F₀ ⦃ F ⦄
    F1 = F₁ ⦃ F ⦄
    G0 = F₀ ⦃ G ⦄
    G1 = F₁ ⦃ G ⦄
  field
    bijection : ∀ X Y → Bijection (X ~> G0 Y) (F0 X ~> Y)
    right-extend : ∀ {X Y Y'}
      (f : X ~> G0 Y)
      (g : Y ~> Y')
      → let ℂ→𝔻  = forw ⦃ bijection X Y ⦄
            ℂ→𝔻' = forw ⦃ bijection X Y' ⦄
      in
      g ∘ ℂ→𝔻 f == ℂ→𝔻' (G1 g ∘ f)
    left-extend : ∀ {X' X Y}
      (f : X ~> G0 Y)
      (g : X' ~> X)
      → let ℂ→𝔻  = forw ⦃ bijection X Y ⦄
            ℂ→𝔻' = forw ⦃ bijection X' Y ⦄
      in
      ℂ→𝔻 f ∘ F1 g == ℂ→𝔻' (f ∘ g)

  private
    instance
      bij  = λ {X}{Y} → bijection X Y
      _ = λ {X}{Y} → inverse-left ⦃ bi-inverse ⦃ bij {X}{Y} ⦄ ⦄
      _ = λ {X}{Y} → inverse-right ⦃ bi-inverse ⦃ bij {X}{Y} ⦄ ⦄

  right-extend-back : ∀ {X Y Y'}
      (f : F0 X ~> Y)
      (g : Y ~> Y')
      → let 𝔻→ℂ  = back ⦃ bijection X Y ⦄
            𝔻'→ℂ = back ⦃ bijection X Y' ⦄
      in
      G1 g ∘ 𝔻→ℂ f == 𝔻'→ℂ (g ∘ f)
  right-extend-back f g =
    proof G1 g ∘ back f
      === back (forw (G1 g ∘ back f))
        :by: sym $ subrel $ left-inv (G1 g ∘ back f)
      === back (forw (back (g ∘ f)))
        :by: ap back (
          proof forw (G1 g ∘ back f)
            === g ∘ forw (back f)
              :by: sym $ right-extend (back f) g
            === g ∘ f
              :by: ap (g ∘_) $ subrel $ right-inv f
            === forw (back (g ∘ f))
              :by: sym $ subrel $ right-inv (g ∘ f) [: _==_ ]
          qed)
      === back (g ∘ f)
        :by: subrel $ left-inv (back (g ∘ f))
    qed

  left-extend-back : ∀ {X X' Y}
      (f : F0 X ~> Y)
      (g : X' ~> X)
      → let 𝔻→ℂ  = back ⦃ bijection X Y ⦄
            𝔻'→ℂ = back ⦃ bijection X' Y ⦄
      in
      𝔻→ℂ f ∘ g == 𝔻'→ℂ (f ∘ F1 g)
  left-extend-back f g =
    proof back f ∘ g
      === back (forw (back f ∘ g))
        :by: sym $ subrel $ left-inv (back f ∘ g)
      === back (forw (back (f ∘ F1 g)))
        :by: ap back (
        proof forw (back f ∘ g)
            === forw (back f) ∘ F1 g
              :by: sym $ left-extend (back f) g
            === f ∘ F1 g
              :by: ap (_∘ F1 g) $ subrel $ right-inv f
            === forw (back (f ∘ F1 g))
              :by: sym $ subrel $ right-inv (f ∘ F1 g) [: _==_ ]
          qed)
      === back (f ∘ F1 g)
        :by: subrel $ left-inv (back (f ∘ F1 g))
    qed

⊣→-| :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F : Functor ℂ 𝔻}
  {G : Functor 𝔻 ℂ}
  (A : F ⊣ G)
  → --------------------
  F -| G
forw ⦃ _-|_.bijection (⊣→-| {ℂ = ℂ}{𝔻}{F}{G} A) X Y ⦄ X~>GY =
  ε at Y ∘ F₁ ⦃ F ⦄ X~>GY
  where instance _ = 𝔻; _ = A
back ⦃ _-|_.bijection (⊣→-| {ℂ = ℂ}{𝔻}{F}{G} A) X Y ⦄ FX~>Y =
  F₁ ⦃ G ⦄ FX~>Y ∘ η at X
  where instance _ = ℂ; _ = A
bi-inverse ⦃ _-|_.bijection (⊣→-| {ℂ = ℂ}{𝔻}{F}{G} A) X Y ⦄ =
  let
  instance
    _ = ℂ; _ = 𝔻; _ = F; _ = G; _ = A
    F0 = F₀ ⦃ F ⦄
    F1 = F₁ ⦃ F ⦄
    G0 = F₀ ⦃ G ⦄
    G1 = F₁ ⦃ G ⦄
    _ = _-|_.bijection (⊣→-| A) X Y
    left-inverse : LeftInverse forw back
    left-inverse = record { left-inv = λ f → subrel (
      proof G1 (ε at Y ∘ F1 f) ∘ η at X
        === G1 (ε at Y) ∘ G1 (F1 f) ∘ η at X
          :by: ap (_∘ η at X) $ ∘-preserv ⦃ G ⦄ (ε at Y) (F1 f)
        === G1 (ε at Y) ∘ (G1 (F1 f) ∘ η at X)
          :by: sym $ assoc _ _ _
        === G1 (ε at Y) ∘ (η at G0 Y ∘ f)
          :by: ap (G1 (ε at Y) ∘_) $ sym $ naturality ⦃ η ⦄ f
        === G1 (ε at Y) ∘ η at G0 Y ∘ f
          :by: assoc (G1 (ε at Y)) (η at G0 Y) f
        === (G1 (ε at Y) ∘ id (G0 (F0 (G0 Y)))) ∘
            (G1 (F1 (id (G0 Y))) ∘ η at G0 Y) ∘
            f
          :by: ap2 (λ f₀ f₁ → f₀ ∘ f₁ ∘ f)
                   (sym $ right-unit (G1 (ε at Y)))
                   (proof η at G0 Y
                      === id (G0 (F0 (G0 Y))) ∘ η at G0 Y
                        :by: sym $ left-unit (η at G0 Y)
                      === G1 (F1 (id (G0 Y))) ∘ η at G0 Y
                        :by: ap (_∘ η at G0 Y) $
                             sym $ id-preserv ⦃ G o F ⦄ (G0 Y)
                             [: _==_ ]
                    qed)
        === left-compose G ε O right-compose η G at Y ∘ f
          :by: Id.refl _
        === Identity G at Y ∘ f
          :by: ap (λ — → — at Y ∘ f) $ axiom-G
        === f :by: left-unit f [: _==_ ]
      qed)}
    right-inverse : RightInverse forw back
    right-inverse = record { right-inv = λ f → subrel (
      proof ε at Y ∘ F1 (G1 f ∘ η at X)
        === ε at Y ∘ (F1 (G1 f) ∘ F1 (η at X))
          :by: ap (ε at Y ∘_) $ ∘-preserv ⦃ F ⦄ (G1 f) (η at X)
        === ε at Y ∘ F1 (G1 f) ∘ F1 (η at X)
          :by: assoc _ _ _
        === f ∘ ε at F0 X ∘ F1 (η at X)
          :by: ap (_∘ F1 (η at X)) $ naturality ⦃ ε ⦄ f
        === f ∘ (ε at F0 X ∘ F1 (η at X))
          :by: sym $ assoc f _ _
        === f ∘ ((id (F0 X) ∘ ε at F0 X) ∘ (F1 (η at X) ∘ id (F0 X)))
          :by: ap (f ∘_) $ sym $
               ap2 _∘_ (left-unit (ε at F0 X))
                       (right-unit (F1 (η at X)))
        === f ∘ right-compose ε F O left-compose F η at X
          :by: Id.refl _
        === f ∘ Identity F at X
          :by: ap (λ — → f ∘ — at X) $ axiom-F
        === f :by: right-unit f [: _==_ ]
      qed)}
  in record {}
_-|_.right-extend (⊣→-| {ℂ = ℂ}{𝔻}{F}{G} A) {X}{Y}{Y'} X~>GY Y~>Y' =
  proof Y~>Y' ∘ (ε at Y ∘ F1 X~>GY)
    === Y~>Y' ∘ ε at Y ∘ F1 X~>GY
      :by: assoc _ _ _
    === ε at Y' ∘ F1 (G1 Y~>Y') ∘ F1 X~>GY
      :by: ap (_∘  F1 X~>GY) $ sym $ naturality ⦃ ε ⦄ Y~>Y'
    === ε at Y' ∘ (F1 (G1 Y~>Y') ∘ F1 X~>GY)
      :by: sym $ assoc _ _ _
    === ε at Y' ∘ F1 (G1 Y~>Y' ∘ X~>GY)
      :by: ap (ε at Y' ∘_) $ sym $ ∘-preserv _ _
  qed
  where instance _ = ℂ; _ = 𝔻; _ = F; _ = G; _ = A
        F0 = F₀ ⦃ F ⦄
        F1 = F₁ ⦃ F ⦄
        G0 = F₀ ⦃ G ⦄
        G1 = F₁ ⦃ G ⦄
_-|_.left-extend (⊣→-| {ℂ = ℂ}{𝔻}{F}{G} A){X'}{X}{Y} X~>GY X'~>X =
  proof ε at Y ∘ F1 X~>GY ∘ F1 X'~>X
    === ε at Y ∘ (F1 X~>GY ∘ F1 X'~>X)
      :by: sym $ assoc _ _ _
    === ε at Y ∘ F1 (X~>GY ∘ X'~>X)
      :by: ap (ε at Y ∘_) $ sym $ ∘-preserv X~>GY X'~>X
  qed
  where instance _ = ℂ; _ = 𝔻; _ = F; _ = G; _ = A
        F0 = F₀ ⦃ F ⦄
        F1 = F₁ ⦃ F ⦄
        G0 = F₀ ⦃ G ⦄
        G1 = F₁ ⦃ G ⦄
