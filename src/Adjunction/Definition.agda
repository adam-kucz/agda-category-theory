{-# OPTIONS --exact-split --safe --prop #-}
module Adjunction.Definition where

open import Category
open import Functor
open import NaturalTransformation renaming (Composition to _O_)

open import Universes
open import Proposition.Identity hiding (refl)

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

open import Function using (Bijection; forw)

-- alternative definition
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

open import Proof

⊣→-| :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F : Functor ℂ 𝔻}
  {G : Functor 𝔻 ℂ}
  (A : F ⊣ G)
  → --------------------
  F -| G
⊣→-| {ℂ = ℂ}{𝔻}{F}{G} A = record
  { bijection = λ X Y → record
    { forw = λ X~>GY → ε at Y ∘ F1 X~>GY
    ; back = λ FX~>Y → G1 FX~>Y ∘ η at X
    ; left-inverse = λ f →
      proof G1 (ε at Y ∘ F1 f) ∘ η at X
        〉 _==_ 〉 G1 (ε at Y) ∘ G1 (F1 f) ∘ η at X
          :by: ap (_∘ η at X) $ ∘-preserv ⦃ G ⦄ (ε at Y) (F1 f)
        〉 _==_ 〉 G1 (ε at Y) ∘ (G1 (F1 f) ∘ η at X)
          :by: sym $ assoc _ _ _
        〉 _==_ 〉 G1 (ε at Y) ∘ (η at G0 Y ∘ f)
          :by: ap (G1 (ε at Y) ∘_) $ sym $ naturality ⦃ η ⦄ f
        〉 _==_ 〉 G1 (ε at Y) ∘ η at G0 Y ∘ f
          :by: assoc _ _ _
        〉 _==_ 〉 left-compose G (ε) O right-compose (η) G
                   at Y ∘ f
          :by: refl _
        〉 _==_ 〉 Identity G at Y ∘ f
          :by: ap (λ — → — at Y ∘ f) $ axiom-G
        〉 _==_ 〉 f :by: left-unit f
      qed
    ; right-inverse = λ f →
      proof ε at Y ∘ F1 (G1 f ∘ η at X)
        〉 _==_ 〉 ε at Y ∘ (F1 (G1 f) ∘ F1 (η at X))
          :by: ap (ε at Y ∘_) $ ∘-preserv ⦃ F ⦄ (G1 f) (η at X)
        〉 _==_ 〉 ε at Y ∘ F1 (G1 f) ∘ F1 (η at X)
          :by: assoc _ _ _
        〉 _==_ 〉 f ∘ ε at F0 X ∘ F1 (η at X)
          :by: ap (_∘ F1 (η at X)) $ naturality ⦃ ε ⦄ f
        〉 _==_ 〉 f ∘ (ε at F0 X ∘ F1 (η at X))
          :by: sym $ assoc _ _ _
        〉 _==_ 〉 f ∘ right-compose (ε) F O left-compose F (η) at X
          :by: refl _
        〉 _==_ 〉 f ∘ Identity F at X
          :by: ap (λ — → f ∘ — at X) $ axiom-F
        〉 _==_ 〉 f :by: right-unit f
      qed
    }
  ; right-extend = λ {X}{Y}{Y'} X~>GY Y~>Y' →
    proof Y~>Y' ∘ (ε at Y ∘ F1 X~>GY)
      〉 _==_ 〉 Y~>Y' ∘ ε at Y ∘ F1 X~>GY
        :by: assoc _ _ _
      〉 _==_ 〉 ε at Y' ∘ F1 (G1 Y~>Y') ∘ F1 X~>GY
        :by: ap (_∘  F1 X~>GY) $ sym $ naturality ⦃ ε ⦄ Y~>Y'
      〉 _==_ 〉 ε at Y' ∘ (F1 (G1 Y~>Y') ∘ F1 X~>GY)
        :by: sym $ assoc _ _ _
      〉 _==_ 〉 ε at Y' ∘ F1 (G1 Y~>Y' ∘ X~>GY)
        :by: ap (ε at Y' ∘_) $ sym $ ∘-preserv _ _
    qed
  ; left-extend = λ {X'}{X}{Y} X~>GY X'~>X →
    proof ε at Y ∘ F1 X~>GY ∘ F1 X'~>X
      〉 _==_ 〉 ε at Y ∘ (F1 X~>GY ∘ F1 X'~>X)
        :by: sym $ assoc _ _ _
      〉 _==_ 〉 ε at Y ∘ F1 (X~>GY ∘ X'~>X)
        :by: ap (ε at Y ∘_) $ sym $ ∘-preserv X~>GY X'~>X
    qed
  }
  where private instance _ = ℂ; _ = 𝔻; _ = F; _ = G; _ = A
        F0 = F₀ ⦃ F ⦄
        F1 = F₁ ⦃ F ⦄
        G0 = F₀ ⦃ G ⦄
        G1 = F₁ ⦃ G ⦄

