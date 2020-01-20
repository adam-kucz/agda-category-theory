{-# OPTIONS --exact-split --prop #-}
module Adjunction.Property where

open import Adjunction.Definition

open import Universes

open import Category hiding (compose)
open import Functor
open import NaturalTransformation
  renaming (Composition to _O_;
            right-compose to rc;
            left-compose to lc)

open import Proof

open import Axiom.FunctionExtensionality

-- compose :
--   ⦃ ℂ : Category 𝒰 𝒱 ⦄
--   ⦃ 𝔻 : Category 𝒲 𝒯 ⦄
--   {F H : Functor ℂ 𝔻}
--   {G : Functor 𝔻 ℂ}
--   (A : F ⊣ G)
--   (θ : F ⟹ H)
--   (ϕ : H ⟹ F)
--   → --------------
--   H ⊣ G
-- η ⦃ compose {G = G} A θ ϕ ⦄ = lc G θ O η ⦃ A ⦄
-- ε ⦃ compose {G = G} A θ ϕ ⦄ = ε ⦃ A ⦄ O rc ϕ G
-- axiom-F ⦃ compose {F = F}{H}{G} A θ ϕ ⦄ =
--   ⟹== (rc (ε O rc ϕ G) H O lc H (lc G θ O η)) (Identity H) $
--   fun-ext λ x →
--     proof ε at (H0 x) ∘ ϕ at (G0 (H0 x)) ∘ H1 (G1 (θ at x) ∘ η at x)
--       === id (H0 x)
--         :by: {!axiom-G ⦃ A ⦄!} -- ∀ x → G1 (ε at x) O η at (G0 x) == id (G0 x)
--     qed
--   where instance _ = A
--         G0 = F₀ ⦃ G ⦄
--         H0 = F₀ ⦃ H ⦄
--         G1 = F₁ ⦃ G ⦄
--         H1 = F₁ ⦃ H ⦄
-- axiom-G ⦃ compose A θ ϕ ⦄ = {!!}
