{-# OPTIONS --exact-split --safe --prop #-}
-- based on Awodey 1.7
module Category.Free where

open import Universes
open import Example.Graphs

open Graph ⦃ … ⦄ hiding (edge)

data Path (G : Graph 𝒰 𝒱)(s : V ⦃ G ⦄) : (t : V ⦃ G ⦄) → 𝒰 ⊔ 𝒱 ˙ where
  empty : Path G s s
  step : let instance _ = G in {v₁ v₂ : V}
    (e : v₁ -E-> v₂)
    (p : Path G s v₁)
    → --------------------
    Path G s v₂

concat : {G : Graph 𝒰 𝒱}{v₀ v₁ v₂ : V ⦃ G ⦄}
  (p₀ : Path G v₁ v₂)
  (p₁ : Path G v₀ v₁)
  → ----------------------
  Path G v₀ v₂
concat empty p₁ = p₁
concat (step e p₀) p₁ = step e (concat p₀ p₁)

open import Proof

concat-right-empty : {G : Graph 𝒰 𝒱}{s t : V ⦃ G ⦄}
  (p : Path G s t)
  → --------------------
  concat p empty == p
concat-right-empty empty = refl empty
concat-right-empty (step e p) = ap (step e) $ concat-right-empty p

concat-assoc : {G : Graph 𝒰 𝒱}{v₀ v₁ v₂ v₃ : V ⦃ G ⦄}
  (p₂ : Path G v₂ v₃)
  (p₁ : Path G v₁ v₂)
  (p₀ : Path G v₀ v₁)
  → --------------------
  concat p₂ (concat p₁ p₀) == concat (concat p₂ p₁) p₀
concat-assoc empty p₁ p₀ = refl (concat p₁ p₀)
concat-assoc (step e p₂) p₁ p₀ = ap (step e) $ concat-assoc p₂ p₁ p₀

open import Category

open import Function hiding (id; _∘_; _$_)

Free : (G : Graph 𝒰 𝒱) → Category 𝒰 (𝒰 ⊔ 𝒱)
Free G = record
  { obj = V ⦃ G ⦄
  ; _~>_ = Path G 
  ; id = λ _ → empty
  ; _∘_ = concat
  ; left-unit = refl
  ; right-unit = concat-right-empty
  ; assoc = concat-assoc
  }
