{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category

module Construction.Initial ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Construction.Terminal
open import Category.Opposite

IsInitial = IsInitial' ℂ
  where IsInitial' = dual (λ ℂ → IsTerminal ⦃ ℂ ⦄)

Initial = Initial' ℂ
  where Initial' = dual (λ ℂ → Terminal ⦃ ℂ ⦄)

𝟘 : ⦃ I : Initial ⦄ → obj
𝟘 = 𝟘' ℂ
  where 𝟘' = dual (λ ℂ ⦃ _ : Terminal ⦃ ℂ ⦄ ⦄ → 𝟙 ⦃ ℂ ⦄)


