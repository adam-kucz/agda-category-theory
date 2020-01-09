{-# OPTIONS --exact-split --safe --prop #-}
module Construction.Initial where

open import Category
open import Category.Opposite
open import Construction.Terminal

open import PropUniverses
open import Proposition.Unique

-- TODO: fix 'dual' in CategoryTheorey.Category.Opposite
IsInitial : ⦃ C : Category 𝒰 𝒱 ⦄ (𝟘 : obj) → 𝒰 ⊔ 𝒱 ᵖ
IsInitial ⦃ C ⦄ = IsTerminal ⦃ C ᵒᵖ ⦄

module IsInitial where
  from-initial :
    ⦃ C : Category 𝒰 𝒱 ⦄
    {𝟘 : obj}
    (init : IsInitial 𝟘)
    (X : obj)
    → ---------------------
    Unique (𝟘 ~> X)
  from-initial ⦃ C ⦄ = IsTerminal.to-terminal ⦃ C ᵒᵖ ⦄

Initial : ⦃ C : Category 𝒰 𝒱 ⦄ → 𝒰 ⊔ 𝒱 ˙
Initial ⦃ C ⦄ = Terminal ⦃ C ᵒᵖ ⦄

module Initial where
  𝟘 : ⦃ C : Category 𝒰 𝒱 ⦄ (I : Initial) → obj
  𝟘 ⦃ C ⦄ = Terminal.𝟙 ⦃ C ᵒᵖ ⦄
  
𝟘 : ⦃ C : Category 𝒰 𝒱 ⦄ ⦃ _ : Initial ⦄ → obj
𝟘 ⦃ C ⦄ = 𝟙 ⦃ C ᵒᵖ ⦄

[] : ⦃ C : Category 𝒰 𝒱 ⦄ (X : obj) ⦃ i : Initial ⦄ → Unique (𝟘 ~> X)
[] ⦃ C ⦄ = 〈〉 ⦃ C ᵒᵖ ⦄

initials-are-isomorphic :
  ⦃ C : Category 𝒰 𝒱 ⦄
  (I I' : Initial ⦃ C ⦄)
  → ---------------------
  Initial.𝟘 I ≅-unique Initial.𝟘 I'
initials-are-isomorphic ⦃ C ⦄ I I' =
  ≅-unique-self-dual ⦃ C ᵒᵖ ⦄ (terminals-are-isomorphic ⦃ C ᵒᵖ ⦄ I I')

isomorphic-to-initial-is-initial :
  ⦃ C : Category 𝒰 𝒱 ⦄
  (I : Initial)
  {X : obj}
  (I≅X : _≅_ ⦃ C ᵒᵖ ⦄ (Initial.𝟘 I) X)
  → --------------------------
  IsInitial X
isomorphic-to-initial-is-initial ⦃ C ⦄ =
  isomorphic-to-terminal-is-terminal ⦃ C ᵒᵖ ⦄
