{-# OPTIONS --exact-split --safe --prop #-}
module CategoryTheory.Category.Definition where

open import PropUniverses
open import Proposition.Identity using (_==_)
open import Logic

record Category (𝒰 𝒱 : Universe) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ˙ where
  infixl 25 _∘_
  field
    obj : 𝒰 ˙
    _~>_ : (X Y : obj) → 𝒱 ˙
    id : ∀ X → X ~> X
    _∘_ : ∀ {X Y Z} → (g : Y ~> Z) (f : X ~> Y) → X ~> Z
    left-unit : ∀ {X Y} (f : X ~> Y) → id Y ∘ f == f
    right-unit : ∀ {X Y} (f : X ~> Y) → f ∘ id X == f
    assoc : ∀ {X Y Z W}
      (h : Z ~> W)
      (g : Y ~> Z)
      (f : X ~> Y)
      → -----------------------------
      h ∘ (g ∘ f) == (h ∘ g) ∘ f

  mor : (X Y : obj) → 𝒱 ˙
  mor = _~>_
  
  dom : {X Y : obj} (f : X ~> Y) → obj
  dom {X = X} _ = X
  
  cod : {X Y : obj} (f : X ~> Y) → obj
  cod {Y = Y} _ = Y

open Category ⦃ … ⦄ hiding (mor; dom; cod) public

{-# DISPLAY Category._~>_ C X Y = X ~> Y #-}
{-# DISPLAY Category._∘_ C X Y = X ∘ Y #-}

record Arrow ⦃ ℂ : Category 𝒰 𝒱 ⦄ : 𝒰 ⊔ 𝒱 ˙ where
  constructor mk-arrow
  field
    dom cod : obj
    mor : dom ~> cod

pattern _—_➙_ X f Y = mk-arrow X Y f

arrow : ⦃ ℂ : Category 𝒰 𝒱 ⦄ {X Y : obj} (f : X ~> Y) → Arrow
arrow {X = X} {Y} f = X — f ➙ Y

open Category ⦃ … ⦄ using (mor; dom; cod) public
