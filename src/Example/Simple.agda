{-# OPTIONS --safe --exact-split --prop  #-}
module CategoryTheory.Example.Simple where

open import Universes
open import CategoryTheory.Category

open import Type.Empty renaming (𝟘 to Empty)
open import Type.Unit renaming (𝟙 to Unit)
open import Proposition.Identity

𝟘 : Category 𝒰₀ 𝒰₀
obj ⦃ 𝟘 ⦄ = Empty
_~>_ ⦃ 𝟘 ⦄ ()
id ⦃ 𝟘 ⦄ ()
_∘_ ⦃ 𝟘 ⦄ {()}
left-unit ⦃ 𝟘 ⦄ {()}
right-unit ⦃ 𝟘 ⦄ {()}
assoc ⦃ 𝟘 ⦄ {()}

𝟙 : Category 𝒰₀ 𝒰₀
obj ⦃ 𝟙 ⦄ = Unit
_~>_ ⦃ 𝟙 ⦄ _ _ = Unit
id ⦃ 𝟙 ⦄ _ = ⋆
_∘_ ⦃ 𝟙 ⦄ _ _ = ⋆
left-unit ⦃ 𝟙 ⦄ ⋆ = refl ⋆
right-unit ⦃ 𝟙 ⦄ ⋆ = refl ⋆
assoc ⦃ 𝟙 ⦄ _ _ _ = refl ⋆

open import Type.Identity

Discrete : (X : 𝒰 ˙) → Category 𝒰 𝒰
obj ⦃ Discrete X ⦄ = X
_~>_ ⦃ Discrete X ⦄ = _≡_
id ⦃ Discrete X ⦄ = refl
_∘_ ⦃ Discrete X ⦄ (refl _) g = g
left-unit ⦃ Discrete X ⦄ f = refl f
right-unit ⦃ Discrete X ⦄ (refl x) = refl (refl x)
assoc ⦃ Discrete X ⦄ (refl x) g h = refl (Category._∘_ (Discrete X) g h)


