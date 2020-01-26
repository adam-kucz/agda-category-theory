{-# OPTIONS --safe --exact-split --prop  #-}
open import Universes
open import Structure.Monoid

module Example.CategoryOfMonoid {X : 𝒰 ˙} ⦃ M : Monoid X ⦄ where

open import Category

open import Type.Unit
open import Proposition.Identity.Property
open import Relation.Binary.Property
  using (refl; trans)
import Operation.Binary.Property as OpProp

CategoryOfMonoid : Category 𝒰₀ 𝒰
obj ⦃ CategoryOfMonoid ⦄ = 𝟙
_~>_ ⦃ CategoryOfMonoid ⦄ _ _ = X
id ⦃ CategoryOfMonoid ⦄ _ = e
_∘_ ⦃ CategoryOfMonoid ⦄ = _∙_
left-unit ⦃ CategoryOfMonoid ⦄ = OpProp.left-unit
right-unit ⦃ CategoryOfMonoid ⦄ = OpProp.right-unit
assoc ⦃ CategoryOfMonoid ⦄ = OpProp.assoc

private instance C = CategoryOfMonoid

open import Construction.Terminal
open import Construction.Cone.Universal

open import Proposition.Sum
open import Logic
open import Proof

terminal :
  (p : Σₚ λ (c : X) → (x : X) → c == x)
  → --------------------------------------------
  IsTerminal ⋆
to-universal ⦃ terminal (c , c==) ⦄ _ =
  c , ((λ ()) , λ m _ → sym $ c== m)
