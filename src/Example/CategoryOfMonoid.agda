{-# OPTIONS --safe --exact-split --prop  #-}
module CategoryTheory.Example.CategoryOfMonoid where

open import CategoryTheory.Category
open import Structure.Monoid

open import Universes
open import Type.Unit
open import Proposition.Identity.Property
open import Relation.Binary.Property
  using (refl; trans)
import Operation.Binary.Property as OpProp

CategoryOfMonoid : {X : 𝒰 ˙}
  ⦃ M : Monoid X ⦄
  → --------------------------
  Category 𝒰₀ 𝒰
obj ⦃ CategoryOfMonoid ⦄ = 𝟙
_~>_ ⦃ CategoryOfMonoid {X = X} ⦄ _ _ = X
id ⦃ CategoryOfMonoid ⦄ _ = e
_∘_ ⦃ CategoryOfMonoid ⦄ = _∙_
left-unit ⦃ CategoryOfMonoid ⦃ M ⦄ ⦄ = OpProp.left-unit
right-unit ⦃ CategoryOfMonoid ⦄ = OpProp.right-unit
assoc ⦃ CategoryOfMonoid ⦄ = OpProp.assoc
