{-# OPTIONS --safe --exact-split --prop  #-}
open import CategoryTheory.Category
open import Structure.Preorder
open import PropUniverses

module CategoryTheory.Example.CategoryOfPreorder
  {X : 𝒰 ˙}
  ⦃ P : Preorder 𝒱 X ⦄
  where

open import Proposition.Identity.Property
open import Relation.Binary.Property
  using (refl; trans)

private
  data Indicator (P : 𝒲 ᵖ) : 𝒲 ˙ where
    ⋆ : (p : P) → Indicator P

CategoryOfPreorder : Category 𝒰 𝒱
obj ⦃ CategoryOfPreorder ⦄ = X
_~>_ ⦃ CategoryOfPreorder ⦄ x y = Indicator (x ⊑ y)
id ⦃ CategoryOfPreorder ⦄ x = ⋆ (refl x)
_∘_ ⦃ CategoryOfPreorder ⦄ (⋆ y⊑z) (⋆ x⊑y) = ⋆ (trans x⊑y y⊑z)
left-unit ⦃ CategoryOfPreorder ⦄ (⋆ x⊑y) = refl (⋆ x⊑y)
right-unit ⦃ CategoryOfPreorder ⦄ (⋆ x⊑y) = refl (⋆ x⊑y)
assoc ⦃ CategoryOfPreorder ⦄ (⋆ z⊑w) (⋆ y⊑z) (⋆ x⊑y) =
  refl (⋆ (trans (trans x⊑y y⊑z) z⊑w))

private
  instance
    C = CategoryOfPreorder

open import Proposition.Identity
  renaming (Idₚ to Id) using ()
open import Logic using (_,_; ⋆ₚ)
open import CategoryTheory.Object.Terminal

terminal :
  {⊤ : X}
  (⊤⊒ : (x : X) → x ⊑ ⊤)
  → -----------------------------------
  IsTerminal ⊤
IsTerminal.to-terminal (terminal ⊤⊒) x = ⋆ (⊤⊒ x) , λ { (⋆ _) → refl (⋆ (⊤⊒ x)) }

open import CategoryTheory.Object.Initial

initial :
  {⊥ : X}
  (⊥⊑ : (x : X) → ⊥ ⊑ x)
  → -----------------------------------
  IsInitial ⊥
IsTerminal.to-terminal (initial ⊥⊑) x = ⋆ (⊥⊑ x) , λ { (⋆ _) → refl (⋆ (⊥⊑ x)) }
