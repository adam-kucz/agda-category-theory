{-# OPTIONS --safe --exact-split --prop  #-}
open import Category
open import Structure.Preorder
open import PropUniverses

module Example.CategoryOfPreorder
  {X : 𝒰 ˙}
  ⦃ P : Preorder 𝒱 X ⦄
  where

open import Proof

private
  data Indicator (P : 𝒲 ᵖ) : 𝒲 ˙ where
    ⋆ : (p : P) → Indicator P

  Indicator== : ∀ {P : 𝒲 ᵖ}
    (a b : Indicator P)
    → -----------------------------------
    a == b
  Indicator== (⋆ _) (⋆ _) = refl (⋆ _)

CategoryOfPreorder : Category 𝒰 𝒱
obj ⦃ CategoryOfPreorder ⦄ = X
_~>_ ⦃ CategoryOfPreorder ⦄ x y = Indicator (x ⊑ y)
id ⦃ CategoryOfPreorder ⦄ x = ⋆ (refl x)
_∘_ ⦃ CategoryOfPreorder ⦄ {x}{y}{z} (⋆ y⊑z) (⋆ x⊑y) =
  ⋆ (proof x
       〉 _⊑_ 〉 y :by: x⊑y
       〉 _⊑_ 〉 z :by: y⊑z
     qed)
  where instance _ = composable-trans
                 _ = composable-==-R (_⊑_ ⦃ P ⦄)
left-unit ⦃ CategoryOfPreorder ⦄ (⋆ x⊑y) = refl (⋆ x⊑y)
right-unit ⦃ CategoryOfPreorder ⦄ (⋆ x⊑y) = refl (⋆ x⊑y)
assoc ⦃ CategoryOfPreorder ⦄ (⋆ z⊑w) (⋆ y⊑z) (⋆ x⊑y) = refl (⋆ _)

private instance C = CategoryOfPreorder

open import Proposition.Identity
  renaming (Idₚ to Id) using ()
open import Logic using (_,_; ⋆ₚ)
open import Construction.Terminal

open import Construction.Cone.Universal

terminal :
  {⊤ : X}
  (⊤⊒ : (x : X) → x ⊑ ⊤)
  → -----------------------------------
  IsTerminal ⊤
to-universal ⦃ terminal ⊤⊒ ⦄ {V} _ =
  ⋆ (⊤⊒ V) ,
  ((λ ()),
   (λ _ _ → Indicator== _ _))

open import Construction.Initial

initial :
  {⊥ : X}
  (⊥⊑ : (x : X) → ⊥ ⊑ x)
  → -----------------------------------
  IsInitial ⊥
to-universal ⦃ initial ⊥⊑ ⦄ {V} c =
  ⋆ (⊥⊑ V) ,
  ((λ ()) ,
   λ _ _ → Indicator== _ _)
