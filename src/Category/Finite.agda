{-# OPTIONS --exact-split --prop #-}
module Category.Finite where

open import Universes
open import Category

open import Type.Unit
open import Type.BinarySum
open import Type.Sum hiding (_,_)
open import Proposition.Empty
open import Proposition.Identity
open import Proposition.Identity.Coercion
open import Proposition.Decidable
open import Proposition.Sum
open import Data.List
open import Data.FinNat
open import Data.Nat hiding (_+_)
open import Proof

f+id : ∀ {m} (f : (a b : Finℕ m) → 𝒰 ˙)(a b : Finℕ m) → 𝒰 ˙
f+id f a b = (Σₚ λ (_ : 𝟙) → (a == b)) + f a b

[_,_]_o_ : ∀ {m}{X Y Z : Finℕ m}
  (f : (a b : Finℕ m) → 𝒰 ˙)
  (compose : ∀ {X}{Y}{Z}
    (g : f Y Z)
    (f₀ : f X Y)
    → f+id f X Z)
  (h : f+id f Y Z)
  (g : f+id f X Y)
  → ---------------------------
  f+id f X Z
[_,_]_o_ {X = X} f _ (inl (⋆ , p)) g =
  coe (ap (f+id f X) p) g
[_,_]_o_ {Z = Z} f _ (inr h) (inl (⋆ , p)) =
  coe (ap (λ — → f+id f — Z) $ sym p) (inr h)
[ _ , compose ] inr h o inr g = compose h g

Finite : ∀ m
  (f : (a b : Finℕ m) → 𝒰 ˙)
  (compose : ∀ {X}{Y}{Z}
    (g : f Y Z)
    (f₀ : f X Y)
    → f+id f X Z)
  (compose-prop : ∀ {X}{Y}{Z}{W}
     (h : f Z W)
     (g : f Y Z)
     (f₀ : f X Y)
     → ----------------------------------------
     [ f , compose ] inr h o compose g f₀ == [ f , compose ] compose h g o inr f₀)
  → -------------------------------------------------------------------------------
  Category 𝒰₀ 𝒰
obj ⦃ Finite m _ _ _ ⦄ = Finℕ m
_~>_ ⦃ Finite _ f _ _ ⦄ = f+id f
id ⦃ Finite _ _ _ _ ⦄ X = inl (⋆ , Idₚ.refl X)
_∘_ ⦃ Finite _ f compose _ ⦄ = [ f , compose ]_o_
left-unit ⦃ Finite _ f _ _ ⦄ {X}{Y} f₁ =
  coe-eval-hom f₁
right-unit ⦃ Finite _ f _ _ ⦄ (inl (⋆ , Idₚ.refl X)) =
  coe-eval-hom (inl (⋆ , Idₚ.refl X))
right-unit ⦃ Finite _ f _ _ ⦄ {X} {Y} (inr y) = coe-eval-hom (inr y)
assoc ⦃ Finite m f c p ⦄ {X}{Y} (inl (⋆ , Idₚ.refl Z)) g f₀ =
  let _o_ = _∘_ ⦃ Finite m f c p ⦄ in
  proof coe (Idₚ.refl _) (g o f₀)
    === g o f₀
      :by: coe-eval-hom _
    === coe (Idₚ.refl _) g o f₀
      :by: ap (_o f₀) $ sym $ coe-eval-hom _
  qed
assoc ⦃ Finite m f c p ⦄ (inr h) (inl (⋆ , Idₚ.refl Y)) f₀ =
  let _o_ = _∘_ ⦃ Finite m f c p ⦄ in
  proof inr h o coe (Idₚ.refl _) f₀
    === inr h o f₀
      :by: ap (inr h o_) $ coe-eval-hom _
    === coe (Idₚ.refl _) (inr h) o f₀
      :by: ap (_o f₀) $ sym $ coe-eval-hom _
  qed
assoc ⦃ Finite m f compose p ⦄ (inr h) (inr g) (inl (⋆ , Idₚ.refl X)) =
  let _o_ = _∘_ ⦃ Finite m f compose p ⦄ in
  proof inr h o coe (Idₚ.refl _) (inr g)
    === compose h g
      :by: ap (inr h o_) $ coe-eval-hom (inr g)
    === compose h g o inl (⋆ , Idₚ.refl X)
      :by: sym $ right-unit ⦃ Finite m f compose p ⦄ (compose h g)
  qed
assoc ⦃ Finite _ f _ p ⦄ (inr h) (inr g) (inr f₀) = p h g f₀

