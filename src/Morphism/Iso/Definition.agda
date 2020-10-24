{-# OPTIONS --exact-split --safe --prop #-}
open import Category
open import PropUniverses hiding (X; Y)

module Morphism.Iso.Definition ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Proposition.Identity using (_==_)
open import Logic

iso : {X Y : obj} (f : X ~> Y) → 𝒱 ᵖ
iso f = ∃ λ (g : Y ~> X) → f ∘ g == id Y ∧ g ∘ f == id X
  where X = dom f
        Y = cod f

infix 151 _≅_ isomorphic _≅-unique_
_≅_ isomorphic _≅-unique_ : (X Y : obj) → 𝒱 ᵖ
X ≅ Y = ∃ λ (f : X ~> Y) → iso f
isomorphic = _≅_
X ≅-unique Y = ∃! λ (f : X ~> Y) → iso f

syntax isomorphic ⦃ ℂ ⦄ A B = A ≅[ ℂ ] B

open import Proof
open import Function.Proof
open import Relation.Binary.Property
open import Proposition.Function using (_$_)

iso-uniq : {X Y : obj}
  (f : X ~> Y)
  (f-iso : iso f)
  → -------------------------------------------
  ∃! λ (g : Y ~> X) → f ∘ g == id Y ∧ g ∘ f == id X
iso-uniq {X = X} {Y} f (g , (fg=id , gf=id)) =
  g ,
  ((fg=id , gf=id) ,
    (λ { g' (fg'=id , g'f=id) →
      proof g'
        === g' ∘ id Y    :by: sym $ right-unit g'
        === g' ∘ (f ∘ g) :by: ap (g' ∘_) $ sym fg=id
        === (g' ∘ f) ∘ g :by: assoc g' f g
        === id X ∘ g     :by: ap (_∘ g) g'f=id
        === g            :by: left-unit g
      qed}))
  where import Proposition.Identity.Homogeneous.Property as IdHom
        instance hi = IdHom.Relating-all-Id
