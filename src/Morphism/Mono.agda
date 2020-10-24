{-# OPTIONS --exact-split --safe --prop #-}
open import Category
open import PropUniverses hiding (X; Y)

module Morphism.Mono ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Proposition.Identity

mono : {A B : obj}(f : A ~> B) → 𝒰 ⊔ 𝒱 ᵖ
mono {A}{B} f = {C : obj}{g h : C ~> A}(p : f ∘ g == f ∘ h) → g == h

mono' : (A B : obj)(f : A ~> B) → 𝒰 ⊔ 𝒱 ᵖ
mono' _ _ f = mono f

syntax mono' A B f = f ˸ A ⤚→ B

open import Proof
open import Proposition.Proof hiding (id)

id-is-mono : (X : obj) → mono (id X)
id-is-mono X {g = g}{h} q =
  proof g
    === id X ∘ g :by: sym $ left-unit g
    === id X ∘ h :by: q
    === h        :by: left-unit h
  qed

∘-mono-closed :
  {X Y Z : obj}
  {f : X ~> Y}
  {g : Y ~> Z}
  (p₁ : mono f)
  (p₂ : mono g)
  → ----------------------
  mono (g ∘ f)
∘-mono-closed {f = f}{g} p₁ p₂ {g = g'} {h'} q =
  have g ∘ (f ∘ g') == g ∘ (f ∘ h')
      :from: proof g ∘ (f ∘ g')
               === g ∘ f ∘ g'   :by: assoc g f g'
               === g ∘ f ∘ h'   :by: q
               === g ∘ (f ∘ h') :by: sym $ assoc g f h'
             qed
    ⟶ f ∘ g' == f ∘ h' :by: p₂
    ⟶ g' == h'         :by: p₁

pre-mono :
  {X Y Z : obj}
  {f : X ~> Y}
  {g : Y ~> Z}
  (p : mono (g ∘ f))
  → ----------------------
  mono f
pre-mono {f = f} {g} p {g = g'} {h'} q = p (
  proof g ∘ f ∘ g'
    === g ∘ (f ∘ g') :by: sym $ assoc g f g'
    === g ∘ (f ∘ h') :by: ap (g ∘_) q
    === g ∘ f ∘ h'   :by: assoc g f h'
  qed)

open import Logic

split-mono : {X Y : obj}(s : X ~> Y) → 𝒱 ᵖ
split-mono {X = X}{Y} s = ∃ λ (r : Y ~> X) → r ∘ s == id X

-- retraction-of_[_] : {X Y : obj}(s : X ~> Y)(p : split-mono s) → Y ~> X
-- retraction-of s [ r , _ ] = r

retract-of_[_] : {X : obj}(Y : obj){s : X ~> Y}(p : split-mono s) → obj
retract-of_[_] {X} Y p = X

split-mono-is-mono :
  {X Y : obj}{s : X ~> Y}
  (p : split-mono s)
  → -----------------------
  mono s
split-mono-is-mono {X = X}{_}{s} (r , p) {g = g} {h} q =
  proof g
    === id X ∘ g    :by: sym $ left-unit g
    === r ∘ s ∘ g   :by: ap (_∘ g) $ sym p
    === r ∘ (s ∘ g) :by: sym $ assoc r s g
    === r ∘ (s ∘ h) :by: ap (r ∘_) q
    === r ∘ s ∘ h   :by: assoc r s h
    === id X ∘ h    :by: ap (_∘ h) p
    === h           :by: left-unit h
  qed
