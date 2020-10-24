{-# OPTIONS --exact-split --safe --prop #-}
open import Category
open import PropUniverses hiding (X; Y)

module Morphism.Mono.Definition ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Proposition.Identity

monic : {A B : obj}(f : A ~> B) → 𝒰 ⊔ 𝒱 ᵖ
monic {A}{B} f = {C : obj}{g h : C ~> A}(p : f ∘ g == f ∘ h) → g == h

monic-syntax : (A B : obj)(f : A ~> B) → 𝒰 ⊔ 𝒱 ᵖ
monic-syntax _ _ f = monic f

syntax monic-syntax A B f = f ˸ A ⤚→ B

open import Proof
open import Proposition.Proof hiding (id)

id-is-monic : (X : obj) → monic (id X)
id-is-monic X {g = g}{h} q =
  proof g
    === id X ∘ g :by: sym $ left-unit g
    === id X ∘ h :by: q
    === h        :by: left-unit h
  qed

∘-monic-closed :
  {X Y Z : obj}
  {g : Y ~> Z}
  {f : X ~> Y}
  (p₁ : monic g)
  (p₂ : monic f)
  → ----------------------
  monic (g ∘ f)
∘-monic-closed {g = g}{f} p₀ p₁ {g = g'} {h'} q =
  have g ∘ (f ∘ g') == g ∘ (f ∘ h')
      :from: proof g ∘ (f ∘ g')
               === g ∘ f ∘ g'   :by: assoc g f g'
               === g ∘ f ∘ h'   :by: q
               === g ∘ (f ∘ h') :by: sym $ assoc g f h'
             qed
    ⟶ f ∘ g' == f ∘ h' :by: p₀
    ⟶ g' == h'         :by: p₁

pre-monic :
  {X Y Z : obj}
  {f : X ~> Y}
  {g : Y ~> Z}
  (p : monic (g ∘ f))
  → ----------------------
  monic f
pre-monic {f = f} {g} p {g = g'} {h'} q = p (
  proof g ∘ f ∘ g'
    === g ∘ (f ∘ g') :by: sym $ assoc g f g'
    === g ∘ (f ∘ h') :by: ap (g ∘_) q
    === g ∘ f ∘ h'   :by: assoc g f h'
  qed)

open import Logic

split-monic : {X Y : obj}(s : X ~> Y) → 𝒱 ᵖ
split-monic {X = X}{Y} s = ∃ λ (r : Y ~> X) → r ∘ s == id X

-- retraction-of_[_] : {X Y : obj}(s : X ~> Y)(p : split-monic s) → Y ~> X
-- retraction-of s [ r , _ ] = r

retract-of_[_] : {X : obj}(Y : obj){s : X ~> Y}(p : split-monic s) → obj
retract-of_[_] {X} Y p = X

split-monic-is-monic :
  {X Y : obj}{s : X ~> Y}
  (p : split-monic s)
  → -----------------------
  monic s
split-monic-is-monic {X = X}{_}{s} (r , p) {g = g} {h} q =
  proof g
    === id X ∘ g    :by: sym $ left-unit g
    === r ∘ s ∘ g   :by: ap (_∘ g) $ sym p
    === r ∘ (s ∘ g) :by: sym $ assoc r s g
    === r ∘ (s ∘ h) :by: ap (r ∘_) q
    === r ∘ s ∘ h   :by: assoc r s h
    === id X ∘ h    :by: ap (_∘ h) p
    === h           :by: left-unit h
  qed
