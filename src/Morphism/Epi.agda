{-# OPTIONS --exact-split --safe --prop #-}
open import Category
open import PropUniverses hiding (X; Y)

module Morphism.Epi ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Proposition.Identity

epi : {A B : obj}(f : A ~> B) → 𝒰 ⊔ 𝒱 ᵖ
epi {A}{B} f = {D : obj}{i j : B ~> D} (p : i ∘ f == j ∘ f) → i == j

epi' : (A B : obj)(f : A ~> B) → 𝒰 ⊔ 𝒱 ᵖ
epi' _ _ f = epi f

syntax epi' A B f = f ˸ A -↠ B

open import Proof

id-is-epi : (X : obj) → epi (id X)
id-is-epi X {i = i}{j} q =
  proof i
    === i ∘ id X :by: sym $ right-unit i
    === j ∘ id X :by: q
    === j        :by: right-unit j
  qed

open import Logic

split-epi : {X Y : obj}(r : X ~> Y) → 𝒱 ᵖ
split-epi {X = X}{Y} r = ∃ λ (s : Y ~> X) → r ∘ s == id Y

split-epi-is-epi :
  {X Y : obj}{r : X ~> Y}
  (p : split-epi r)
  → -----------------------
  epi r
split-epi-is-epi {Y = Y}{r} (s , p) {i = i}{j} q =
  proof i
    === i ∘ id Y    :by: sym $ right-unit i
    === i ∘ (r ∘ s) :by: ap (i ∘_) $ sym p
    === i ∘ r ∘ s   :by: assoc i r s
    === j ∘ r ∘ s   :by: ap (_∘ s) q
    === j ∘ (r ∘ s) :by: sym $ assoc j r s
    === j ∘ id Y    :by: ap (j ∘_) p
    === j           :by: right-unit j
  qed

projective : (P : obj) → 𝒰 ⊔ 𝒱 ᵖ
projective P = ∀{E X e}(p : e ˸ E -↠ X)(f : P ~> X) →
  ∃ λ (fbar : P ~> E) → e ∘ fbar == f

_lifts-across_ : {P X E : obj}(f : P ~> X)(e : E ~> X) → 𝒰 ⊔ 𝒱 ᵖ
_lifts-across_ {P}{X}{E} f e = e ˸ E -↠ X ∧ projective P

epi-into-projective-splits : ∀{P X e}
  (p : projective P)
  (q : e ˸ X -↠ P)
  → ------------------
  split-epi e
epi-into-projective-splits {P} p q = p q (id P)
