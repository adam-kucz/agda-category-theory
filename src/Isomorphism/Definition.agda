{-# OPTIONS --exact-split --safe --prop #-}

open import Category

open import PropUniverses hiding (X; Y)

module Isomorphism.Definition ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

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

monic : {X Y : obj} (p : X ~> Y) → 𝒰 ⊔ 𝒱 ᵖ
monic p = {W : obj} {f g : W ~> dom p} (q : p ∘ f == p ∘ g) → f == g

epic : {X Y : obj} (p : X ~> Y) → 𝒰 ⊔ 𝒱 ᵖ
epic p = {W : obj} {f g : cod p ~> W} (q : f ∘ p == g ∘ p) → f == g

id-is-monic : (X : obj) → monic (id X)
id-is-monic X {f = f} {g} q =
  proof f
    === id X ∘ f :by: sym $ left-unit f
    === id X ∘ g :by: q
    === g        :by: left-unit g
  qed

open import Proposition.Proof hiding (id)

∘-monic-closed :
  {X Y Z : obj}
  {f : X ~> Y}
  {g : Y ~> Z}
  (p₁ : monic f)
  (p₂ : monic g)
  → ----------------------
  monic (g ∘ f)
∘-monic-closed {f = f} {g} p₁ p₂ {f = f₁} {g₁} q =
  have g ∘ (f ∘ f₁) == g ∘ (f ∘ g₁)
      :from: proof g ∘ (f ∘ f₁)
               === g ∘ f ∘ f₁ :by: assoc g f f₁
               === g ∘ f ∘ g₁ :by: q
               === g ∘ (f ∘ g₁) :by: sym $ assoc g f g₁
             qed
    ⟶ f ∘ f₁ == f ∘ g₁ :by: p₂
    ⟶ f₁ == g₁        :by: p₁

pre-monic :
  {X Y Z : obj}
  {f : X ~> Y}
  {g : Y ~> Z}
  (p : monic (g ∘ f))
  → ----------------------
  monic f
pre-monic {f = f} {g} p {f = f₁} {g₁} q = p (
  proof g ∘ f ∘ f₁
    === g ∘ (f ∘ f₁) :by: sym $ assoc g f f₁
    === g ∘ (f ∘ g₁) :by: ap (g ∘_) q
    === g ∘ f ∘ g₁   :by: assoc g f g₁
  qed)

split-monic : {X Y : obj}(s : X ~> Y) → 𝒱 ᵖ
split-monic {X = X}{Y} s = ∃ λ (r : Y ~> X) → r ∘ s == id X

split-monic-is-monic :
  {X Y : obj}{s : X ~> Y}
  (p : split-monic s)
  → -----------------------
  monic s
split-monic-is-monic {X = X}{_}{s} (r , p) {f = f} {g} q =
  proof f
    === id X ∘ f    :by: sym $ left-unit f
    === r ∘ s ∘ f   :by: ap (_∘ f) $ sym p
    === r ∘ (s ∘ f) :by: sym $ assoc r s f
    === r ∘ (s ∘ g) :by: ap (r ∘_) q
    === r ∘ s ∘ g   :by: assoc r s g
    === id X ∘ g    :by: ap (_∘ g) p
    === g           :by: left-unit g
  qed

iso-is-split-monic : 
  {X Y : obj}{f : X ~> Y}
  (p : iso f)
  → -----------------------
  split-monic f
iso-is-split-monic (f⁻¹ , (_ , left-inv)) = f⁻¹ , left-inv

iso-is-monic :
  {X Y : obj}{f : X ~> Y}
  (p : iso f)
  → -----------------------
  monic f
iso-is-monic p = split-monic-is-monic $ iso-is-split-monic p
