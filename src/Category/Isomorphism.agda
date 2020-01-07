{-# OPTIONS --exact-split --safe --prop #-}

open import CategoryTheory.Category.Definition

open import PropUniverses hiding (X; Y)

module CategoryTheory.Category.Isomorphism ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Proposition.Identity using (_==_)
open import Logic

iso : (f : Arrow) → 𝒱 ᵖ
iso (X — f ➙ Y) = ∃ λ (g : Y ~> X) → f ∘ g == id Y ∧ g ∘ f == id X

_≅_ : (X Y : obj) → 𝒱 ᵖ
X ≅ Y = ∃ λ (f : X ~> Y) → iso (X — f ➙ Y)

_≅-unique_ : (X Y : obj) → 𝒱 ᵖ
X ≅-unique Y = ∃! λ (f : X ~> Y) → iso (X — f ➙ Y)

open import Proof
open import Function.Proof
open import Relation.Binary.Property
open import Proposition.Function using (_$_)

iso-uniq : {X Y : obj}
  (f : X ~> Y)
  (f-iso : iso (X — f ➙ Y))
  → -------------------------------------------
  ∃! λ (g : Y ~> X) → f ∘ g == id Y ∧ g ∘ f == id X
iso-uniq {X = X} {Y} f (g , (fg=id , gf=id)) =
  g ,
  ((fg=id , gf=id) ,
    (λ { g' (fg'=id , g'f=id) →
      proof
        g' 〉 _==_ 〉 g' ∘ id Y    :by: sym $ right-unit g'
           〉 _==_ 〉 g' ∘ (f ∘ g) :by: ap (g' ∘_) (sym fg=id)
           〉 _==_ 〉 (g' ∘ f) ∘ g :by: assoc g' f g
           〉 _==_ 〉 id X ∘ g     :by: ap (_∘ g) g'f=id
           〉 _==_ 〉 g            :by: left-unit g
      qed}))

monic : (p : Arrow) → 𝒰 ⊔ 𝒱 ᵖ
monic (X — p ➙ Y) = {W : obj} {f g : W ~> dom p} (q : p ∘ f == p ∘ g) → f == g

epic : {X Y : obj} (p : X ~> Y) → 𝒰 ⊔ 𝒱 ᵖ
epic p = {W : obj} {f g : cod p ~> W} (q : f ∘ p == g ∘ p) → f == g

id-is-monic : (X : obj) → monic (X — id X ➙ X)
id-is-monic X {f = f} {g} q =
  proof f
    〉 _==_ 〉 id X ∘ f :by: sym $ left-unit f
    〉 _==_ 〉 id X ∘ g :by: q
    〉 _==_ 〉 g        :by: left-unit g
  qed

open import Proposition.Proof

∘-monic-closed :
  {X Y Z : obj}
  {f : X ~> Y}
  {g : Y ~> Z}
  (p₁ : monic (X — f ➙ Y))
  (p₂ : monic (Y — g ➙ Z))
  → ----------------------
  monic (X — g ∘ f ➙ Z)
∘-monic-closed {f = f} {g} p₁ p₂ {f = f₁} {g₁} q =
  have g ∘ (f ∘ f₁) == g ∘ (f ∘ g₁)
      :from: proof g ∘ (f ∘ f₁)
               〉 _==_ 〉 g ∘ f ∘ f₁ :by: assoc g f f₁
               〉 _==_ 〉 g ∘ f ∘ g₁ :by: q
               〉 _==_ 〉 g ∘ (f ∘ g₁) :by: sym $ assoc g f g₁
             qed
    ⟶ f ∘ f₁ == f ∘ g₁ :by: p₂
    ⟶ f₁ == g₁        :by: p₁

pre-monic :
  {X Y Z : obj}
  {f : X ~> Y}
  {g : Y ~> Z}
  (p : monic (X — g ∘ f ➙ Z))
  → ----------------------
  monic (X — f ➙ Y)
pre-monic {f = f} {g} p {f = f₁} {g₁} q = p (
  proof g ∘ f ∘ f₁
    〉 _==_ 〉 g ∘ (f ∘ f₁) :by: sym $ assoc g f f₁
    〉 _==_ 〉 g ∘ (f ∘ g₁) :by: ap (g ∘_) q
    〉 _==_ 〉 g ∘ f ∘ g₁   :by: assoc g f g₁
  qed)

split-monic : (s : Arrow) → 𝒱 ᵖ
split-monic (X — s ➙ Y) = ∃ λ (r : Y ~> X) → r ∘ s == id X

split-monic-is-monic : {s : Arrow} (p : split-monic s) → monic s
split-monic-is-monic {X — s ➙ Y} (r , p) {f = f} {g} q =
  proof f
    〉 _==_ 〉 id X ∘ f    :by: sym $ left-unit f
    〉 _==_ 〉 r ∘ s ∘ f   :by: ap (_∘ f) $ sym p
    〉 _==_ 〉 r ∘ (s ∘ f) :by: sym $ assoc r s f
    〉 _==_ 〉 r ∘ (s ∘ g) :by: ap (r ∘_) q
    〉 _==_ 〉 r ∘ s ∘ g   :by: assoc r s g
    〉 _==_ 〉 id X ∘ g    :by: ap (_∘ g) p
    〉 _==_ 〉 g           :by: left-unit g
  qed
