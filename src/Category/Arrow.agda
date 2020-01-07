{-# OPTIONS --exact-split --safe --prop #-}

open import CategoryTheory.Category.Definition hiding (dom; cod; mor)

open import Universes

module CategoryTheory.Category.Arrow ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open Arrow
open import Proposition.Identity

record CommutingSquare (f g : Arrow) : 𝒱 ˙ where
  constructor top=_,bot=_,[_]
  field
    top : dom f ~> dom g
    bot : cod f ~> cod g
    commute : bot ∘ mor f == mor g ∘ top

open CommutingSquare

open import Logic

CommutingSquare== :
  {f g : Arrow}
  {◻₁ ◻₂ : CommutingSquare f g}
  → ----------------------------------------------------
  ◻₁ == ◻₂ ↔ top ◻₁ == top ◻₂ ∧ bot ◻₁ == bot ◻₂
⟶ CommutingSquare== (refl ◻) = refl (top ◻) , refl (bot ◻)
⟵ (CommutingSquare== {◻₁ = ◻}) (refl top , refl bot) =
  refl top= top ,bot= bot ,[ commute ◻ ]

open import Proof
open import Relation.Binary.Property using (sym)
open import Proposition.Function using (_$_)

ArrowCategory : Category (𝒰 ⊔ 𝒱) 𝒱
obj ⦃ ArrowCategory ⦄ = Arrow
_~>_ ⦃ ArrowCategory ⦄ = CommutingSquare
id ⦃ ArrowCategory ⦄ f = top= id (dom f) ,bot= id (cod f) ,[
  proof id (cod f) ∘ mor f
    〉 _==_ 〉 mor f              :by: left-unit (mor f)
    〉 _==_ 〉 mor f ∘ id (dom f) :by: sym $ right-unit (mor f)
  qed ]
_∘_ ⦃ ArrowCategory ⦄ {X} {Y} {Z} g f = top= top g ∘ top f ,bot= bot g ∘ bot f ,[
  proof bot g ∘ bot f ∘ mor X
    〉 _==_ 〉 bot g ∘ (bot f ∘ mor X) :by: sym $ assoc (bot g) (bot f) (mor X)
    〉 _==_ 〉 bot g ∘ (mor Y ∘ top f) :by: ap (bot g ∘_) (commute f)
    〉 _==_ 〉 bot g ∘ mor Y ∘ top f   :by: assoc (bot g) (mor Y) (top f)
    〉 _==_ 〉 mor Z ∘ top g ∘ top f   :by: ap (_∘ top f) (commute g)
    〉 _==_ 〉 mor Z ∘ (top g ∘ top f) :by: sym $ assoc (mor Z) (top g) (top f)
  qed ]
left-unit ⦃ ArrowCategory ⦄ f =
  ⟵ CommutingSquare== (left-unit (top f) , left-unit (bot f))
right-unit ⦃ ArrowCategory ⦄ f =
  ⟵ CommutingSquare== (right-unit (top f) , right-unit (bot f))
assoc ⦃ ArrowCategory ⦄ h g f =
  ⟵ CommutingSquare== (assoc (top h) (top g) (top f) , assoc (bot h) (bot g) (bot f))

open import CategoryTheory.Functor

Dom : Functor ArrowCategory ℂ
F₀ ⦃ Dom ⦄ = dom
F₁ ⦃ Dom ⦄ = top
id-preserv ⦃ Dom ⦄ X = refl (id (dom X))
∘-preserv ⦃ Dom ⦄ g f = refl (top g ∘ top f)

Cod : Functor ArrowCategory ℂ
F₀ ⦃ Cod ⦄ = cod
F₁ ⦃ Cod ⦄ = bot
id-preserv ⦃ Cod ⦄ X = refl (id (cod X))
∘-preserv ⦃ Cod ⦄ g f = refl (bot g ∘ bot f)

Refl : Functor ℂ ArrowCategory
F₀ ⦃ Refl ⦄ X = X — id X ➙ X
F₁ ⦃ Refl ⦄ {X} {Y} f = top= f ,bot= f ,[
  proof f ∘ id X
    〉 _==_ 〉 f        :by: right-unit f
    〉 _==_ 〉 id Y ∘ f :by: sym $ left-unit f
  qed ]
id-preserv ⦃ Refl ⦄ X = ⟵ CommutingSquare== (refl (id X) , refl (id X))
∘-preserv ⦃ Refl ⦄ g f = ⟵ CommutingSquare== (refl (g ∘ f) , refl (g ∘ f))
