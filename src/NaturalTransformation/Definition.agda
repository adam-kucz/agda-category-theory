{-# OPTIONS --exact-split --safe --prop #-}
module NaturalTransformation.Definition where

open import Category
open import Functor.Definition

open import Universes
open import Proposition.Identity hiding (refl)

infix 215 _⟹_
record _⟹_
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F G : Functor ℂ 𝔻)
  : ----------------------------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  where
  constructor [at=_,naturality=_]
  private
    instance _ = ℂ; _ = 𝔻; _ = F; _ = G

  infix 170 _at_
  field
    _at_ : (X : obj ⦃ ℂ ⦄) → F₀ ⦃ F ⦄ X ~> F₀ ⦃ G ⦄ X
    naturality : ∀ {X Y} (f : X ~> Y) → _at_ Y ∘ F₁ f == F₁ f ∘ _at_ X

open _⟹_ using (_at_) public
open _⟹_ ⦃ … ⦄ using (naturality) public

{-# DISPLAY _⟹_._at_ ϕ Y = ϕ Y #-}
{-# DISPLAY _⟹_.naturality ϕ Y = naturality ϕ Y #-}

⟹== :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F G : Functor ℂ 𝔻}
  (θ ϕ : F ⟹ G)
  (p : _at_ θ == _at_ ϕ)
  → -----------------------------
  θ == ϕ
⟹== θ θ (Id.refl _) = Id.refl θ

⟹het== :
  {ℂ ℂ' : Category 𝒰 𝒱}
  {𝔻 𝔻' : Category 𝒲 𝒯}
  {F G : Functor ℂ 𝔻}
  {F' G' : Functor ℂ' 𝔻'}
  (θ : F ⟹ G)
  (ϕ : F' ⟹ G')
  (ℂ==ℂ' : ℂ == ℂ')
  (𝔻==𝔻' : 𝔻 == 𝔻')
  (F==F' : F Het.== F')
  (G==G' : G Het.== G')
  (p : _at_ θ Het.== _at_ ϕ)
  → -----------------------------
  θ Het.== ϕ
⟹het== θ θ (Id.refl _)(Id.refl _)(Het.refl _)(Het.refl _)(Het.refl _) =
  Het.refl θ

open import Category.ArrowCategory
open import Functor.Construction

-- alternative definition
record NaturalTransformation'
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  (F G : Functor ℂ 𝔻)
  : ----------------------------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  where
  field
    ϕ : Functor ℂ (𝔻 ^→)
    Dom-o-ϕ : Dom ⦃ 𝔻 ⦄ o ϕ == F
    Cod-o-ϕ : Cod ⦃ 𝔻 ⦄ o ϕ == G

open NaturalTransformation' ⦃ … ⦄

open import Function.Property using (Bijection)
open import Proposition.Sum
open import Proof
open import Logic

⟹→NatTrans' :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  {F G : Functor ℂ 𝔻}
  (θ : F ⟹ G)
  → -----------------------------
  NaturalTransformation' F G
⟹→NatTrans' {ℂ = ℂ} {𝔻} {F} {G} θ = record
  { ϕ = record
    { F₀ = λ X → F₀ ⦃ F ⦄ X — θ at X ➙ F₀ ⦃ G ⦄ X
    ; F₁ = λ f → top= F₁ ⦃ F ⦄ f ,bot= F₁ ⦃ G ⦄ f
                 ,[ sym $ naturality ⦃ θ ⦄ f ]
    ; id-preserv = λ X →
      ⟵ (CommutingSquare== ⦃ 𝔻 ⦄)
        (id-preserv ⦃ F ⦄ X , id-preserv ⦃ G ⦄ X)
    ; ∘-preserv = λ g f →
      ⟵ (CommutingSquare== ⦃ 𝔻 ⦄)
        (∘-preserv ⦃ F ⦄ g f , ∘-preserv ⦃ G ⦄ g f)
    }
  ; Dom-o-ϕ = Id.refl F
  ; Cod-o-ϕ = Id.refl G
  }
