{-# OPTIONS --safe --exact-split --prop  #-}
module CategoryTheory.Category.Opposite where

open import CategoryTheory.Category.Definition

open import PropUniverses
open import Proposition.Identity using (_==_; refl)
open import Relation.Binary using (sym)

_ᵒᵖ : (C : Category 𝒰 𝒱) → Category 𝒰 𝒱
C ᵒᵖ = record
  { obj = obj
  ; _~>_ = λ X Y → Y ~> X
  ; id = id
  ; _∘_ = λ g f → f ∘ g
  ; left-unit = right-unit
  ; right-unit = left-unit
  ; assoc = λ h g f → sym (assoc f g h)
  }
  where instance _ = C

open import Function.Property using (Involutive; invol)

instance
  Involutiveᵒᵖ : Involutive (_ᵒᵖ {𝒰} {𝒱})
  invol ⦃ Involutiveᵒᵖ ⦄ = refl

dual : (A : ⦃ C : Category 𝒰 𝒱 ⦄ → X) ⦃ C : Category 𝒰 𝒱 ⦄ → X
dual A ⦃ C ⦄ = A ⦃ C ᵒᵖ ⦄

dualₚ : (A : ⦃ C : Category 𝒰 𝒱 ⦄ → 𝑋) ⦃ C : Category 𝒰 𝒱 ⦄ → 𝑋
dualₚ A ⦃ C ⦄ = A ⦃ C ᵒᵖ ⦄

open import CategoryTheory.Category.Isomorphism
open import Logic using (_,_)

iso-self-dual :
  ⦃ C : Category 𝒰 𝒱 ⦄
  {X Y : obj} (f : X ~> Y)
  (iso-f : iso ⦃ C ⦄ f)
  → ----------------------
  iso ⦃ C ᵒᵖ ⦄ f
iso-self-dual f (g , (g∘f==id , f∘g==id)) = g , (f∘g==id , g∘f==id)

≅-self-dual :
  ⦃ C : Category 𝒰 𝒱 ⦄
  {X Y : obj}
  (X≅Y : X ≅ Y)
  → --------------------
  _≅_ ⦃ C ᵒᵖ ⦄ X Y
≅-self-dual (X~>Y , (Y~>X , p)) = Y~>X , (X~>Y , p)

open import Proposition.Identity using (_==_; ap)
open import Proposition.Function using (_$_)
open import Proof

≅-unique-self-dual :
  ⦃ C : Category 𝒰 𝒱 ⦄
  {X Y : obj}
  (X≅Y : X ≅-unique Y)
  → --------------------
  _≅-unique_ ⦃ C ᵒᵖ ⦄ X Y
≅-unique-self-dual {X = X} {Y}
    (X~>Y , (Y~>X , (X~>Y∘Y~>X==id , Y~>X∘X~>Y==id) , uniq-iso-X~>Y)) =
  Y~>X , (X~>Y , (X~>Y∘Y~>X==id , Y~>X∘X~>Y==id) ,
  λ { Y~>X' (X~>Y' , (X~>Y'∘Y~>X'==id , Y~>X'∘X~>Y'==id)) →
    proof Y~>X'
     〉 _==_ 〉 Y~>X' ∘ id Y          :by: sym $ right-unit Y~>X'
     〉 _==_ 〉 Y~>X' ∘ (X~>Y ∘ Y~>X) :by: ap (Y~>X' ∘_) $ sym X~>Y∘Y~>X==id
     〉 _==_ 〉 Y~>X' ∘ X~>Y ∘ Y~>X   :by: assoc Y~>X' X~>Y Y~>X
     〉 _==_ 〉 Y~>X' ∘ X~>Y' ∘ Y~>X
       :by: ap (λ — → Y~>X' ∘ — ∘ Y~>X) $
            sym $
            uniq-iso-X~>Y X~>Y' (Y~>X' , (X~>Y'∘Y~>X'==id , Y~>X'∘X~>Y'==id))
     〉 _==_ 〉 id X ∘ Y~>X           :by: ap (_∘ Y~>X) Y~>X'∘X~>Y'==id
     〉 _==_ 〉 Y~>X                 :by: left-unit Y~>X
    qed})

