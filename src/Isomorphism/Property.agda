{-# OPTIONS --safe --exact-split --prop  #-}
module Isomorphism.Property where

open import Category
open import Isomorphism.Definition

open import Universes
open import Logic using (_,_)

open import Category.Opposite

iso-self-dual :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  {X Y : obj}
  {f : X ~> Y}
  (iso-f : iso f)
  → --------------------
  let iso-dual = dual (λ ℂ {X}{Y} → iso ⦃ ℂ ⦄{X}{Y}) ℂ
  in iso-dual f
iso-self-dual (g , (left , right)) = g , (right , left)

≅-self-dual :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  {X Y : obj}
  (X≅Y : X ≅ Y)
  → --------------------
  let _≅-dual_ = dual (λ ℂ → _≅_ ⦃ ℂ ⦄) ℂ
  in X ≅-dual Y
≅-self-dual (X~>Y , (Y~>X , p)) = Y~>X , (X~>Y , p)

open import Proposition.Identity using (_==_; ap)
open import Proposition.Function using (_$_)
open import Proof

≅-unique-self-dual :
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  {X Y : obj}
  (X≅Y : X ≅-unique Y)
  → --------------------
  let _≅-unique-dual_ = dual (λ ℂ → _≅-unique_ ⦃ ℂ ⦄) ℂ
  in X ≅-unique-dual Y
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

