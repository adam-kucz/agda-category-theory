{-# OPTIONS --safe --exact-split --prop  #-}
open import Universes
open import Category

module Morphism.Iso.Property ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Morphism.Iso.Definition

open import Logic using (_,_)

open import Category.Opposite

iso-self-dual :
  {X Y : obj}
  {f : X ~> Y}
  (iso-f : iso f)
  → --------------------
  let iso-dual = dual (λ ℂ {X}{Y} → iso ⦃ ℂ ⦄{X}{Y}) ℂ
  in iso-dual f
iso-self-dual (g , (left , right)) = g , (right , left)

≅-self-dual :
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
     === Y~>X' ∘ id Y          :by: sym $ right-unit Y~>X'
     === Y~>X' ∘ (X~>Y ∘ Y~>X) :by: ap (Y~>X' ∘_) $ sym X~>Y∘Y~>X==id
     === Y~>X' ∘ X~>Y ∘ Y~>X   :by: assoc Y~>X' X~>Y Y~>X
     === Y~>X' ∘ X~>Y' ∘ Y~>X
       :by: ap (λ — → Y~>X' ∘ — ∘ Y~>X) $
            sym $
            uniq-iso-X~>Y X~>Y' (Y~>X' , (X~>Y'∘Y~>X'==id , Y~>X'∘X~>Y'==id))
     === id X ∘ Y~>X           :by: ap (_∘ Y~>X) Y~>X'∘X~>Y'==id
     === Y~>X                  :by: left-unit Y~>X
    qed})

open import Relation.Binary

instance
  Reflexive≅ : Reflexive _≅_
  Symmteric≅ : Symmetric _≅_
  Transitive≅ : Transitive _≅_

refl ⦃ Reflexive≅ ⦄ X = id X , (id X , (left-unit (id X) , left-unit (id X)))
sym ⦃ Symmteric≅ ⦄ (f , (f⁻¹ , (p , q))) = (f⁻¹ , (f , (q , p)))
trans ⦃ Transitive≅ ⦄ (f , (f⁻¹ , (pf , qf)))(g , (g⁻¹ , (pg , qg))) =
  g ∘ f , (f⁻¹ ∘ g⁻¹ , ((
  proof g ∘ f ∘ (f⁻¹ ∘ g⁻¹)
    === g ∘ (f ∘ (f⁻¹ ∘ g⁻¹)) :by: sym $ assoc g f _
    === g ∘ (f ∘ f⁻¹ ∘ g⁻¹)   :by: ap (g ∘_) $ assoc f f⁻¹ g⁻¹
    === g ∘ (id _ ∘ g⁻¹)      :by: ap (g ∘_) $ ap (_∘ g⁻¹) pf
    === g ∘ g⁻¹               :by: ap (g ∘_) $ left-unit g⁻¹
    === id _                  :by: pg
  qed) , (
  proof f⁻¹ ∘ g⁻¹ ∘ (g ∘ f)
    === f⁻¹ ∘ (g⁻¹ ∘ (g ∘ f)) :by: sym $ assoc f⁻¹ g⁻¹ _
    === f⁻¹ ∘ (g⁻¹ ∘ g ∘ f)   :by: ap (f⁻¹ ∘_) $ assoc g⁻¹ g f
    === f⁻¹ ∘ (id _ ∘ f)      :by: ap (λ — → f⁻¹ ∘ (— ∘ f)) qg
    === f⁻¹ ∘ f               :by: ap (f⁻¹ ∘_) $ left-unit f
    === id _                  :by: qf
  qed)))
