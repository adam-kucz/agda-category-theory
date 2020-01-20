{-# OPTIONS --exact-split --prop  #-}
module Example.Set' where

open import Category

open import Universes
open import Proposition.Identity using (_==_; refl; ap)
open import Logic using (_↔_; ⟶; ⟵; _,_; ⋆ₚ)
open import Function
  renaming (id to id-fun)
  hiding (left-unit; right-unit; _∘_)

Set' : Category (𝒰 ⁺) 𝒰
obj ⦃ Set' {𝒰} ⦄ = 𝒰 ˙
_~>_ ⦃ Set' ⦄ X Y = X → Y
id ⦃ Set' ⦄ X = id-fun
_∘_ ⦃ Set' ⦄ = _∘ₛ_
left-unit ⦃ Set' ⦄ = refl
right-unit ⦃ Set' ⦄ = refl
assoc ⦃ Set' ⦄ _ _ _ = refl _

open import Isomorphism using (iso)
open import Proof hiding (_$_)
open import Proposition.Sum

open import Axiom.FunctionExtensionality

private
  instance
    _ = Set'

open import Function.BijectionEquivalence

iso-in-Set : {X Y : 𝒰 ˙} (f : (x : X) → Y) → iso f ↔ Bijective f
⟶ (iso-in-Set f) (g , (f∘g==id , g∘f==id)) = record {}
  where instance
          inject : Injective f
          surject : Surjective f
          inj ⦃ inject ⦄ {x} {y} fx==fy =
            proof x
              〉 _==_ 〉 g (f x) :by: ==→~ (sym g∘f==id) x
              〉 _==_ 〉 g (f y) :by: ap g fx==fy
              〉 _==_ 〉 y       :by: ==→~ g∘f==id y
            qed
          surj ⦃ surject ⦄ y = g y , ==→~ f∘g==id y
⟵ (iso-in-Set {X = X} {Y} f) q =
  back , (fun-ext right-inv , fun-ext left-inv)
  where instance
          _ = q
          b : Bijection X Y
          b = bijection-of-bijective f ⦃ q ⦄
          _ = inverse-right ⦃ bi-inverse ⦃ b ⦄ ⦄
          _ = inverse-left ⦃ bi-inverse ⦃ b ⦄ ⦄

-- open import Construction.Terminal

-- terminal : (p : Σₚ λ (c : X) → (x : X) → c == x) → IsTerminal X
-- IsTerminal.to-terminal (terminal (c , c==)) Y =
--   (λ _ → c) , λ f → fun-ext λ y → sym (c== (f y))

-- open import Type.Empty renaming (𝟘 to ∅) using ()
-- open import Construction.Initial

-- initial : IsInitial ∅
-- IsTerminal.to-terminal initial X = (λ ()) , λ _ → fun-ext λ ()
