{-# OPTIONS --exact-split --prop  #-}
module CategoryTheory.Example.Set' where

open import CategoryTheory.Category

open import Universes
open import Proposition.Identity using (_==_; refl; ap)
open import Logic using (_↔_; ⟶; ⟵; _,_; ⋆ₚ)
open import Function
  renaming (id to id-fun; _∘_ to _o_)
  hiding (left-unit; right-unit)

Set' : Category (𝒰 ⁺) 𝒰
obj ⦃ Set' {𝒰} ⦄ = 𝒰 ˙
_~>_ ⦃ Set' ⦄ X Y = (x : X) → Y
id ⦃ Set' ⦄ X = id-fun
_∘_ ⦃ Set' ⦄ g f = g o f
left-unit ⦃ Set' ⦄ f = refl f
right-unit ⦃ Set' ⦄ f = refl f
assoc ⦃ Set' ⦄ h g f = refl (h o g o f)

open import Relation.Binary.Property
open import Proof
open import Proposition.Sum using (elem; prop; Σₚ)
open import Function.Extensionality

iso-in-Set : ∀ (f : (x : X) → Y) → iso ⦃ Set' ⦄ f ↔ Bijective f
⟶ (iso-in-Set f) (g , (f∘g==id , g∘f==id)) = record {}
  where instance
          inject : Injective f
          surject : Surjective f
          inj ⦃ inject ⦄ {x} {y} fx==fy =
            proof x
              〉 _==_ 〉 g (f x) :by: ap (_$ x) (sym g∘f==id)
              〉 _==_ 〉 g (f y) :by: ap g fx==fy
              〉 _==_ 〉 y       :by: ap (_$ y) g∘f==id
            qed
          sur ⦃ surject ⦄ y = g y , ap (_$ y) f∘g==id
⟵ (iso-in-Set {X = X} {Y} f) q =
  elem o inv ,
  (fun-ext (λ y → prop (inv y)) ,
   fun-ext (λ x → inj (prop (inv (f x)))))
  where open import Axiom.Choice
        inv : (y : Y) → Σₚ λ x → f x == y
        inv y = choice (sur y)

open import CategoryTheory.Object.Terminal

terminal : (p : Σₚ λ (c : X) → (x : X) → c == x) → IsTerminal ⦃ Set' ⦄ X
IsTerminal.to-terminal (terminal (c , c==)) Y =
  (λ _ → c) , λ f → fun-ext λ y → sym (c== (f y))

open import Type.Empty renaming (𝟘 to ∅) using ()
open import CategoryTheory.Object.Initial

initial : IsInitial ⦃ Set' ⦄ ∅
IsTerminal.to-terminal initial X = (λ ()) , λ _ → fun-ext λ ()
