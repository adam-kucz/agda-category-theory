{-# OPTIONS --exact-split --prop  #-}
module Example.Mon where

open import Category
open import Structure.Monoid

open import Universes
open import Type.Sum hiding (_,_)
open import Proposition.Sum
open import Function
  renaming (id to id-fun; _∘_ to _o_) using ()
open import Proof

open import Axiom.FunctionExtensionality

Mon : Category (𝒰 ⁺) 𝒰
obj ⦃ Mon {𝒰} ⦄ = Σ λ (X : 𝒰 ˙) → Monoid X
_~>_ ⦃ Mon ⦄ (X Σ., Mx) (Y Σ., My) =
  Σₚ λ (f : X → Y) →
    f e == e ⦃ My ⦄ ∧
    ∀ x y → f (x ∙ y) == f x ∙ f y
  where instance _ = Mx; _ = My
id ⦃ Mon ⦄ (X Σ., Mx) = id-fun , (refl e , λ x y → refl (x ∙ y))
  where instance _ = Mx
_∘_ ⦃ Mon ⦄ {X Σ., Mx}{Y Σ., My}{Z Σ., Mz}(g , (ge , g∙)) (f , (fe , f∙)) = 
  g o f ,
  ((proof g (f e) === g e :by: ap g fe
                  === e   :by: ge
    qed) ,
    (λ x y → proof g (f (x ∙ y))
       === g (f x ∙ f y)     :by: ap g $ f∙ x y
       === g (f x) ∙ g (f y) :by: g∙ (f x) (f y)
     qed))
  where instance _ = Mx; _ = My; _ = Mz
left-unit ⦃ Mon ⦄ = refl
right-unit ⦃ Mon ⦄ = refl
assoc ⦃ Mon ⦄ _ _ _ = Σₚ== (refl _)

module WithFixedUnvierse {𝒰} where
  private instance Mon' = Mon {𝒰}

  open import Construction.Cone.Universal
  open import Construction.Terminal
  
  terminal : ∀ {X : obj}
    (p : Σₚ λ (c : pr₁ X) → (x : pr₁ X) → c == x)
    → --------------------------------------
    IsTerminal X
  to-universal ⦃ terminal {X Σ., M} (c , c==) ⦄ _ =
    (λ _ → c) ,
    (c== e , λ _ _ → c== (c ∙ c)) ,
    ((λ ()) , λ { (f , _) _ → Σₚ== $ fun-ext λ x → sym $ c== (f x) })
    where instance _ = M
