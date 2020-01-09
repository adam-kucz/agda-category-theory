{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Category
open import Construction.Terminal as Term hiding (〈〉)

module Construction.Terminal.Property
  ⦃ C : Category 𝒰 𝒱 ⦄
  ⦃ T : Terminal ⦄
  where

open import Axiom.UniqueChoice

〈〉 : (X : obj) → X ~> 𝟙
〈〉 X = !get (Term.〈〉 X)

open import Proposition.Identity
open import Logic
open import Proof

〈〉-id : 〈〉 𝟙 == id 𝟙 
〈〉-id with Term.〈〉 𝟙
〈〉-id | h , uniq =
  proof 〈〉 𝟙
    〉 _==_ 〉 h    :by: uniq (〈〉 𝟙)
    〉 _==_ 〉 id 𝟙 :by: sym $ uniq (id 𝟙)
  qed
