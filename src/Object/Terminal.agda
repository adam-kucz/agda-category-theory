{-# OPTIONS --exact-split --safe --prop #-}
module CategoryTheory.Object.Terminal where

open import CategoryTheory.Category

open import PropUniverses
open import Proposition.Unique

record IsTerminal ⦃ C : Category 𝒰 𝒱 ⦄ (𝟙 : obj) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    to-terminal : (X : obj) → Unique (X ~> 𝟙)

record Terminal ⦃ C : Category 𝒰 𝒱 ⦄ : 𝒰 ⊔ 𝒱 ˙ where
  field
    𝟙 : obj
    ⦃ def ⦄ : IsTerminal 𝟙

open Terminal ⦃ … ⦄ public

〈〉 : ⦃ C : Category 𝒰 𝒱 ⦄ (X : obj) ⦃ _ : Terminal ⦄ → Unique (X ~> 𝟙)
〈〉 X = IsTerminal.to-terminal def X

open import Proposition.Sum using (_,_)
open import Proposition.Identity using (_==_; ap)
open import Relation.Binary.Property
open import Proof
open Terminal

terminals-are-isomorphic :
  ⦃ C : Category 𝒰 𝒱 ⦄
  (T T' : Terminal)
  → --------------------------
  𝟙 T ≅-unique 𝟙 T'
terminals-are-isomorphic T T'
  with 〈〉 (𝟙 T) ⦃ T' ⦄ | 〈〉 (𝟙 T') ⦃ T ⦄ | 〈〉 (𝟙 T) ⦃ T ⦄ | 〈〉 (𝟙 T') ⦃ T' ⦄
terminals-are-isomorphic T T'
  | T~>T' , T~>T'-unique | T'~>T , _ | T~>T , T~>T-unique | T'~>T' , T'~>T'-unique =
  T~>T' , (
    (T'~>T ,
      ((proof T~>T' ∘ T'~>T
          〉 _==_ 〉 T'~>T' :by: T'~>T'-unique (T~>T' ∘ T'~>T)
          〉 _==_ 〉 id 1T' :by: sym (T'~>T'-unique (id 1T'))
        qed),
       (proof T'~>T ∘ T~>T' 
          〉 _==_ 〉 T~>T :by: T~>T-unique (T'~>T ∘ T~>T')
          〉 _==_ 〉 id 1T :by: sym (T~>T-unique (id 1T))
        qed))),
    λ other-T~>T' _ → T~>T'-unique other-T~>T')
  where 1T = 𝟙 T
        1T' = 𝟙 T'

isomorphic-to-terminal-is-terminal :
  ⦃ C : Category 𝒰 𝒱 ⦄
  (T : Terminal)
  {X : obj}
  (T≅X : 𝟙 T ≅ X)
  → --------------------------
  IsTerminal X
IsTerminal.to-terminal
  (isomorphic-to-terminal-is-terminal T {X} T≅X) Y with (〈〉 Y ⦃ T ⦄)
IsTerminal.to-terminal
  (isomorphic-to-terminal-is-terminal
    T {X} (f , (g , (f∘g==id , g∘f==id))))
      Y | Y~>T , Y~>T-unique =
  f ∘ Y~>T ,
  λ (y : Y ~> X) →
    proof y
      〉 _==_ 〉 id X ∘ y :by: sym (left-unit y)
      〉 _==_ 〉 (f ∘ g) ∘ y :by: ap (_∘ y) (sym f∘g==id)
      〉 _==_ 〉 f ∘ (g ∘ y) :by: sym (assoc f g y)
      〉 _==_ 〉 f ∘ Y~>T :by: ap (f ∘_) (Y~>T-unique (g ∘ y))
    qed
