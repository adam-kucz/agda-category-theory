{-# OPTIONS --exact-split --prop --safe #-}
open import Category
open import PropUniverses

module Construction.Simple.Coproduct.Definition.Explicit
  ⦃ C : Category 𝒰 𝒱 ⦄
  where

open import Proposition.Identity
open import Logic

record IsCoproduct
    (A B : obj)
    (P : obj)
    (inl : A ~> P)
    (inr : B ~> P)
    : ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  where
  field
    from-coproduct :
      {X : obj}
      (f : A ~> X)
      (g : B ~> X)
      → -------------------------------------------
      ∃! λ (h : P ~> X) → h ∘ inl == f ∧ h ∘ inr == g

record Coproduct (A B : obj) : 𝒰 ⊔ 𝒱 ˙ where
  field
    object : obj
    inl : A ~> object
    inr : B ~> object
    ⦃ def ⦄ : IsCoproduct A B object inl inr

open Coproduct ⦃ … ⦄ public

infixl 180 _+_
_+_ : (A B : obj) ⦃ _ : Coproduct A B ⦄ → obj
A + B = object
  
[_,_] :
  {A B X : obj}
  (f : A ~> X)
  (g : B ~> X)
  ⦃ P : Coproduct A B ⦄
  → ------------------
  ∃! λ (h : A + B ~> X) → h ∘ inl == f ∧ h ∘ inr == g
[ f , g ] = IsCoproduct.from-coproduct def f g

