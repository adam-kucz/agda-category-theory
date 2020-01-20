{-# OPTIONS --exact-split --prop --safe #-}
open import PropUniverses hiding (B)
open import Category

module Construction.Simple.Pullback.Definition ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Proposition.Identity
open import Logic

record IsPullback
    (A X Y : obj)
    (p : A ~> X)
    (f : Y ~> X)
    (B : obj)
    (u : B ~> A)
    (q : B ~> Y)
    : ---------------------
    𝒰 ⊔ 𝒱 ᵖ
  where
  field
    comm : p ∘ u == f ∘ q
    to-pullback :
      {W : obj}
      (k : W ~> A)
      (h : W ~> Y)
      (comm : p ∘ k == f ∘ h)
      → -------------------------------------------
      ∃! λ (l : W ~> B) → q ∘ l == h ∧ u ∘ l == k

syntax IsPullback A X Y p f B u q =
  is-pullback[ A — p ⇾ X ⇽ f — Y ]-[⇽ u — B — q ⇾]

record Pullback (A X Y : obj)(p : A ~> X)(f : Y ~> X) : 𝒰 ⊔ 𝒱 ˙ where
  field
    B : obj
    u : B ~> A
    q : B ~> Y
    ⦃ def ⦄ : is-pullback[ A — p ⇾ X ⇽ f — Y ]-[⇽ u — B — q ⇾]

open Pullback ⦃ … ⦄ public

syntax Pullback A X Y p f = pullback[ A — p ⇾ X ⇽ f — Y ]
