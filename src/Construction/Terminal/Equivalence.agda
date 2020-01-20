{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Category

module Construction.Terminal.Equivalence ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Construction.Terminal.Definition ⦃ ℂ ⦄
open import Construction.Naive.Terminal ⦃ ℂ ⦄ renaming (
  IsTerminal to IsNaiveTerminal;
  Terminal to NaiveTerminal;
  𝟙 to 𝟙′
  )

private
  to-terminal = IsNaiveTerminal.to-terminal

open import Logic
open import Proposition.Unique
open import Proposition.Sum
open import Type.Empty renaming (𝟘 to EmptyType)
open import Category.Empty
open import Functor.Constant
open import NaturalTransformation.Empty
open import Construction.Cone.Universal

open import Axiom.UniqueChoice

IsTerminal↔IsNaiveTerminal : (T : obj) → IsTerminal T ↔ IsNaiveTerminal T
IsNaiveTerminal.to-terminal (⟶ (IsTerminal↔IsNaiveTerminal T) univ) X =
  elem f-def ,
  λ y → ∧right (prop f-def) y (λ ())
  where instance _ = univ
        f-def = !choice (is-universal (EmptyNatTrans (Const 𝟘 X)))
is-universal ⦃ ⟵ (IsTerminal↔IsNaiveTerminal T) q ⦄ {X} c =
  !get uniq ,
  ((λ ()) ,
   λ f′ _ → !prop uniq f′ )
  where uniq : Unique (X ~> T)
        uniq = to-terminal q X
