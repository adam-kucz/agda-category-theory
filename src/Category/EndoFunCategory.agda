{-# OPTIONS --exact-split --prop #-}
module Category.EndoFunCategory where

open import Category.Definition
open import Functor hiding (Id; _o_)
open import NaturalTransformation renaming (Identity to Id; Composition to _o_)
open import Category.ArrowCategory

open import Universes hiding (X; Y; Z)
open import Logic hiding (_,_)
open import Proof hiding (Id)

open import Axiom.FunctionExtensionality

EndoFunCategory :
  (ℂ : Category 𝒰 𝒱)
  → --------------------
  Category (𝒰 ⊔ 𝒱) (𝒰 ⊔ 𝒱)
EndoFunCategory ℂ = record
  { obj = EndoFunctor ℂ
  ; _~>_ = λ F G → F ⟹ G
  ; id = Id
  ; _∘_ = _o_
  ; left-unit = λ {X} {Y} θ →
    ⟹== (Id Y o θ) θ $ fun-ext λ _ → left-unit _
  ; right-unit = λ {F} {G} θ →
    ⟹== (θ o Id F) θ $ fun-ext λ _ → right-unit _
  ; assoc = λ ψ ϕ θ → 
    ⟹== (ψ o (ϕ o θ)) ((ψ o ϕ) o θ) $ fun-ext λ _ → assoc _ _ _
  }
  where instance _ = ℂ
