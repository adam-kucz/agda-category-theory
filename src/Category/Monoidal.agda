{-# OPTIONS --exact-split --prop #-}
module Category.Monoidal where

open import Category.Definition hiding (ℂ)
open import Category.Cat
open import Category.FunCategory
open import Functor.Definition
open import Functor.Construction
open import NaturalTransformation
open import Construction.Product
open import Isomorphism.Definition

open import Universes
open import Type.Sum hiding (_×_)
open import Proposition.Identity

record MonoidalCategory (𝒰 𝒱 : Universe) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ˙ where
  field
    ⦃ ℂ ⦄ : Category 𝒰 𝒱
  private
    instance
      cat = CatCategory {𝒰}{𝒱}
      pcc = CatProducts {A = ℂ}{ℂ}
      pcc2 = CatProducts {A = ℂ}{_×_ ⦃ cat ⦄ ℂ ℂ ⦃ pcc ⦄}
      pc2c = CatProducts {A = _×_ ⦃ cat ⦄ ℂ ℂ ⦃ pcc ⦄}{ℂ}
  field
    _⊗_ : Functor (ℂ × ℂ) ℂ -- TOOD: change name
  private
    tp = _⊗_
  field
    unit : obj ⦃ ℂ ⦄

  infixl 166 _⨂_
  _⨂_ : (A B : obj ⦃ ℂ ⦄) → obj ⦃ ℂ ⦄
  A ⨂ B = F₀ ⦃ tp ⦄ (A , B)

  private
    instance
      c3 = FunCategory (ℂ × ℂ × ℂ) ℂ
      c1 = FunCategory ℂ ℂ

  field
    α : (tp o (tp ⊠ Id ℂ)) ~> (tp o (Id ℂ ⊠ tp) o assoc-mor-inv ℂ ℂ ℂ)
    α-iso : iso α
  F : (Fun : Functor ℂ (FunCategory ℂ ℂ))(X : obj ⦃ ℂ ⦄) → Functor ℂ ℂ
  F Fun = F₀ {ℂ = ℂ}{𝔻 = FunCategory ℂ ℂ}⦃ Fun ⦄
  field
    ƛ : F (Cur tp) unit ~> Id ℂ
    ƛ-iso : iso ƛ
    ρ : F (Cur (tp o swap-mor ℂ ℂ)) unit ~> Id ℂ
    ρ-iso : iso ρ
    pentagon : (A B C D : obj ⦃ ℂ ⦄)
      → ------------------------------
      {!α at (A , B , C ⨂ D)!} -- α at (A , B , C ⨂ D) ∘ α at (A ⨂ B , C , D)
      ==
      {!!}
      -- (id A ⨂ α at (B , C , D) ∘ α at (A , B ⨂ C , D) ∘ α at (A , B , C) ⨂ id D)
    triangle : (A B : obj ⦃ ℂ ⦄)
      → ---------------------------------------------------
      {!!}
      -- id A ⨂ ƛ at B ∘ α at (A , unit , B) == ρ at A ⨂ id B

open MonoidalCategory ⦃ … ⦄ hiding (ℂ) public

-- {-# DISPLAY tensor-product A B = _⨂_ A B #-}
