{-# OPTIONS --safe --exact-split --prop  #-}
module Category.Bijection where

open import Category.Definition

open import Universes
open import Function hiding (id; _∘_; left-unit; right-unit)

on-elems :
  {Obj : 𝒰 ˙}
  (ℂ : Category 𝒱 𝒲)
  (back : Obj → obj ⦃ ℂ ⦄ )
  → --------------------------
  Category 𝒰 𝒲
on-elems {Obj = Obj} ℂ back = record
  { obj = Obj
  ; _~>_ = λ X Y → back X ~> back Y
  ; id = λ X → id (back X)
  ; _∘_ = _∘_
  ; left-unit = left-unit
  ; right-unit = right-unit
  ; assoc = assoc
  }
  where instance _ = ℂ

open import Functor

functor-on-elems :
  {Obj : 𝒰 ˙}
  (F : Functor ℂ 𝔻)
  (back : Obj → obj ⦃ ℂ ⦄)
  → --------------------------
  Functor (on-elems ℂ back) 𝔻
functor-on-elems F back =
  [F₀= F₀ ∘ₛ back
  ,F₁= F₁
  ,id-pres= (λ X → id-preserv (back X))
  ,∘-pres= ∘-preserv
  ]
  where instance _ = F
