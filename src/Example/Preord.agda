{-# OPTIONS --safe --exact-split --prop  #-}
module CategoryTheory.Example.Preord where

open import CategoryTheory.Category
open import Structure.Preorder

open import PropUniverses
open import Type.Sum hiding (_,_)
open import Proposition.Sum
open import Proposition.Identity using (refl; _==_) 
open import Function renaming (id to id-fun; _∘_ to _o_)
open import Function.Proof

Preord : Category (𝒰 ⁺) 𝒰
obj ⦃ Preord {𝒰} ⦄ = Σ λ (X : 𝒰 ˙) → Preorder 𝒰₀ X
_~>_ ⦃ Preord ⦄ X Y = Σₚ λ (f : (x : pr₁ X) → pr₁ Y) → monotone f
  where instance _ = pr₂ X; _ = pr₂ Y
id ⦃ Preord ⦄ X =
  id-fun ,
  record { rel-preserv = λ a⊑b → a⊑b }
_∘_ ⦃ Preord ⦄ (g , mon-g) (f , mon-f) =
  g o f ,
  record { rel-preserv = λ a⊑b → ap g (ap f a⊑b) }
  where instance _ = mon-f; _ = mon-g
left-unit ⦃ Preord ⦄ monotone-f = refl monotone-f
right-unit ⦃ Preord ⦄ monotone-f = refl monotone-f
assoc ⦃ Preord ⦄
  {X = X@(sX Σ., Px)} {Y = (Y Σ., Py)} {Z = (Z Σ., Pz)} {W = (W Σ., Pw)}
  (h , prop₁) (g , prop₂) (f , prop₃) =
  {!!} -- please
  where hi : {X : 𝒰 ˙} {x y : X}
          (𝐴 : (x : X) → 𝒱 ᵖ)
          (p : x == y)
          → ------------------------
          (x Σ., 𝐴 x) == (y Σ., 𝐴 y)
        hi 𝐴 (refl x) = refl (x Σ., 𝐴 x)
        T = Σₚ (monotone ⦃ Px ⦄ ⦃ Pw ⦄)
        -- please : ∀ (h :  g f →
        --          h o (g o f) Σ., monotone ⦃ Px ⦄ ⦃ Pw ⦄ (h o (g o f)) ==
        --          (h o g) o f Σ., monotone ⦃ Px ⦄ ⦃ Pw ⦄ ((h o g) o f)
        -- please h g f = hi (monotone ⦃ Px ⦄ ⦃ Pw ⦄) (refl (h o g o f))
        -- hi2 = {!monotone ⦃ Px ⦄ ⦃ Pw ⦄ (h o (g o f))!}
