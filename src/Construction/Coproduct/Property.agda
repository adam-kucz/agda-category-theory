{-# OPTIONS --exact-split --prop #-}
module Construction.Coproduct.Property where

open import Construction.Coproduct.Definition

open import Universes
import Type.BinarySum as ⊎
open import Type.Sum hiding (_,_)
open import Data.FinNat
open import Logic
open import Function.Property
open import Proposition.Proof
open import Proof

open import Category
open import Functor
open import NaturalTransformation
open import Adjunction
open import Category.Opposite
open import Construction.Cone.Definition
open import Construction.Cone.Universal

functor-coproduct :
  {ℂ 𝔻 : Category 𝒰 𝒱}
  {X Y : obj ⦃ ℂ ⦄}
  (P : Coproduct ⦃ ℂ ⦄ X Y)
  (F : Functor ℂ 𝔻)
  (A : Σ λ G → F ⊣ G)
  → -----------------------------
  let instance _ = F; _ = P; _ = ℂ; _ = ℂ ᵒᵖ in
  IsCoproduct ⦃ 𝔻 ⦄ (F₀ X) (F₀ Y) (F₀ (X + Y)) (F₁ inl) (F₁ inr)
to-universal ⦃ functor-coproduct {ℂ = ℂ}{𝔻}{X}{Y} P F (G Σ., A) ⦄ {V} c
  with [ back (c at ₀) , back (c at ₁) ]
  where instance _ = ℂ; _ = 𝔻; _ = P
        A' : F -| G
        A' = ⊣→-| A
        instance
          bij : ∀ {X}{Y} → Bijection (X ~> F₀ ⦃ G ⦄ Y) (F₀ ⦃ F ⦄ X ~> Y)
          bij {X}{Y} = _-|_.bijection A' X Y
to-universal (functor-coproduct {ℂ = ℂ}{𝔻}{X}{Y} P F (G Σ., A)) {V} c
  | [b[c₀],b[c₁]] , (b[c₀]==[b[c₀],b[c₁]]∘inl , b[c₁]==[b[c₀],b[c₁]]∘inr , uniq) =
  forw [b[c₀],b[c₁]] ,
  ((λ { ₀ → (proof c at ₀
               === forw (back (c at ₀))
                 :by: sym $ right-inv (c at ₀)
               === forw ([b[c₀],b[c₁]] ∘ inl)
                 :by: ap forw b[c₀]==[b[c₀],b[c₁]]∘inl
               === forw [b[c₀],b[c₁]] ∘ F₁ ⦃ F ⦄ inl
                 :by: sym $ _-|_.left-extend A' [b[c₀],b[c₁]] inl
             qed)
      ; ₁ → (proof c at ₁
               === forw (back (c at ₁))
                 :by: sym $ right-inv (c at ₁)
               === forw ([b[c₀],b[c₁]] ∘ inr)
                 :by: ap forw b[c₁]==[b[c₀],b[c₁]]∘inr
               === forw [b[c₀],b[c₁]] ∘ F₁ ⦃ F ⦄ inr
                 :by: sym $ _-|_.left-extend A' [b[c₀],b[c₁]] inr
             qed)}),
    λ FU~>V p →
      proof FU~>V
        === forw (back FU~>V)
          :by: sym $ right-inv FU~>V
        === forw [b[c₀],b[c₁]]
          :by: ap forw $ uniq (back FU~>V) $ ((
            proof back (c at ₀)
              === back (FU~>V ∘ F₁ ⦃ F ⦄ inl)
                :by: ap back $ p ₀
              === back FU~>V ∘ inl
                :by: sym $ _-|_.left-extend-back A' FU~>V inl
            qed) , (
            proof back (c at ₁)
              === back (FU~>V ∘ F₁ ⦃ F ⦄ inr)
                :by: ap back $ p ₁
              === back FU~>V ∘ inr
                :by: sym $ _-|_.left-extend-back A' FU~>V inr
            qed))
      qed)
  where instance _ = ℂ; _ = 𝔻; _ = P; _ = ℂ ᵒᵖ; _ = 𝔻 ᵒᵖ
        A' : F -| G
        A' = ⊣→-| A
        instance
          bij : ∀ {X}{Y} → Bijection (X ~> F₀ ⦃ G ⦄ Y) (F₀ ⦃ F ⦄ X ~> Y)
          bij {X}{Y} = _-|_.bijection A' X Y
          _ = λ {X}{Y} → inverse-left ⦃ bi-inverse ⦃ bij {X}{Y} ⦄ ⦄
          _ = λ {X}{Y} → inverse-right ⦃ bi-inverse ⦃ bij {X}{Y} ⦄ ⦄
