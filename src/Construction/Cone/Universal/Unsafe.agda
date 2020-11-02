{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Category

module Construction.Cone.Universal.Unsafe (𝕀 : Category 𝒳 𝒵) where

open import Functor
open import NaturalTransformation
open import Construction.Cone.Definition using (Diagram; Cone)
open import Construction.Cone.Universal.Definition

open import Proposition.Identity.Coercion
open import Proof

left-compose-cone :
  {ℂ : Category 𝒰 𝒱}
  {𝔻 : Category 𝒲 𝒯}
  → let instance _ = ℂ; _ = 𝔻 in
  {D : Diagram 𝕀}
  {V : obj}
  (F : Functor ℂ 𝔻)
  (c : Cone 𝕀 D V)
  → ------------------------
  let instance _ = F in
  Cone 𝕀 (F o D) (F₀ V)
left-compose-cone {D = D} {V} F c =
  coe (ap (_⟹ F o D) (o-Const 𝕀 V F))
      (left-compose F c)

-- open import Type.Sum renaming (_,_ to _Σ,_)
-- open import Function.Property
 -- open import Adjunction

-- functor-universal-cone :
--   {ℂ : Category 𝒰 𝒱}
--   {𝔻 : Category 𝒲 𝒯}
--   {D : Diagram 𝕀 ⦃ ℂ ⦄}
--   (univ : UniversalCone ⦃ ℂ ⦄ 𝕀 D)
--   (F : Functor ℂ 𝔻)
--   (A : Σ λ G → G ⊣ F)
--   → -----------------------------
--   let instance _ = ℂ; _ = 𝔻; _ = F; _ = univ in
--   IsUniversalCone 𝕀 (F₀ U) (left-compose-cone F cone)
-- to-universal ⦃ functor-universal-cone {ℂ = ℂ}{_}{D} univ F (G Σ, A) ⦄ {V} c
--   with to-universal ((right-compose ε D) O left-compose-cone G c)
--   where instance _ = univ; _ = ℂ; _ = A
-- to-universal (functor-universal-cone {ℂ = ℂ}{𝔻} univ F (G Σ, A)) {V} c
--   | GV~>U , (comp , uniq) =
--   f ,
--   ((λ i → {!!}) ,
--    λ f' p → {!!})
--   where instance _ = univ; _ = ℂ; _ = 𝔻; _ = A
--         A' = ⊣→-| A
--         f : V ~> F₀ ⦃ F ⦄ U
--         f = back ⦃ _-|_.bijection A' V U ⦄ GV~>U

