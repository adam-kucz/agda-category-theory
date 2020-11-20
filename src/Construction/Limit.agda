{-# OPTIONS --exact-split --safe --prop #-}
module Construction.Limit where

open import Category
open import Construction.Cone
open import Construction.Terminal

open import PropUniverses
open import Type.Sum renaming (_,_ to _Σ,_)

module WithIndexCategory ⦃ ℂ : Category 𝒰 𝒱 ⦄{𝕀 : Category 𝒲 𝒯} where
  IsLimit :
    (D : Diagram 𝕀)
    (cone : Σ λ (U : obj) → Cone 𝕀 D U)
    → ------------------------------------
    𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ᵖ
  IsLimit D = IsTerminal ⦃ ConeCat 𝕀 D ⦄

  Limit lim← : (D : Diagram 𝕀) → 𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒯 ˙
  Limit D = Terminal ⦃ ConeCat 𝕀 D ⦄
  
  lim← = Limit
  
  open import Proposition.Sum
  open import Proof
  
  LimitIsUniversalCone :
    {D : Diagram 𝕀}
    (L : Limit D)
    → let V = pr₁ (elem L)
          cone = pr₂ (elem L)
    in ----------------------
    IsUniversalCone 𝕀 V cone
  to-universal ⦃ LimitIsUniversalCone (V Σ, c , p) ⦄ {V'} c'
    with (f , pf , q) ← p (V' Σ, c') =
    f , ((λ X → sym $ pf X) ,
         λ f' pf' → caseₚ q (f' , λ X → sym $ pf' X) of λ
         { (Id.refl (f , pf)) → refl f })
  
  open import Morphism.Iso
  
  open import Logic
  
  UniversalCone≅Limit : 
    {D : Diagram 𝕀}
    (L : Limit D)
    (UC : UniversalCone 𝕀 D)
    → let instance _ = UC; _ = ConeCat 𝕀 D
    in ------------------------
    elem L ≅ (U Σ, cone)
  UniversalCone≅Limit L@(V Σ, c , _) UC =
    ∃!→∃ $ universal-cone-uniq-upto-uniq-iso 𝕀
    record { U = V ; cone = c ; universality = LimitIsUniversalCone L }
    UC

open WithIndexCategory public

open import Type.Enumerable

IsFinite : (ℂ : Category 𝒰 𝒱) → 𝒰 ⊔ 𝒱 ˙
IsFinite ℂ = is-enumerable obj × ∀(X Y : obj) → is-enumerable (X ~> Y)
  where instance _ = ℂ

HasAllFiniteLimits : (ℂ : Category 𝒰 𝒱) → 𝒰ω
HasAllFiniteLimits ℂ = ∀{𝒲 𝒳}
  (𝕀 : Category 𝒲 𝒳)
  (fin𝕀 : IsFinite 𝕀)
  → let instance _ = ℂ in
  (D : Diagram 𝕀)
  → -----------------------------------------------
  Limit D
