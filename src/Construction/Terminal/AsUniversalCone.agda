{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses
open import Category

module Construction.Terminal.AsUniversalCone ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

import Construction.Terminal.Definition ⦃ ℂ ⦄ as T

𝕀 : Category 𝒰₀ 𝒰₀
𝕀 = 𝟘
  where open import Category.Empty

open import Construction.Cone.Definition 𝕀

TerminalDiagram : Diagram
TerminalDiagram = EmptyFunctor ℂ
  where open import Functor.Empty

TerminalCone : (𝟙 : obj) → Cone TerminalDiagram 𝟙
TerminalCone 𝟙 = EmptyNatTrans (Const 𝕀 𝟙)
  where open import Functor.Constant
        open import NaturalTransformation.Empty

open import Construction.Cone.Universal.Definition ⦃ ℂ ⦄ 𝕀

IsTerminal : (𝟙 : obj) → 𝒰 ⊔ 𝒱 ᵖ
IsTerminal 𝟙 = IsUniversalCone 𝟙 (TerminalCone 𝟙)

Terminal : 𝒰 ⊔ 𝒱 ˙
Terminal = UniversalCone TerminalDiagram

𝟙 : ⦃ T : Terminal ⦄ → obj
𝟙 = U

open import Logic
open import Proof

open import NaturalTransformation

IsTerminal↔ : ∀ 𝟙 → IsTerminal 𝟙 ↔ T.IsTerminal 𝟙
⟶ (IsTerminal↔ 𝟙) univ X
  with f , (_ , !f) ← to-universal ⦃ univ ⦄ (TerminalCone X) =
  f , λ f' → !f f' λ ()
to-universal ⦃ ⟵ (IsTerminal↔ 𝟙) q ⦄ {X} _ with f , !f ← q X =
  f , ((λ ()) , λ f' _ → !f f')

open import Morphism.Iso

TTerminal→Terminal : (T : T.Terminal) → Terminal
TTerminal→Terminal T@(_ , p) =
  record { U = T.𝟙; cone = cone'; universality = univ p }
  where instance _ = T
        cone' = TerminalCone T.𝟙
        univ : T.IsTerminal T.𝟙 → IsUniversalCone T.𝟙 cone'
        to-universal ⦃ univ q ⦄ {V} c with f , p ← q V =
          f , ((λ ()) , λ f' _ → p f')

Terminal→TTerminal : (T : Terminal) → T.Terminal
Terminal→TTerminal T = 𝟙 , λ X → go X $ to-universal (c X)
  where instance _ = T
        c = TerminalCone
        go : (V' : obj)
             (p : ∃! λ (f : V' ~> 𝟙) → ∀ X → c V' at X == cone at X ∘ f)
             → --------------------------------------------------
             ∃!-of-type (V' ~> 𝟙)
        go X (f , (_ , !f)) = f , λ f' → !f f' λ ()

Terminal≅ : (T : Terminal)(T' : T.Terminal) → 𝟙 ⦃ T ⦄ ≅ T.𝟙 ⦃ T' ⦄
Terminal≅ T T'@(_ , p)
  with p 𝟙 | to-universal (TerminalCone T.𝟙)
     | p T.𝟙 | to-universal cone
  where instance _ = T; _ = T'
... | f , _ | f⁻¹ , (_ , _) | !id | !id' =
  f , (f⁻¹ , (∃!-of-type== !id (f ∘ f⁻¹) (id _) ,
              ∃!== !id' (λ ()) (λ ())))

