{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Category

module Construction.Pullback.Property ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Construction.Pullback.Definition
open import Construction.Pullback.Syntax

open import Type.Sum renaming (_,_ to _Σ,_)
open import Logic
open import Proof

open import Construction.Cone.Universal

-- diagram:
-- A' ~ f' ~> B' ~ g' ~> D
-- |         /          /
-- h″       h'         h
-- ↓        ↓         ↙
-- A ~ f ~> B ~ g ~> C
two-pullbacks : {A B C D : obj}
  {f : A ~> B}{g : B ~> C}{h : D ~> C}
  (pull-gh : Pullback g h) →
  let instance _ = pull-gh in
  (pull-fh' : Pullback f p₁) →
  let instance _ = pull-fh' in
  --------------------------------------------------
  IsPullback (g ∘ f) h (A ×[ B ] (B ×[ C ] D)) p₁ (p₂ ∘ p₂)
two-pullbacks {f = f}{g}{h} (B' Σ, (h' Σ, g') , (gh'==hg' , umpB'))
                            (A' Σ, (h″ Σ, f') , (fh″==h'f' , umpA')) =
  (proof g ∘ f ∘ h″
     === g ∘ (f ∘ h″)  :by: sym $ assoc g f h″ 
     === g ∘ (h' ∘ f') :by: ap (g ∘_) fh″==h'f' 
     === g ∘ h' ∘ f'   :by: assoc g h' f' 
     === h ∘ g' ∘ f'   :by: ap (_∘ f') gh'==hg'
     === h ∘ (g' ∘ f') :by: sym $ assoc h g' f'
   qed) ,
  λ p₀' p₁' q → let prf = proof g ∘ (f ∘ p₀')
                            === g ∘ f ∘ p₀' :by: assoc g f p₀'
                            === h ∘ p₁'     :by: q
                          qed
    in case umpB' (f ∘ p₀') p₁' prf of
    λ { (uB' , ((h'uB'==fp₀' , g'uB'==p₁') , !uB')) →
    case umpA' p₀' uB' (sym h'uB'==fp₀') of
    λ { (uA' , ((h″uA'==p₀' , f'uA'==uB') , !uA')) →
    uA' , ((h″uA'==p₀' , (
    proof g' ∘ f' ∘ uA'
      === g' ∘ (f' ∘ uA') :by: sym $ assoc g' f' uA'
      === g' ∘ uB'        :by: ap (g' ∘_) f'uA'==uB'
      === p₁'             :by: g'uB'==p₁'
    qed)) ,
    λ {uA″ (h″uA″==p₀' , g'f'uA'==p₁') →
      !uA' uA″ (h″uA″==p₀' , !uB' (f' ∘ uA″) ((
        proof h' ∘ (f' ∘ uA″)
          === h' ∘ f' ∘ uA″  :by: assoc h' f' uA″
          === f ∘ h″ ∘ uA″   :by: ap (_∘ uA″) $ sym fh″==h'f'
          === f ∘ (h″ ∘ uA″) :by: sym $ assoc f h″ uA″
          === f ∘ p₀'        :by: ap (f ∘_) h″uA″==p₀'
        qed) , (
        proof g' ∘ (f' ∘ uA″)
          === g' ∘ f' ∘ uA″ :by: assoc g' f' uA″
          === p₁'           :by: g'f'uA'==p₁'
        qed)))})}}

open import Morphism.Iso
open import Morphism.Iso.Proof
import Construction.Pullback.AsUniversalCone as CPullback

pullback-associative : {A B C D : obj}
  {f : A ~> B}{g : B ~> C}{h : D ~> C}
  (pull-gh : Pullback g h) →
  let instance _ = pull-gh in
  (pull-fh' : Pullback f p₁) →
  let instance _ = pull-fh' in
  (pull-gfh : Pullback (g ∘ f) h) →
  let instance _ = pull-gfh in
  --------------------------------------------------
  A ×[ B ] (B ×[ C ] D) ≅ A ×[ C ] D
pullback-associative {A}{B}{C}{D} pull-gh pull-fh' pull-gfh@(A×[C]D Σ, _ , _) =
  proof A ×[ B ] (B ×[ C ] D)
    〉 _≅_ 〉 A×[C]D :by: {!!}
    〉 _≅_ 〉 A×[C]D :by: {!!}
  qed
  where instance _ = pull-gh; _ = pull-fh'; _ = pull-gfh
