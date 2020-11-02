{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Category

module Construction.Property.PullbackIsEqualizer ⦃ ℂ : Category 𝒰 𝒱 ⦄ where

open import Construction.Product as Prod
open import Construction.Equalizer as Equal
open import Construction.Pullback hiding (〈_,_〉)

open import Type.BinarySum
open import Type.Unit
open import Data.FinNat
open import Logic
open import Proof

equalizer-pullback :
  {A B C : obj}
  (f : A ~> C)
  (g : B ~> C)
  ⦃ P : Product A B ⦄
  (E : obj)
  (p₁ : E ~> A)
  (p₂ : E ~> B)
  → ----------------------------------------
  IsEqualizer (f ∘ π₁) (g ∘ π₂) E 〈 p₁ , p₂ 〉 ↔ IsPullback f g E p₁ p₂
⟶ (equalizer-pullback f g E p₁ p₂) (fπ₁〈p₁,p₂〉==gπ₂〈p₁,p₂〉 , ump) =
  (proof f ∘ p₁
     === f ∘ (π₁ ∘ 〈 p₁ , p₂ 〉) :by: ap (f ∘_) $ sym $ π₁-prop p₁ p₂
     === f ∘ π₁ ∘ 〈 p₁ , p₂ 〉   :by: assoc f π₁ _
     === g ∘ π₂ ∘ 〈 p₁ , p₂ 〉   :by: fπ₁〈p₁,p₂〉==gπ₂〈p₁,p₂〉
     === g ∘ (π₂ ∘ 〈 p₁ , p₂ 〉) :by: sym $ assoc g π₂ _
     === g ∘ p₂                :by: ap (g ∘_) $ π₂-prop p₁ p₂
   qed) ,
   λ p₁' p₂' q → case ump 〈 p₁' , p₂' 〉 (
     proof f ∘ π₁ ∘ 〈 p₁' , p₂' 〉
       === f ∘ (π₁ ∘ 〈 p₁' , p₂' 〉) :by: sym $ assoc f π₁ _
       === f ∘ p₁'                 :by: ap (f ∘_) $ π₁-prop p₁' p₂'
       === g ∘ p₂'                 :by: q
       === g ∘ (π₂ ∘ 〈 p₁' , p₂' 〉) :by: ap (g ∘_) $ sym $ π₂-prop p₁' p₂'
       === g ∘ π₂ ∘ 〈 p₁' , p₂' 〉   :by: assoc g π₂ _
     qed) of λ { (z , (pz , !z)) → z , ((
       proof p₁ ∘ z
         === π₁ ∘ 〈 p₁ , p₂ 〉 ∘ z   :by: ap (_∘ z) $ sym $ π₁-prop p₁ p₂
         === π₁ ∘ (〈 p₁ , p₂ 〉 ∘ z) :by: sym $ assoc π₁ _ z
         === π₁ ∘ 〈 p₁' , p₂' 〉     :by: ap (π₁ ∘_) $ sym pz
         === p₁'                   :by: π₁-prop p₁' p₂'
       qed) , (
       proof p₂ ∘ z
         === π₂ ∘ 〈 p₁ , p₂ 〉 ∘ z   :by: ap (_∘ z) $ sym $ π₂-prop p₁ p₂
         === π₂ ∘ (〈 p₁ , p₂ 〉 ∘ z) :by: sym $ assoc π₂ _ z
         === π₂ ∘ 〈 p₁' , p₂' 〉     :by: ap (π₂ ∘_) $ sym pz
         === p₂'                   :by: π₂-prop p₁' p₂'
       qed) , λ z' (p₁z'==p₁' , p₂z'==p₂') → !z z' (
         proof 〈 p₁' , p₂' 〉
           === 〈 p₁ ∘ z' , p₂ ∘ z' 〉
             :by: ap2 〈_,_〉 (sym p₁z'==p₁')(sym p₂z'==p₂')
           === 〈 p₁ , p₂ 〉 ∘ z'
             :by: sym $ product-compose p₁ p₂ z'
         qed))}
⟵ (equalizer-pullback f g E p₁ p₂) (fp₁==gp₂ , ump) =
  (proof f ∘ π₁ ∘ 〈 p₁ , p₂ 〉
       === f ∘ (π₁ ∘ 〈 p₁ , p₂ 〉) :by: sym $ assoc f π₁ _
       === f ∘ p₁                :by: ap (f ∘_) $ π₁-prop p₁ p₂
       === g ∘ p₂                :by: fp₁==gp₂
       === g ∘ (π₂ ∘ 〈 p₁ , p₂ 〉) :by: ap (g ∘_) $ sym $ π₂-prop p₁ p₂
       === g ∘ π₂ ∘ 〈 p₁ , p₂ 〉   :by: assoc g π₂ _
     qed) ,
  λ e' p → case ump (π₁ ∘ e')(π₂ ∘ e')(
    proof f ∘ (π₁ ∘ e')
      === f ∘ π₁ ∘ e'   :by: assoc f π₁ e'
      === g ∘ π₂ ∘ e'   :by: p
      === g ∘ (π₂ ∘ e') :by: sym $ assoc g π₂ e'
    qed) of λ { (z , (pz₀ , pz₁ , !z)) → z , (
    (proof e'
       === id _ ∘ e'            :by: sym $ left-unit e'
       === 〈 π₁ , π₂ 〉 ∘ e'      :by: ap (_∘ e') $ sym 〈π₁,π₂〉==id
       === 〈 π₁ ∘ e' , π₂ ∘ e' 〉 :by: product-compose π₁ π₂ e'
       === 〈 p₁ ∘ z , p₂ ∘ z 〉   :by: ap2 〈_,_〉 (sym pz₀)(sym pz₁)
       === 〈 p₁ , p₂ 〉 ∘ z       :by: sym $ product-compose p₁ p₂ z
     qed) , (λ z' pz' → !z z' (
    (proof p₁ ∘ z'
       === π₁ ∘ 〈 p₁ , p₂ 〉 ∘ z'
         :by: ap (_∘ z') $ sym $ π₁-prop p₁ p₂
       === π₁ ∘ (〈 p₁ , p₂ 〉 ∘ z')
         :by: sym $ assoc π₁ 〈 p₁ , p₂ 〉 z'
       === π₁ ∘ e'
         :by: ap (π₁ ∘_) $ sym pz'
     qed) ,
    (proof p₂ ∘ z'
       === π₂ ∘ 〈 p₁ , p₂ 〉 ∘ z'
         :by: ap (_∘ z') $ sym $ π₂-prop p₁ p₂
       === π₂ ∘ (〈 p₁ , p₂ 〉 ∘ z')
         :by: sym $ assoc π₂ 〈 p₁ , p₂ 〉 z'
       === π₂ ∘ e'
         :by: ap (π₂ ∘_) $ sym pz'
     qed))))}

open import Type.Sum renaming (_,_ to _Σ,_; _×_ to _x_) hiding (〈_,_〉)

Products×Equalizers→Pullbacks :
  ⦃ Prods : HasProducts ℂ ⦄
  ⦃ Eqs : HasEqualizers ℂ ⦄
  → ----------------------------------------
  HasPullbacks ℂ
Products×Equalizers→Pullbacks ⦃ Eqs = Eqs ⦄{A}{B}{C}{f}{g}
  with P Σ, e , p ← Eqs {A = A × B}{f = f ∘ π₁}{g ∘ π₂} =
  P Σ, (π₁ ∘ e Σ, π₂ ∘ e) ,
  ⟶ (equalizer-pullback f g P (π₁ ∘ e) (π₂ ∘ e)) $
  Id.coe (ap (IsEqualizer (f ∘ π₁) (g ∘ π₂) P)(
    proof e
      === id (A × B) ∘ e     :by: sym $ left-unit e
      === 〈 π₁ , π₂ 〉 ∘ e     :by: ap (_∘ e) $ sym 〈π₁,π₂〉==id
      === 〈 π₁ ∘ e , π₂ ∘ e 〉 :by: product-compose π₁ π₂ e [: _==_ ]
    qed))
  p

        
