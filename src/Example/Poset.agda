{-# OPTIONS --exact-split --prop  #-}
module Example.Poset where

open import Category
open import Structure.PartialOrder

open import PropUniverses
open import Type.Sum renaming (_,_ to _,,_)
open import Proposition.Sum
open import Function
  renaming (id to id-fun; _∘_ to _o_)
  using (Surjective; surj; sur; ==→~; _~_)
open import Proof
open import Structure.Preorder using (monotone; FormPreorder)

Poset : Category (𝒰 ⁺ ⊔ 𝒱 ⁺) (𝒰 ⊔ 𝒱)
obj ⦃ Poset {𝒰}{𝒱} ⦄ = Σ λ (X : 𝒰 ˙) → PartialOrder 𝒱 X
_~>_ ⦃ Poset ⦄ (X ,, Px) (Y ,, Py) =
  Σₚ λ (f : X → Y) → monotone (_⊑_ ⦃ Px ⦄) (_⊑_ ⦃ Py ⦄) f
id ⦃ Poset ⦄ _ =
  id-fun ,
  record { rel-preserv = λ a⊑b → a⊑b }
_∘_ ⦃ Poset ⦄ (g , mon-g) (f , mon-f) =
  g o f ,
  record { rel-preserv = λ a⊑b → ap g (ap f a⊑b) }
  where instance _ = mon-f; _ = mon-g
left-unit ⦃ Poset ⦄ = refl
right-unit ⦃ Poset ⦄ = refl
assoc ⦃ Poset ⦄ _ _ _ = Σₚ== (refl _)

module WithFixedUnvierse {𝒰}{𝒱} where
  private instance Poset' = Poset {𝒰}{𝒱}

  open import Logic
  open import Isomorphism
  open import Relation.Binary hiding (_~_)
  open import Proposition.Proof
  open import Function.Proof using (rel-preserv)
  
  open import Axiom.UniqueChoice
  open import Axiom.FunctionExtensionality
  
  Poset-iso :
    {X Y : obj}
    {f : X ~> Y}
    → ----------------------------------------------------------
    let instance _ = pr₂ X; _ = pr₂ Y
        f' = elem f in
    iso {X = X}{Y} f
    ↔
    Surjective f' ∧ ∀ {x x'} (p : f' x ⊑ f' x') → x ⊑ x'
  surj ⦃ ∧left (⟶ Poset-iso ((f⁻¹ , _) , (f∘f⁻¹==id , _))) ⦄ y =
    f⁻¹ y , ==→~ (from-Σₚ== f∘f⁻¹==id) y
  ∧right (⟶ (Poset-iso {X = _ ,, X-po}{_ ,, Y-po}{f = (f , _)})
             ((f⁻¹ , f⁻¹-mon) , (_ , f⁻¹∘f==id)))
    {x}{x'} p =
    proof x
      〉 _==_ 〉 f⁻¹ (f x) :by: sym $ ==→~ (from-Σₚ== f⁻¹∘f==id) x
      〉 _⊑_ 〉 f⁻¹ (f x') :by: ap f⁻¹ p
      〉 _==_ 〉 x'        :by: ==→~ (from-Σₚ== f⁻¹∘f==id) x'
    qed
    where instance
            _ = X-po; _ = f⁻¹-mon
            open Composable⊑ X-po
  ⟵ (Poset-iso {X = X ,, X-po}{Y ,, Y-po}{f , f-mon})  (sur-f , reflective) =
    f⁻¹ , f⁻¹-mon ,
    (Σₚ== (fun-ext fof⁻¹~id) ,
     Σₚ== (fun-ext f⁻¹of~id))
    where instance
            _ = sur-f; _ = Y-po; _ = X-po; _ = f-mon
            open Composable⊑ X-po
            open Composable⊑ Y-po
          uniq : ∀ y → ∃! λ x → f x == y
          uniq y with sur f y
          uniq y | x , Id.refl _ =
            x , (refl (f x) ,
              λ x₁ p →
              antisym (reflective (
                proof f x₁
                  〉 _⊑_ 〉 f x₁  :by: refl (f x₁)
                  〉 _==_ 〉 f x :by: p
                qed))
              (reflective (
                proof f x
                  〉 _⊑_ 〉 f x  :by: refl (f x)
                  〉 _==_ 〉 f x₁ :by: sym p
                qed)))
          f⁻¹ : Y → X
          f⁻¹ y = elem (!choice (uniq y))
          fof⁻¹~id : f o f⁻¹ ~ id-fun
          fof⁻¹~id y = ∧left (prop (!choice (uniq y)))
          f⁻¹of~id : f⁻¹ o f ~ id-fun
          f⁻¹of~id x =
            have (∀ y (p : f y == f x) → y == f⁻¹ (f x))
                :from: ∧right (prop (!choice (uniq (f x))))
              ⟶ x == f⁻¹ (f x) :by: (λ q → q x (refl (f x)))
              ⟶ f⁻¹ (f x) == x :by: sym
          f⁻¹-mon : monotone (_⊑_ ⦃ Y-po ⦄) (_⊑_ ⦃ X-po ⦄) f⁻¹
          rel-preserv ⦃ f⁻¹-mon ⦄ {a}{b} a⊑b = reflective (
            proof f (f⁻¹ a)
              〉 _==_ 〉 a         :by: fof⁻¹~id a
              〉 _⊑_ 〉 b          :by: a⊑b
              〉 _==_ 〉 f (f⁻¹ b) :by: sym $ fof⁻¹~id b
            qed)
  
  open import Construction.Cone.Universal
  open import Construction.Terminal

  terminal : ∀ {X : obj}
    (p : Σₚ λ (c : pr₁ X) → (x : pr₁ X) → c == x)
    → --------------------------------------
    IsTerminal X
  to-universal ⦃ terminal (c , c==) ⦄ _ =
    (λ _ → c) ,
    record { rel-preserv = λ _ → refl c } ,
    ((λ ()) , λ { (f , _) _ → Σₚ== $ fun-ext λ x → sym $ c== (f x) })
