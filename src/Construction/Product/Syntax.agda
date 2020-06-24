{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Category
open import Construction.Product.Definition
  as Prod hiding (〈_,_〉)

module Construction.Product.Syntax {ℂ : Category 𝒰 𝒱} where
private instance _ = ℂ
  
open import Proposition.Identity
  renaming (Idₚ to Id) hiding (refl)
open import Proposition.Sum
open import Axiom.UniqueChoice

open import Proof

private
  module Properties {A B : obj} ⦃ P : Product A B ⦄ where

    get-mor :
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      Σₚ λ (h : X ~> A × B) → f == π₁ ∘ h ∧ g == π₂ ∘ h ∧
        ∀ (h' : X ~> A × B) (p : f == π₁ ∘ h' ∧ g == π₂ ∘ h') → h' == h
    get-mor f g = !choice (Prod.〈 f , g 〉)
    
    〈_,_〉 :
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      X ~> A × B
    〈 f , g 〉 = elem (get-mor f g)
    
    prod-mor== : 
      {X : obj}
      {f f' : X ~> A}
      {g g' : X ~> B}
      (p : f == f')
      (q : g == g')
      → ------------------
      〈 f , g 〉 == 〈 f' , g' 〉
    prod-mor== (Id.refl f) (Id.refl g) = refl 〈 f , g 〉
    
    π₁-prop :
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      f == π₁ ∘ 〈 f , g 〉
    π₁-prop f g with get-mor f g
    π₁-prop f g | h , (p , _ , _) = p
    
    π₂-prop :
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      g == π₂ ∘ 〈 f , g 〉
    π₂-prop f g with get-mor f g
    π₂-prop f g | h , (_ , p , _) = p
    
    prod-mor-uniq : 
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      ∀ (h : X ~> A × B) (p : f == π₁ ∘ h ∧ g == π₂ ∘ h) → h == 〈 f , g 〉
    prod-mor-uniq f g with get-mor f g
    prod-mor-uniq f g | _ , (_ , uniq) = uniq
    
    〈π₁,π₂〉==id : 〈 π₁ , π₂ 〉 == id (A × B)
    〈π₁,π₂〉==id = sym $
      prod-mor-uniq π₁ π₂ (id (A × B))
      (sym $ right-unit π₁ , sym $ right-unit π₂)
    
    product-compose :
      {X Y : obj}
      (f : Y ~> A)
      (g : Y ~> B)
      (i : X ~> Y)
      → ------------------
      〈 f , g 〉 ∘ i == 〈 f ∘ i , g ∘ i 〉
    product-compose f g i = prod-mor-uniq (f ∘ i) (g ∘ i) (〈 f , g 〉 ∘ i)
      (sym (proof π₁ ∘ (〈 f , g 〉 ∘ i)
          〉 _==_ 〉 π₁ ∘ 〈 f , g 〉 ∘ i :by: assoc π₁ 〈 f , g 〉 i
          〉 _==_ 〉 f ∘ i             :by: ap (_∘ i) $ sym $ π₁-prop f g
        qed) ,
       sym (proof π₂ ∘ (〈 f , g 〉 ∘ i)
          〉 _==_ 〉 π₂ ∘ 〈 f , g 〉 ∘ i :by: assoc π₂ 〈 f , g 〉 i
          〉 _==_ 〉 g ∘ i             :by: ap (_∘ i) $ sym $ π₂-prop f g
        qed))

open Properties hiding (get-mor) public

infixl 167 _⊠_
_⊠_ :
  {X Y A B : obj}
  (f : X ~> A)
  (g : Y ~> B)
  ⦃ _ : Product X Y ⦄
  ⦃ _ : Product A B ⦄
  → ------------------
  X × Y ~> A × B
f ⊠ g = 〈 f ∘ π₁ , g ∘ π₂ 〉

⊠-compose :
  {X Y Z W A B : obj}
  (g  : X ~> A)
  (f  : Z ~> X)
  (g' : Y ~> B)
  (f' : W ~> Y)
  ⦃ _ : Product Z W ⦄
  ⦃ _ : Product X Y ⦄
  ⦃ _ : Product A B ⦄
  → -------------------------------------
  (g ∘ f) ⊠ (g' ∘ f') == g ⊠ g' ∘ f ⊠ f'
⊠-compose g f g' f' = 
  proof (g ∘ f) ⊠ (g' ∘ f')
    〉 _==_ 〉 〈 g ∘ f ∘ π₁ , g' ∘ f' ∘ π₂ 〉 :by: refl ((g ∘ f) ⊠ (g' ∘ f'))
    〉 _==_ 〉 〈 g ∘ π₁ ∘ ff' , g' ∘ π₂ ∘ ff' 〉
      :by: prod-mor==
        (proof g ∘ f ∘ π₁
           〉 _==_ 〉 g ∘ (f ∘ π₁)   :by: sym $ assoc g f π₁
           〉 _==_ 〉 g ∘ (π₁ ∘ ff') :by: ap (g ∘_) $ π₁-prop (f ∘ π₁) (f' ∘ π₂)
           〉 _==_ 〉 g ∘ π₁ ∘ ff'   :by: assoc g π₁ ff'
         qed)
        (proof g' ∘ f' ∘ π₂
           〉 _==_ 〉 g' ∘ (f' ∘ π₂)  :by: sym $ assoc g' f' π₂
           〉 _==_ 〉 g' ∘ (π₂ ∘ ff') :by: ap (g' ∘_) $ π₂-prop (f ∘ π₁) (f' ∘ π₂)
           〉 _==_ 〉 g' ∘ π₂ ∘ ff'   :by: assoc g' π₂ ff'
         qed)
    〉 _==_ 〉 〈 g ∘ π₁ , g' ∘ π₂ 〉 ∘ ff'
      :by: sym (product-compose (g ∘ π₁) (g' ∘ π₂) ff')
    〉 _==_ 〉 g ⊠ g' ∘ f ⊠ f' :by: refl (g ⊠ g' ∘ f ⊠ f')
  qed
  where ff' = 〈 f ∘ π₁ , f' ∘ π₂ 〉

⊠-id :
  (X X' : obj)
  ⦃ _ : Product X X' ⦄
  → ------------------------------
  id X ⊠ id X' == id (X × X')
⊠-id X X' =
  proof id X ⊠ id X'
    〉 _==_ 〉 〈 id X ∘ π₁ , id X' ∘ π₂ 〉 :by: refl (id X ⊠ id X')
    〉 _==_ 〉 〈 π₁ , id X' ∘ π₂ 〉       :by: ap 〈_, id X' ∘ π₂ 〉 (left-unit π₁)
    〉 _==_ 〉 〈 π₁ , π₂ 〉               :by: ap 〈 π₁ ,_〉 (left-unit π₂) 
    〉 _==_ 〉 id (X × X')              :by: 〈π₁,π₂〉==id
  qed
