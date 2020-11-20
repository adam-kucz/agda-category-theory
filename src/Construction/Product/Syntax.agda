{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Category
module Construction.Product.Syntax ⦃ ℂ : Category 𝒰 𝒱 ⦄ where
  
open import Proposition.Sum
open import Proof

open import Axiom.UniqueChoice

open import Construction.Product.Definition
  as Prod hiding (〈_,_〉)

private
  instance _ = ℂ
  module Properties {A B : obj} ⦃ P : Product A B ⦄ where

    get-mor :
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      Σₚ λ (h : X ~> A × B) → π₁ ∘ h == f  ∧ π₂ ∘ h == g ∧
        ∀ (h' : X ~> A × B) (p : π₁ ∘ h' == f ∧ π₂ ∘ h' == g) → h' == h
    get-mor f g = !choice (prop P f g)
    
    〈_,_〉 :
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      X ~> A × B
    〈 f , g 〉 = elem (get-mor f g)
    
    π₁-prop :
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      π₁ ∘ 〈 f , g 〉 == f 
    π₁-prop f g with get-mor f g
    π₁-prop f g | h , (p , _ , _) = p
    
    π₂-prop :
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      π₂ ∘ 〈 f , g 〉 == g
    π₂-prop f g with get-mor f g
    π₂-prop f g | h , (_ , p , _) = p
    
    prod-mor-uniq : 
      {X : obj}
      (f : X ~> A)
      (g : X ~> B)
      → ------------------
      ∀ (h : X ~> A × B) (p : π₁ ∘ h == f ∧ π₂ ∘ h == g) → h == 〈 f , g 〉
    prod-mor-uniq f g with get-mor f g
    prod-mor-uniq f g | _ , (_ , uniq) = uniq
    
    〈π₁,π₂〉==id : 〈 π₁ , π₂ 〉 == id (A × B)
    〈π₁,π₂〉==id = sym $
      prod-mor-uniq π₁ π₂ (id (A × B)) (right-unit π₁ , right-unit π₂)
    
    product-compose :
      {X Y : obj}
      (f : Y ~> A)
      (g : Y ~> B)
      (i : X ~> Y)
      → ------------------
      〈 f , g 〉 ∘ i == 〈 f ∘ i , g ∘ i 〉
    product-compose f g i = prod-mor-uniq (f ∘ i) (g ∘ i) (〈 f , g 〉 ∘ i)
      ((proof π₁ ∘ (〈 f , g 〉 ∘ i)
          === π₁ ∘ 〈 f , g 〉 ∘ i :by: assoc π₁ 〈 f , g 〉 i
          === f ∘ i             :by: ap (_∘ i) $ π₁-prop f g
        qed) ,
       (proof π₂ ∘ (〈 f , g 〉 ∘ i)
          === π₂ ∘ 〈 f , g 〉 ∘ i :by: assoc π₂ 〈 f , g 〉 i
          === g ∘ i             :by: ap (_∘ i) $ π₂-prop f g [: _==_ ]
        qed))

open Properties hiding (get-mor) public

prod-mor : {A B : obj}
  (P : Product A B)
  {X : obj}
  (f : X ~> A)
  (g : X ~> B)
  → let instance _ = P
  in ------------------------------
  X ~> A × B
prod-mor P f g = let instance _ = P in 〈 f , g 〉

infixl 167 _⊠_
_⊠_ :
  {X Y A B : obj}
  ⦃ _ : Product X Y ⦄
  ⦃ _ : Product A B ⦄
  (f : X ~> A)
  (g : Y ~> B)
  → ------------------
  X × Y ~> A × B
f ⊠ g = 〈 f ∘ π₁ , g ∘ π₂ 〉

⊠-compose :
  {X Y Z W A B : obj}
  ⦃ Z×W : Product Z W ⦄
  ⦃ X×Y : Product X Y ⦄
  ⦃ A×B : Product A B ⦄
  (g  : X ~> A)
  (f  : Z ~> X)
  (g' : Y ~> B)
  (f' : W ~> Y)
  → -------------------------------------
  (g ∘ f) ⊠ (g' ∘ f') == g ⊠ g' ∘ f ⊠ f'
⊠-compose {X}{Y}{Z}{W} g f g' f' =
  proof (g ∘ f) ⊠ (g' ∘ f')
    === 〈 g ∘ f ∘ π₁z , g' ∘ f' ∘ π₂w 〉
      :by: Id.refl ((g ∘ f) ⊠ (g' ∘ f'))
    === 〈 g ∘ π₁x ∘ ff' , g' ∘ π₂y ∘ ff' 〉
      :by: ap2 〈_,_〉
        (proof g ∘ f ∘ π₁z
           === g ∘ (f ∘ π₁z)   :by: sym $ assoc g f _
           === g ∘ (π₁x ∘ ff')
             :by: ap (g ∘_) $ sym $ π₁-prop (f ∘ π₁z)(f' ∘ π₂w)
           === g ∘ π₁x ∘ ff'   :by: assoc g π₁x ff' [: _==_ ]
         qed)
        (proof g' ∘ f' ∘ π₂w
           === g' ∘ (f' ∘ π₂w)  :by: sym $ assoc g' f' _
           === g' ∘ (π₂y ∘ ff')
             :by: ap (g' ∘_) $ sym $ π₂-prop (f ∘ π₁z)(f' ∘ π₂w)
           === g' ∘ π₂y ∘ ff'   :by: assoc g' π₂y ff' [: _==_ ]
         qed)
    === 〈 g ∘ π₁x , g' ∘ π₂y  〉 ∘ ff'
      :by: sym $ product-compose (g ∘ π₁x) (g' ∘ π₂y) ff'
    === g ⊠ g' ∘ f ⊠ f'
      :by: Id.refl (g ⊠ g' ∘ f ⊠ f')
  qed
  where π₁z : Z × W ~> Z
        π₁z = π₁
        π₁x : X × Y ~> X
        π₁x = π₁
        π₂w : Z × W ~> W
        π₂w = π₂
        π₂y : X × Y ~> Y
        π₂y = π₂
        ff' : Z × W ~> X × Y
        ff' = 〈 f ∘ π₁z , f' ∘ π₂w 〉

⊠-id :
  (X X' : obj)
  ⦃ _ : Product X X' ⦄
  → ------------------------------
  id X ⊠ id X' == id (X × X')
⊠-id X X' =
  proof id X ⊠ id X'
    === 〈 id X ∘ π₁ , id X' ∘ π₂ 〉 :by: refl (id X ⊠ id X')
    === 〈 π₁ , id X' ∘ π₂ 〉       :by: ap 〈_, id X' ∘ π₂ 〉 (left-unit π₁)
    === 〈 π₁ , π₂ 〉               :by: ap 〈 π₁ ,_〉 (left-unit π₂) 
    === id (X × X')              :by: 〈π₁,π₂〉==id
  qed
