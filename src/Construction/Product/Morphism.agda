{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Category

module Construction.Product.Morphism {ℂ : Category 𝒰 𝒱} where
  private instance _ = ℂ
  
  open import Construction.Product.Definition hiding (〈_,_〉)
  open import Construction.Product.Syntax
  
  assoc-mor :
    (A B C : obj)
    ⦃ pab : Product A B ⦄
    ⦃ p[ab]c : Product (A × B) C ⦄
    ⦃ pbc : Product B C ⦄
    ⦃ pa[bc] : Product A (B × C) ⦄
    → --------------------------------
    A × (B × C) ~> A × B × C
  assoc-mor A B C  = 〈 〈 π₁ , π₁ ∘ π₂ 〉 , π₂ {A = B} ∘ π₂ 〉

  assoc-mor-inv :
    (A B C : obj)
    ⦃ pab : Product A B ⦄
    ⦃ p[ab]c : Product (A × B) C ⦄
    ⦃ pbc : Product B C ⦄
    ⦃ pa[bc] : Product A (B × C) ⦄
    → --------------------------------
    A × B × C ~> A × (B × C)
  assoc-mor-inv A B C  = 〈 π₁ ∘ π₁ , 〈 π₂ ∘ π₁ , π₂ 〉 〉

  swap-mor :
    (A B : obj)
    ⦃ pab : Product A B ⦄
    ⦃ pba : Product B A ⦄
    → --------------------
    A × B ~> B × A
  swap-mor A B = 〈 π₂ , π₁ 〉
  
  diagonal-mor :
    (A : obj)
    ⦃ paa : Product A A ⦄
    → ---------------------
    A ~> A × A
  diagonal-mor A = 〈 id A , id A 〉

