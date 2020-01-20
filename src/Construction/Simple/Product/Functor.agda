{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Category
open import Construction.Product.Property

module Construction.Product.Functor
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  ⦃ P : HasProducts ℂ ⦄
  where

open import Functor
open import Category.OrderedPair renaming (_×_ to _x_)
open import Construction.Product.Definition ⦃ ℂ ⦄ hiding (〈_,_〉)
open import Type.Sum hiding (_×_)
open import Construction.Product.Unsafe

open import Proof
open import Logic renaming (_,_ to _,,_)

Pair : Functor (ℂ x ℂ) ℂ 
F₀ ⦃ Pair ⦄ (X , X') = X × X'
F₁ ⦃ Pair ⦄ (f , f') = f ⊠ f'
id-preserv ⦃ Pair ⦄ (X , X') = ⊠-id X X'
∘-preserv ⦃ Pair ⦄ (g , g') (f , f') = ⊠-compose g f g' f'
