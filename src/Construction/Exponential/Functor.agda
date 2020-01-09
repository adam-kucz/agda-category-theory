{-# OPTIONS --exact-split --prop #-}
open import Universes
open import Category
open import Construction.Product
open import Construction.Exponential.Property

module Construction.Exponential.Functor
  ⦃ ℂ : Category 𝒰 𝒱 ⦄
  ⦃ P : HasProducts ℂ ⦄
  ⦃ E : HasExponentials ℂ ⦄
  where

open import Functor
open import Construction.Exponential
open import Construction.Product.Unsafe

open import Proof

^_ : (X : obj) → Functor ℂ ℂ 
F₀ ⦃ ^ X ⦄ Y = Y ^ X
F₁ ⦃ ^ X ⦄ f = cur (f ∘ app)
id-preserv ⦃ ^ X ⦄ Y =
  proof cur (id Y ∘ app)
    〉 _==_ 〉 cur app    :by: ap cur $ left-unit app
    〉 _==_ 〉 id (Y ^ X) :by: cur-app==id
  qed
∘-preserv ⦃ ^ X ⦄ g f = cur-compose-app g f
