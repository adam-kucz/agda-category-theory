{-# OPTIONS --exact-split --prop #-}
module Category.Cat.Product where

open import Category.Cat.Definition

open import Universes
open import Type.Sum hiding (_×_) renaming (_,_ to _Σ,_)
open import Logic
open import Proof

open import Category
open import Functor
open import Category.Product
open import Construction.Product as P hiding (_×_; 〈_,_〉)

open import Functor.Extensionality

private
  instance _ = CatCategory
  [[_,_]] :
    {ℂ : Category 𝒰 𝒱}
    {𝔻 : Category 𝒰 𝒱}
    {𝕏 : Category 𝒰 𝒱}
    (f : Functor 𝕏 ℂ)
    (g : Functor 𝕏 𝔻)
    → --------------------
    Functor 𝕏 (ℂ × 𝔻)

[[ f , g ]] =
  [F₀= 〈 F₀ ⦃ f ⦄ , F₀ ⦃ g ⦄ 〉
  ,F₁= 〈 F₁ ⦃ f ⦄ , F₁ ⦃ g ⦄ 〉
  ,id-pres= (λ X → ap2 _Σ,_ (id-preserv ⦃ f ⦄ X)(id-preserv ⦃ g ⦄ X))
  ,∘-pres= (λ g' f' → ap2 _Σ,_ (∘-preserv ⦃ f ⦄ g' f')(∘-preserv ⦃ g ⦄ g' f'))
  ]

private
  Σ-het== : {x : X}{x' : Z}{y : Y}{y' : W}
            (p₀ : x Het.== x')
            (p₁ : y Het.== y')
            → --------------------------------------------
            x Σ, y Het.== x' Σ, y'
Σ-het== (Het.refl _)(Het.refl _) = refl _

instance
  CatProducts : HasProducts (CatCategory {𝒰}{𝒱})
CatProducts {A = A}{B} = (A × B Σ, (pi₁ A B Σ, pi₂ A B)) ,
  λ f g → [[ f , g ]] , (refl f , refl g ,
  λ {y (pi₁y==f , pi₂y==g) → funct-ext y [[ f , g ]]
    (λ X → ap2 _Σ,_ (ap (λ — → F₀ ⦃ — ⦄ X) pi₁y==f)
                    (ap (λ — → F₀ ⦃ — ⦄ X) pi₂y==g))
    λ f → Σ-het== (ap (λ — → F₁ ⦃ — ⦄ f) ⦃ Relating-all-==-het== ⦄ pi₁y==f)
                  (ap (λ — → F₁ ⦃ — ⦄ f) ⦃ Relating-all-==-het== ⦄ pi₂y==g)
     })

Cat-prod-prop :
  {𝕏 𝔸 𝔹 : Category 𝒰 𝒱}
  (F : Functor 𝕏 𝔸)
  (G : Functor 𝕏 𝔹)
  → let instance _ = 𝕏 in
  --------------------------------------------------
  (∀(X : obj) → F₀ ⦃ P.〈 F , G 〉 ⦄ X == F₀ ⦃ F ⦄ X Σ, F₀ ⦃ G ⦄ X)
  ∧
  ∀{X X' : obj ⦃ 𝕏 ⦄ }(f : X ~> X') →
    F₁ ⦃ P.〈 F , G 〉 ⦄ f Het.== F₁ ⦃ F ⦄ f Σ, F₁ ⦃ G ⦄ f
∧left (Cat-prod-prop F G) X =
  ap2 _Σ,_ (ap (λ — → F₀ ⦃ — ⦄ X) $ π₁-prop F G)
           (ap (λ — → F₀ ⦃ — ⦄ X) $ π₂-prop F G)
∧right (Cat-prod-prop F G) f =
  Σ-het== (ap (λ — → F₁ ⦃ — ⦄ f)⦃ Relating-all-==-het== ⦄ $ π₁-prop F G)
          (ap (λ — → F₁ ⦃ — ⦄ f)⦃ Relating-all-==-het== ⦄ $ π₂-prop F G)
