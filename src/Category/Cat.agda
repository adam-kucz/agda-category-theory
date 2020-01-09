{-# OPTIONS --exact-split --prop #-}
module Category.Cat where

open import Category.Definition
open import Functor

open import Universes
open import Proposition.Identity

CatCategory : Category (𝒰 ⁺ ⊔ 𝒱 ⁺) (𝒰 ⊔ 𝒱)
obj ⦃ CatCategory {𝒰} {𝒱} ⦄ = Category 𝒰 𝒱
_~>_ ⦃ CatCategory ⦄ = Functor
id ⦃ CatCategory ⦄ = Id
_∘_ ⦃ CatCategory ⦄ = _o_
left-unit ⦃ CatCategory ⦄ f = refl f
right-unit ⦃ CatCategory ⦄ f = refl f
assoc ⦃ CatCategory ⦄ h g f = refl (h o (g o f))

private
  instance
    _ = CatCategory

open import Construction.Terminal
open import Construction.Initial
open import Example.Simple renaming (𝟙 to 𝟙-Cat; 𝟘 to 𝟘-Cat)
open import Type.Unit renaming (𝟙 to Unit)
open import Logic
open import Functor.Extensionality

terminal : IsTerminal 𝟙-Cat
IsTerminal.to-terminal terminal 𝔻 =
  Const 𝔻 ⋆ ,
  λ F → funct-ext F (Const 𝔻 ⋆)
    (λ X → subsingleton (F₀ ⦃ F ⦄ X) ⋆)
    (λ f → subsingleton (F₁ ⦃ F ⦄ f) ⋆)

open import Type.Empty renaming (𝟘 to ∅) using ()
open import Construction.Initial

initial : IsInitial 𝟘-Cat
IsTerminal.to-terminal initial ℂ =
  Trivial ℂ ,
  λ F → funct-ext F (Trivial ℂ) (λ ()) (λ { {()} })
