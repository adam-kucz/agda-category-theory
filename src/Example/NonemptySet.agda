{-# OPTIONS --exact-split --prop  #-}
module Example.NonemptySet where

open import Category

open import Universes
open import Proposition.Empty
open import Proposition.Sum
open import Logic
open import Function
  renaming (id to id-fun; _$_ to _$'_)
  hiding (left-unit; right-unit; _∘_)
open import Proof hiding (Id)

NonemptySet : Category (𝒰 ⁺) 𝒰
obj ⦃ NonemptySet {𝒰} ⦄ = Σₚ λ (X : 𝒰 ˙) → ¬ empty X
_~>_ ⦃ NonemptySet ⦄ (X , _) (Y , _) = X → Y
id ⦃ NonemptySet ⦄ _ = id-fun
_∘_ ⦃ NonemptySet ⦄ = _∘ₛ_
left-unit ⦃ NonemptySet ⦄ = refl
right-unit ⦃ NonemptySet ⦄ = refl
assoc ⦃ NonemptySet ⦄ _ _ _ = refl _

open import Axiom.FunctionExtensionality

module WithUniverse {𝒰 : Universe} where
  private
    instance
      _ = NonemptySet {𝒰}

  open import Construction.Coproduct
  open import Construction.Cone.Universal
  import Type.BinarySum as ⊎
  open ⊎ renaming (_+_ to _⊎_) using () 
  open import NaturalTransformation renaming (Composition to _O_)
  open import Data.FinNat
  
  coproduct : (A B : obj) → Coproduct A B
  coproduct (A , A≠𝟘) (B , B≠𝟘) = record
    { U = A ⊎ B , λ p → A≠𝟘 λ a → p (⊎.inl a)
    ; cone = record
      { _at_ = λ { ₀ → ⊎.inl ; ₁ → ⊎.inr }
      ; naturality = λ { {₀}{₀}(_⊎_.inl _) → refl _
                       ; {₁}{₁}(_⊎_.inl _) → refl _ }
      }
    ; universality = record
      { to-universal = λ c →
        (λ { (_⊎_.inl x) → (c at ₀) x  ; (_⊎_.inr y) → (c at ₁) y }) ,
        ((λ { ₀ → refl _ ; ₁ → refl _ }) ,
          λ f p → fun-ext λ { (_⊎_.inl x) → ==→~ (sym $ p ₀) x
                            ; (_⊎_.inr y) → ==→~ (sym $ p ₁) y})
      }
    }

  open import Functor

  infix 245 [—]^_
  [—]^_ :
    (X : obj)
    → -------------------
    Functor NonemptySet NonemptySet
  F₀ ⦃ [—]^ X@(_ , X≠𝟘) ⦄ Y@(_ , Y≠𝟘) =
    X ~> Y , λ p → Y≠𝟘 λ y → p λ _ → y
  F₁ ⦃ [—]^ _ ⦄ g f = g ∘ₛ f
  id-preserv ⦃ [—]^ _ ⦄ _ = refl id-fun
  ∘-preserv ⦃ [—]^ _ ⦄ g f = fun-ext λ h → refl (g ∘ₛ f ∘ₛ h)

  open import Adjunction
  open import Type.Sum hiding (_,_)
  open import Proposition.Identity using (_≠_)
  open import Construction.Coproduct
  open import Data.Nat hiding (_+_)

  -- [—]^2 : Functor NonemptySet NonemptySet
  -- [—]^2 = [—]^ (Lift𝒰 (Finℕ 2) , λ q → q (↑type ₀))

  -- many-to-2 :
  --   {X : obj}
  --   (p : Σₚ λ (p : elem X × elem X) → pr₁ p ≠ pr₂ p )
  --   → ----------------------------------------------
  --   [—]^ X ⟹ [—]^2
  -- (many-to-2 (x Σ., _ , _) at _) f (↑type ₀) = f x
  -- (many-to-2 (_ Σ., y , _) at _) f (↑type ₁) = f y
  -- naturality ⦃ many-to-2 (x Σ., y , _) ⦄ f =
  --   fun-ext λ g → fun-ext λ
  --     { (↑type ₀) → refl (f (g x))
  --     ; (↑type ₁) → refl (f (g y)) }

  open import Type.Unit

  one : obj
  one = Lift𝒰 𝟙 , λ p → p (↑type ⋆)

  ↑subsingleton : ∀ {𝒱} (x y : Lift𝒰 {𝒱 = 𝒱} 𝟙) → x == y
  ↑subsingleton (↑type ⋆) (↑type ⋆) = refl (↑type ⋆)
  
  open import Proposition.Decidable

  open import Isomorphism
  open import Category.Opposite
  open import Construction.Cone.Definition 𝕀

  private
    module NoRightAdjoint
        {X : obj}
        (p : Σₚ λ (p : elem X × elem X) → pr₁ p ≠ pr₂ p )
        ⦃ d₁ : {x : elem X} → Decidable (pr₁ (elem p) == x) ⦄
        ⦃ d₂ : {x : elem X} → Decidable (pr₂ (elem p) == x) ⦄
        {G : Functor NonemptySet NonemptySet}
        (A : [—]^ X ⊣ G)
        where
      coproduct-𝟙-𝟙 = coproduct one one
      X~>one : obj
      X~>one = X ~> one , λ p → p λ _ → ↑type ⋆
      X~>one-iso :
        Σ λ (f : X~>one ~> one)
        → Σₚ λ (g : one ~> X~>one)
        → f ∘ₛ g == id one ∧ g ∘ₛ f == id X~>one
      X~>one-iso =
        (λ _ → ↑type ⋆) Σ.,
        ((λ _ _ → ↑type ⋆) ,
         ((fun-ext $ ↑subsingleton _) ,
          (fun-ext λ _ → fun-ext λ _ → ↑subsingleton _ _)))
      instance _ = coproduct-𝟙-𝟙
      X~>one+one : obj
      X~>one+one =
        X ~> (one + one) ,
        λ p → p λ _ → _⊎_.inl (↑type ⋆)
      coproduct' :
        (A : [—]^ X ⊣ G)
        → --------------------
        IsCoproduct X~>one X~>one X~>one+one (inl ∘ₛ_) (inr ∘ₛ_)
      coproduct' A = functor-coproduct
        (coproduct one one)
        ([—]^ X)
        (G Σ., A)
      coproduct-𝟙-𝟙' :
        (A : [—]^ X ⊣ G)
        → --------------------
         Coproduct one one
      U ⦃ coproduct-𝟙-𝟙' _ ⦄ = X~>one+one
      cone ⦃ coproduct-𝟙-𝟙' A ⦄ =
        CoproductCocone ((inl ∘ₛ_) ∘ₛ elem (pr₂ X~>one-iso))
                        ((inr ∘ₛ_) ∘ₛ elem (pr₂ X~>one-iso))
      to-universal ⦃ universality ⦃ coproduct-𝟙-𝟙' A ⦄ ⦄ c
        with to-universal ⦃ NonemptySet ᵒᵖ ⦄ ⦃ coproduct' A ⦄
               (compose-cone-diagram ⦃ NonemptySet ᵒᵖ ⦄ c θ)
        where θ :
                CoproductDiagram one one ⟹
                CoproductDiagram X~>one X~>one
              (θ at ₀) _ = ↑type ⋆
              (θ at ₁) _ = ↑type ⋆
              naturality ⦃ θ ⦄ {₀} {₀} (_⊎_.inl _) =
                bi-unit {X = X~>one}{Y = one} _
              naturality ⦃ θ ⦄ {₁}{₁}(_⊎_.inl _) =
                bi-unit {X = X~>one}{Y = one} _
      to-universal (universality (coproduct-𝟙-𝟙' A)) c
        | X~>one+one' , (comp , uniq) =
        X~>one+one' ,
          ((λ { ₀ → fun-ext λ { (↑type ⋆) → ==→~ (comp ₀) (λ _ → ↑type ⋆) }
              ; ₁ → fun-ext λ { (↑type ⋆) → ==→~ (comp ₁) (λ _ → ↑type ⋆) }}) ,
           λ f p → uniq f $ λ
             { ₀ → fun-ext λ g →
               proof (c at ₀) (↑type ⋆)
                 === f (λ x → ⊎.inl (↑type ⋆))
                   :by: ==→~ (p ₀) (↑type ⋆)
                 === f (λ x → ⊎.inl (g x))
                   :by: ap f $ fun-ext λ x →
                          ap ⊎.inl $ ↑subsingleton _ (g x)
               qed
             ; ₁ → fun-ext λ g →
               proof (c at ₁) (↑type ⋆)
                 === f (λ x → ⊎.inr (↑type ⋆))
                   :by: ==→~ (p ₁) (↑type ⋆)
                 === f (λ x → ⊎.inr (g x))
                   :by: ap f $ fun-ext λ x →
                          ap ⊎.inr $ ↑subsingleton _ (g x)
               qed
             })
      isomorphism : let instance _ = NonemptySet ᵒᵖ in
        one + one ≅ X~>one+one
      isomorphism = universal-cone-unique-upto-iso
        ⦃ NonemptySet ᵒᵖ ⦄ 𝕀
        (coproduct-𝟙-𝟙)
        (coproduct-𝟙-𝟙' A)
      x₁ = pr₁ (elem p)
      x₂ = pr₂ (elem p)
      x₁≠x₂ = prop p
      𝟚 = elem one ⊎ elem one
      pattern l₀ = ⊎.inl (↑type ⋆)
      pattern l₁ = ⊎.inr (↑type ⋆)
      no-three-in-𝟙+𝟙 :
        {x y z : 𝟚}
        (p : x ≠ y)(q : y ≠ z)(r : x ≠ z)
        → ⊥
      no-three-in-𝟙+𝟙 {l₀}{l₀} p q r = p (refl l₀)
      no-three-in-𝟙+𝟙 {l₁}{l₁} p q r = p (refl l₁)
      no-three-in-𝟙+𝟙 {l₀}{l₁}{l₀} p q r = r (refl l₀)
      no-three-in-𝟙+𝟙 {l₀}{l₁}{l₁} p q r = q (refl l₁)
      no-three-in-𝟙+𝟙 {l₁}{l₀}{l₀} p q r = q (refl l₀)
      no-three-in-𝟙+𝟙 {l₁}{l₀}{l₁} p q r = r (refl l₁)
      mk-f : (a b : 𝟚) → elem X → 𝟚
      mk-f a b x with decide (x₁ == x)
      mk-f a b x | true _ = a
      mk-f a b x | false _ with decide (x₂ == x)
      mk-f a b x | false _ | true _ = b
      mk-f a b x | false _ | false _ = l₀
      mk-f-aux : ∀ {a a' b b'}
        (p : mk-f a b ~ mk-f a' b')
        → --------------------
        a == a' ∧ b == b'
      mk-f-aux p with p x₁ | p x₂
      mk-f-aux p | a | b
        with decide (x₁ == x₁) ⦃ d₁ ⦄
           | decide (x₁ == x₂) ⦃ d₁ ⦄
      mk-f-aux p | a | b | false ¬p | _ =
        ⊥-recursionₚ _ $ ¬p $ refl x₁
      mk-f-aux p | a | b | true _ | true p =
        ⊥-recursionₚ _ $ x₁≠x₂ p
      mk-f-aux p | a | b | true _ | false _ with decide (x₂ == x₂) ⦃ d₂ ⦄
      mk-f-aux p | a | b | true _ | false _ | false ¬p =
        ⊥-recursionₚ _  $ ¬p $ refl x₂
      mk-f-aux p | a | b | true _ | false _ | true _ = a , b
      mk-f-inj : ∀ {a a' b b'}
        (p : a ≠ a' ∨ b ≠ b')
        → --------------------
        mk-f a b ≠ mk-f a' b'
      mk-f-inj (∨left p) q = p $ ∧left $ mk-f-aux $ ==→~ q
      mk-f-inj (∨right p) q = p $ ∧right $ mk-f-aux $ ==→~ q
      l₀≠l₁ : _≠_ {X = 𝟚}{𝟚} l₀ l₁
      l₀≠l₁ ()
      finish : ⊥
      finish with isomorphism
      finish | f , (f⁻¹ , (left , right)) =
        no-three-in-𝟙+𝟙
          (inject (mk-f-inj {l₀}{l₀}{l₀}{l₁} $ ∨right l₀≠l₁))
          (inject (mk-f-inj {l₀}{l₁}{l₁}{l₁} $ ∨left l₀≠l₁))
          (inject (mk-f-inj {l₀}{l₁}{l₀}{l₁} $ ∨left l₀≠l₁))
        where inject : ∀ {g h}
                (p : g ≠ h)
                → -------------
                f g ≠ f h
              inject {g}{h} p q = p (
                proof g
                  === f⁻¹ (f g) :by: sym $ ==→~ left g
                  === f⁻¹ (f h) :by: ap f⁻¹ q
                  === h         :by: ==→~ left h
                qed)
              
  no-right-adjoint :
    (X : obj)
    (p : Σₚ λ (p : elem X × elem X) → pr₁ p ≠ pr₂ p )
    ⦃ d₁ : {x : elem X} → Decidable (pr₁ (elem p) == x) ⦄
    ⦃ d₂ : {x : elem X} → Decidable (pr₂ (elem p) == x) ⦄
    → ----------------------------------------------------
    ¬ ∃ λ (G : Functor NonemptySet NonemptySet) → ¬ empty ([—]^ X ⊣ G)
  no-right-adjoint X p (G , F⊣G≠𝟘) =
    F⊣G≠𝟘 λ (A : [—]^ X ⊣ G) →
      NoRightAdjoint.finish {X} p A 

  right-adjoint-of-𝟙 :
    Σ λ (G : Functor NonemptySet NonemptySet)
      → [—]^ one ⊣ G
  right-adjoint-of-𝟙 = G Σ., F⊣G
    where F = [—]^ one
          G = Id NonemptySet
          F⊣G : F ⊣ G
          (η ⦃ F⊣G ⦄ at _) x = λ (_ : Lift𝒰 𝟙) → x
          naturality ⦃ η ⦃ F⊣G ⦄ ⦄ _ = refl _
          (ε ⦃ F⊣G ⦄ at _) one→X = one→X (↑type ⋆)
          naturality ⦃ ε ⦃ F⊣G ⦄ ⦄ _ = refl _
          axiom-F ⦃ F⊣G ⦄ = ⟹==
            (right-compose (ε ⦃ F⊣G ⦄) F O left-compose F (η ⦃ F⊣G ⦄))
            (Identity F) $
            fun-ext λ X →
            fun-ext λ f →
            fun-ext λ { (↑type ⋆) → refl (f (↑type ⋆)) }
          axiom-G ⦃ F⊣G ⦄ = ⟹==
            (left-compose G (ε ⦃ F⊣G ⦄) O right-compose (η ⦃ F⊣G ⦄) G)
            (Identity G) $
            fun-ext λ X → fun-ext λ x → refl x
