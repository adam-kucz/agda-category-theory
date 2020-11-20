{-# OPTIONS --exact-split --prop #-}
module Construction.Exponential.Property where

open import PropUniverses
open import Proposition.Sum
open import Proof

open import Category
open import Morphism.Iso
open import Construction.Product
  using (HasProducts; _×_; _⊠_; 〈_,_〉; π₁; π₂; 〈π₁,π₂〉==id; ⊠-compose; ⊠-id)
import Construction.Exponential.Definition as ExpDef

open import Axiom.UniqueChoice

HasExponentials : (ℂ : Category 𝒲 𝒯) ⦃ _ : HasProducts ℂ ⦄ → 𝒲 ⊔ 𝒯 ˙
HasExponentials ℂ = ∀ {A B : obj } → Exponential A B
  where instance _ = ℂ
        open ExpDef

open import Construction.Terminal

record CartesianClosed (ℂ : Category 𝒲 𝒯) : 𝒲 ⊔ 𝒯 ˙ where
  private
    instance _ = ℂ
  field
    ⦃ terminal ⦄ : Terminal
    ⦃ products ⦄ : HasProducts ℂ
    ⦃ exponents ⦄ : HasExponentials ℂ

open import Proof
    
private
  module WithFixedCategory
    ⦃ ℂ : Category 𝒰 𝒱 ⦄
    ⦃ P : HasProducts ℂ ⦄
    where

    open ExpDef ⦃ ℂ ⦄ ⦃ P ⦄
  
    private
      module WithFixedExponential
        {X Y : obj}
        ⦃ E : Exponential X Y ⦄
        where

        get-mor :
          {Z : obj}
          (f : Z × X ~> Y)
          → ------------------
          Σₚ λ (g : Z ~> Y ^ X) → app ∘ (g ⊠ id X) == f ∧
            ∀ (g' : Z ~> Y ^ X) (p : app ∘ (g' ⊠ id X) == f) → g' == g
        get-mor {Z = Z} f = !choice (IsExponential.curry exp-def Z f)
    
        app-cur :
          {Z : obj}
          (f : Z × X ~> Y)
          → ----------------------------------------------------------
          app ∘ (cur f ⊠ id X) == f
        app-cur f = left $ prop (get-mor f)
        
        curry-mor-uniq :
          {Z : obj}
          (f : Z × X ~> Y)
          → ----------------------------------------------------------
          ∀ (h : Z ~> Y ^ X) (p : app ∘ (h ⊠ id X) == f) → h == cur f
        curry-mor-uniq f with get-mor f
        curry-mor-uniq f | _ , (_ , uniq) = uniq
        
        cur-app==id : cur app == id (Y ^ X)
        cur-app==id = sym $ curry-mor-uniq app (id (Y ^ X)) (
          proof app ∘ id (Y ^ X) ⊠ id X
            === app ∘ 〈 id (Y ^ X) ∘ π₁ , id X ∘ π₂ 〉
              :by: Id.refl (app ∘ id (Y ^ X) ⊠ id X)
            === app ∘ 〈 π₁ , id X ∘ π₂ 〉
              :by: ap (λ — → app ∘ 〈 — , id X ∘ π₂ 〉) $ left-unit π₁
            === app ∘ 〈 π₁ , π₂ 〉
              :by: ap (λ — → app ∘ 〈 π₁ , — 〉) $ left-unit π₂
            === app ∘ id (Y ^ X × X)
              :by: ap (app ∘_) 〈π₁,π₂〉==id
            === app :by: right-unit app
          qed)

    open WithFixedExponential hiding (get-mor) public
    
    cur-compose-app :
      {X Y Z W : obj}
      (g : Z ~> W)
      (f : Y ~> Z)
      ⦃ E : Exponential X Y ⦄
      ⦃ E' : Exponential X Z ⦄
      ⦃ E″ : Exponential X W ⦄
      → --------------------------------------------------
      cur (g ∘ f ∘ app) == cur (g ∘ app) ∘ cur (f ∘ app)
    cur-compose-app {X}{Y}{Z}{W} g f ⦃ E ⦄ ⦃ E' ⦄ ⦃ E″ ⦄ = sym $
      curry-mor-uniq (g ∘ f ∘ app→Y) (g' ∘ f') (
        proof app→W ∘ (g' ∘ f') ⊠ id X
          === app→W ∘ (g' ∘ f') ⊠ (id X ∘ id X)
            :by: ap (λ — → app→W ∘ (g' ∘ f') ⊠ —) $
                 sym $ left-unit (id X)
          === app→W ∘ (g' ⊠ id X ∘ f' ⊠ id X)
            :by: ap (app→W ∘_) $ ⊠-compose _ _ _ _
          === app→W ∘ g' ⊠ id X ∘ f' ⊠ id X :by: assoc app→W _ _
          === g ∘ app→Z ∘ f' ⊠ id X
            :by: ap (_∘ f' ⊠ id X) $ app-cur ⦃ E″ ⦄ (g ∘ app→Z)
          === g ∘ (app→Z ∘ f' ⊠ id X)       :by: sym $ assoc g app→Z _
          === g ∘ (f ∘ app→Y)
            :by: ap (g ∘_) $ app-cur ⦃ E' ⦄ (f ∘ app→Y)
          === g ∘ f ∘ app→Y                 :by: assoc g f app→Y
        qed)
        where app→Y = app ⦃ E ⦄; app→Z = app ⦃ E' ⦄; app→W = app ⦃ E″ ⦄
              cur→Y^X : ∀{A : obj}(f : A × X ~> Y) → A ~> Y ^ X
              cur→Y^X = cur
              cur→Z^X : ∀{A : obj}(f : A × X ~> Z) → A ~> Z ^ X
              cur→Z^X = cur
              cur→W^X : ∀{A : obj}(f : A × X ~> W) → A ~> W ^ X
              cur→W^X = cur
              f' = cur→Z^X (f ∘ app→Y)
              g' = cur→W^X (g ∘ app→Z)
    
    open import Logic
    
    exps-unique-upto-unique-iso :
      {X Y : obj}
      (E E' : Exponential X Y)
      → ----------------------------
      ∃! λ (f : (Y ^ X) ⦃ E ⦄ ~> (Y ^ X) ⦃ E' ⦄) →
        iso f ∧
        app ⦃ r = E' ⦄ ∘ f ⊠ id X == app ⦃ r = E ⦄
    exps-unique-upto-unique-iso {X = X} {Y} E E' =
      cur2-app1 ,
      (cur1-app2 ,
        ((proof cur2-app1 ∘ cur1-app2
            === cur2-app2
              :by: curry-mor-uniq app2 (cur2-app1 ∘ cur1-app2) (
                proof app2 ∘ (cur2-app1 ∘ cur1-app2) ⊠ id X
                  === app2 ∘ (cur2-app1 ∘ cur1-app2) ⊠ (id X ∘ id X)
                    :by: ap (λ — → app2 ∘ (cur2-app1 ∘ cur1-app2) ⊠ —) $
                         sym $
                         right-unit (id X)
                  === app2 ∘ (cur2-app1 ⊠ id X ∘ cur1-app2 ⊠ id X)
                    :by: ap (app2 ∘_) $ ⊠-compose _ _ _ _
                  === app2 ∘ cur2-app1 ⊠ id X ∘ cur1-app2 ⊠ id X
                    :by: assoc app2 _ _
                  === app1 ∘ cur1-app2 ⊠ id X
                    :by: ap (_∘ cur1-app2 ⊠ id X) $ app-cur ⦃ E' ⦄ app1
                  === app2 :by: app-cur app2
                qed)
            === id exp2 :by: sym $ curry-mor-uniq app2 (id exp2) (
              proof app2 ∘ id exp2 ⊠ id X
                === app2 ∘ id (exp2 × X) :by: ap (app2 ∘_) $ ⊠-id exp2 X
                === app2                 :by: right-unit app2
              qed)
          qed) ,
          (proof cur1-app2 ∘ cur2-app1
            === cur1-app1
              :by: curry-mor-uniq app1 (cur1-app2 ∘ cur2-app1) (
                proof app1 ∘ (cur1-app2 ∘ cur2-app1) ⊠ id X
                  === app1 ∘ (cur1-app2 ∘ cur2-app1) ⊠ (id X ∘ id X)
                    :by: ap (λ — → app1 ∘ (cur1-app2 ∘ cur2-app1) ⊠ —) $
                         sym $ right-unit (id X)
                  === app1 ∘ (cur1-app2 ⊠ id X ∘ cur2-app1 ⊠ id X)
                    :by: ap (app1 ∘_) $ ⊠-compose _ _ _ _
                  === app1 ∘ cur1-app2 ⊠ id X ∘ cur2-app1 ⊠ id X
                    :by: assoc app1 _ _
                  === app2 ∘ cur2-app1 ⊠ id X
                    :by: ap (_∘ cur2-app1 ⊠ id X) $ app-cur app2
                  === app1 :by: app-cur ⦃ E' ⦄ app1
                qed)
            === id exp1 :by: sym $ curry-mor-uniq app1 (id exp1) (
              proof app1 ∘ id exp1 ⊠ id X
                === app1 ∘ id (exp1 × X) :by: ap (app1 ∘_) $ ⊠-id exp1 X
                === app1                 :by: right-unit app1
              qed)
          qed)) ,
       app-cur app1 ,
       λ { f' (_ , p) → curry-mor-uniq app1 f' p})
      where instance _ = E; _ = E'
            exp1 = (Y ^ X) ⦃ E ⦄
            exp2 = (Y ^ X) ⦃ E' ⦄
            app1 = app ⦃ r = E ⦄
            app2 = app ⦃ r = E' ⦄
            cur1-app1 : exp1 ~> exp1
            cur1-app1 = cur ⦃ E ⦄ app1
            cur2-app1 : exp1 ~> exp2
            cur2-app1 = cur ⦃ E' ⦄ app1 
            cur1-app2 : exp2 ~> exp1
            cur1-app2 = cur ⦃ E ⦄ app2 
            cur2-app2 : exp2 ~> exp2
            cur2-app2 = cur ⦃ E' ⦄ app2

open WithFixedCategory public
