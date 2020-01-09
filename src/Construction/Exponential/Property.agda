{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Category
open import Construction.Product
import Construction.Exponential.Definition as ExpDef

module Construction.Exponential.Property where

open import Proposition.Identity renaming (Idₚ to Id) hiding (refl) 
open import Proposition.Sum
open import Construction.Product.Unsafe
open import Axiom.UniqueChoice

HasExponentials : (ℂ : Category 𝒲 𝒯) ⦃ _ : HasProducts ℂ ⦄ → 𝒲 ⊔ 𝒯 ˙
HasExponentials ℂ = ∀ {A B : obj } → Exponential A B
  where instance _ = ℂ
        open ExpDef

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
        app-cur f with get-mor f
        app-cur f | _ , (p , _) = p
        
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
            〉 _==_ 〉 app ∘ 〈 id (Y ^ X) ∘ π₁ , id X ∘ π₂ 〉
              :by: Id.refl (app ∘ id (Y ^ X) ⊠ id X)
            〉 _==_ 〉 app ∘ 〈 π₁ , id X ∘ π₂ 〉
              :by: ap (λ — → app ∘ 〈 — , id X ∘ π₂ 〉) $ left-unit π₁
            〉 _==_ 〉 app ∘ 〈 π₁ , π₂ 〉
              :by: ap (λ — → app ∘ 〈 π₁ , — 〉) $ left-unit π₂
            〉 _==_ 〉 app ∘ id (Y ^ X × X)
              :by: ap (app ∘_) 〈π₁,π₂〉==id
            〉 _==_ 〉 app :by: right-unit app
          qed)

    open WithFixedExponential hiding (get-mor) public
    
    cur-compose-app :
      {X Y Z W : obj}
      (g : Z ~> W)
      (f : Y ~> Z)
      ⦃ E : Exponential X Y ⦄
      ⦃ E' : Exponential X Z ⦄
      ⦃ E'' : Exponential X W ⦄
      → --------------------------------------------------
      cur (g ∘ f ∘ app) == cur (g ∘ app) ∘ cur (f ∘ app)
    cur-compose-app {X} g f = sym $
      curry-mor-uniq (g ∘ f ∘ app) (cur (g ∘ app) ∘ cur (f ∘ app)) (
        proof app ∘ (cur (g ∘ app) ∘ cur (f ∘ app)) ⊠ id X
          〉 _==_ 〉 app ∘ (cur (g ∘ app) ∘ cur (f ∘ app)) ⊠ (id X ∘ id X)
            :by: ap (λ — → app ∘ (cur (g ∘ app) ∘ cur (f ∘ app)) ⊠ —) $
                 sym $ left-unit (id X)
          〉 _==_ 〉 app ∘ (cur (g ∘ app) ⊠ id X ∘ cur (f ∘ app) ⊠ id X)
            :by: ap (app ∘_) $ ⊠-compose _ _ _ _
          〉 _==_ 〉 app ∘ cur (g ∘ app) ⊠ id X ∘ cur (f ∘ app) ⊠ id X
            :by: assoc app _ _
          〉 _==_ 〉 g ∘ app ∘ cur (f ∘ app) ⊠ id X
            :by: ap (_∘ cur (f ∘ app) ⊠ id X) $ app-cur (g ∘ app)
          〉 _==_ 〉 g ∘ (app ∘ cur (f ∘ app) ⊠ id X)
            :by: sym $ assoc g _ _
          〉 _==_ 〉 g ∘ (f ∘ app)
            :by: ap (g ∘_) $ app-cur (f ∘ app)
          〉 _==_ 〉 g ∘ f ∘ app
            :by: assoc g f app
        qed)
    
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
            〉 _==_ 〉 cur2-app2
              :by: curry-mor-uniq app2 (cur2-app1 ∘ cur1-app2) (
                proof app2 ∘ (cur2-app1 ∘ cur1-app2) ⊠ id X
                  〉 _==_ 〉 app2 ∘ (cur2-app1 ∘ cur1-app2) ⊠ (id X ∘ id X)
                    :by: ap (λ — → app2 ∘ (cur2-app1 ∘ cur1-app2) ⊠ —) $
                         sym $
                         right-unit (id X)
                  〉 _==_ 〉 app2 ∘ (cur2-app1 ⊠ id X ∘ cur1-app2 ⊠ id X)
                    :by: ap (app2 ∘_) $ ⊠-compose _ _ _ _
                  〉 _==_ 〉 app2 ∘ cur2-app1 ⊠ id X ∘ cur1-app2 ⊠ id X
                    :by: assoc app2 _ _
                  〉 _==_ 〉 app1 ∘ cur1-app2 ⊠ id X
                    :by: ap (_∘ cur1-app2 ⊠ id X) $ app-cur app1
                  〉 _==_ 〉 app2 :by: app-cur app2
                qed)
            〉 _==_ 〉 id exp2 :by: sym $ curry-mor-uniq app2 (id exp2) (
              proof app2 ∘ id exp2 ⊠ id X
                〉 _==_ 〉 app2 ∘ id (exp2 × X) :by: ap (app2 ∘_) $ ⊠-id exp2 X
                〉 _==_ 〉 app2                 :by: right-unit app2
              qed)
          qed) ,
          (proof cur1-app2 ∘ cur2-app1
            〉 _==_ 〉 cur1-app1
              :by: curry-mor-uniq app1 (cur1-app2 ∘ cur2-app1) (
                proof app1 ∘ (cur1-app2 ∘ cur2-app1) ⊠ id X
                  〉 _==_ 〉 app1 ∘ (cur1-app2 ∘ cur2-app1) ⊠ (id X ∘ id X)
                    :by: ap (λ — → app1 ∘ (cur1-app2 ∘ cur2-app1) ⊠ —) $
                         sym $
                         right-unit (id X)
                  〉 _==_ 〉 app1 ∘ (cur1-app2 ⊠ id X ∘ cur2-app1 ⊠ id X)
                    :by: ap (app1 ∘_) $ ⊠-compose _ _ _ _
                  〉 _==_ 〉 app1 ∘ cur1-app2 ⊠ id X ∘ cur2-app1 ⊠ id X
                    :by: assoc app1 _ _
                  〉 _==_ 〉 app2 ∘ cur2-app1 ⊠ id X
                    :by: ap (_∘ cur2-app1 ⊠ id X) $ app-cur app2
                  〉 _==_ 〉 app1 :by: app-cur app1
                qed)
            〉 _==_ 〉 id exp1 :by: sym $ curry-mor-uniq app1 (id exp1) (
              proof app1 ∘ id exp1 ⊠ id X
                〉 _==_ 〉 app1 ∘ id (exp1 × X) :by: ap (app1 ∘_) $ ⊠-id exp1 X
                〉 _==_ 〉 app1                 :by: right-unit app1
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
