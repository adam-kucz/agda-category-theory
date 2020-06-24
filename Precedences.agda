module Precedences where

-- Functors (250 - 240)

infix 245 _[_,—] -- Functor.Representable
infix 245 _[—,_] -- Functor.Representable
infixl 242 _o_ -- Functor.Construction.Definition
infixl 241 _,_ -- Functor.Product

-- Adjunctions (235 - 225)

infix 230 _⊣_ -- Adjunction.Definition
infix 230 _-|_ -- Adjunction.Definition

-- Natural Transformations (220 - 210)

infix 215 _⟹_ -- NaturalTransformation.Definition
infix 212 _×_ -- Monad.Definition
infix 210 Composition -- NaturalTransformation.Construction

-- Objects (200 - 180)

infixl 190 _^_ -- Construction.Exponential
infixl 181 _×_ -- Construction.Simple.Product
infixl 180 _+_ -- Construction.Simple.Coproduct

-- Morphisms (170 - 160)

infix 170 _at_ -- NaturalTransformation.Definition
infixl 167 _⊠_ -- Construction.Product.Unsafe
infixl 165 _∘[_]_ -- Category.Definition
infixl 165 _∘_ -- Category.Definition
infix 160 _~>_ -- Category.Definition

-- Categories (159 - 151)

infix 159 _ᵒᵖ -- Category.Opposite
infixl 153 _×_ -- Category.Product
infix 151 _≅_ -- Isomorphism.Definition
infix 151 _≅-unique_ -- Isomorphism.Definition
infix 151 _≅[_]_ -- Isomorphism.Definition
