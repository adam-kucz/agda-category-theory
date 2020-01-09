module Precedences where

-- Functors (250 - 240)

infix 245 _[_,—] -- Functor.Representable
infix 245 _[—,_] -- Functor.Representable
infixl 240 _o_ -- Functor.Construction

-- Natural Transformations (220 - 210)

infix 215 _⟹_ -- NaturalTransformation.Definition
infix 210 Composition -- NaturalTransformation.Construction

-- Objects (200 - 180)

infixl 190 _×_ -- Construction.Exponential
infixl 180 _×_ -- Construction.Product

-- Morphisms (170 - 160)

infix 170 _at_ -- NaturalTransformation.Definition
infixl 167 _⊠_ -- Construction.Product.Unsafe
infixl 165 _∘[_]_ -- Category.Definition
infixl 165 _∘_ -- Category.Definition
infix 160 _~>_ -- Category.Definition

-- Categories (159 - 151)

infix 159 _ᵒᵖ -- Category.Opposite
infixl 153 _×_ -- Category.Product
