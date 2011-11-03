{-# OPTIONS --type-in-type #-}

module Spine where

open import Data.Nat
open import Data.Maybe
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty
open import Data.BoundedVec using (BoundedVec) renaming (_∷_ to _BV∷_; [] to BV[])
open import Data.Bool

open import Data.Product
open import Data.Unit
open import Data.Sum

open import Relation.Binary.Core public using (_≡_; refl)

open import Util

-- Type Universe
data Type : Set -> Set where
  bool : Type Bool
  nat  : Type ℕ
  list : {a : Set} -> Type a -> Type (List a)

data Type? : Set where
  con : Type?
  rec : Type?

data Typed (a : Set) : Set where
  _:>_ : a -> Type a -> Typed a

infixl 1 _:>_

-- Decode Type in Set
decodeType : {a : Set} -> Type a -> Set
decodeType nat = ℕ
decodeType bool = Bool
decodeType (list a) = List $ decodeType a

-- Type Equality
Type_≡Type_ : {A B : Set} -> Type A -> Type B -> Maybe (A ≡ B)
Type nat ≡Type nat = just refl
Type bool ≡Type bool = just refl
Type (list A) ≡Type (list B) with Type A ≡Type B
... | nothing = nothing
... | just refl = just refl
Type _ ≡Type _ = nothing

-- Spine Type Representation
data Spine : Set -> Set where
  Con : ∀ {a} -> a -> Spine a
  _:<>:_ : ∀ {a b} -> Spine (a -> b) -> Typed a -> Spine b

infixl 0 _:<>:_

-- Decode a spine value
fromSpine : {a : Set} -> Spine a -> a
fromSpine (Con c) = c
fromSpine (f :<>: (x :> _)) = (fromSpine f) x

-- Encode a spine value
toSpine : {a : Set} -> Type a -> a -> Spine a
toSpine nat n  = Con n
toSpine bool b = Con b
toSpine (list a) [] = Con []
toSpine (list a) (_∷_ x xs) = Con _∷_ :<>: (x :> a) :<>: (xs :> list a) 

-- Signatures
data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} → Signature (b → a) → Type? × Type b → Signature a

infixl 0 _·_

datatype : {a : Set} -> Type a -> List⁺ (Signature a)
datatype bool = Sig true ∷ [ Sig false ]
datatype nat  = Sig zero ∷ [ (Sig suc · rec , nat) ]
datatype (list a) = Sig [] ∷ [ (Sig (_∷_) · con , a · rec , (list a)) ]

-- 
True : Spine Bool
True = Con true

zeroo : Spine ℕ
zeroo = Con zero

two : Spine ℕ
two = Con suc :<>: (suc zero :> nat)