{-# OPTIONS --type-in-type #-}

module Spine where

open import Data.Nat
open import Data.Maybe
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty
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
interpretSTRep : {a : Set} -> Type a -> Set
interpretSTRep nat = ℕ
interpretSTRep bool = Bool
interpretSTRep (list a) = List $ interpretSTRep a

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
toSpine nat zero  = Con zero
toSpine nat (suc n) = Con suc :<>: (n :> nat)
toSpine bool b = Con b
toSpine (list a) [] = Con []
toSpine (list a) (_∷_ x xs) = Con _∷_ :<>: (x :> a) :<>: (xs :> list a) 

-- Signatures
data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} → Signature (b → a) → Type? × Type b → Signature a

infixl 0 _·_

sigList : {n : ℕ}{a : Set} -> Type a -> List⁺ (Signature a)
sigList bool = Sig true ∷ [ Sig false ]
sigList nat  = Sig zero ∷ [ (Sig suc · rec , nat) ]
sigList (list a) = Sig [] ∷ [ (Sig (_∷_) · con , a · rec , (list a)) ]
