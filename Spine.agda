{-# OPTIONS --type-in-type #-}

module Spine where

open import Data.Nat
open import Data.Maybe
open import Data.List 
open import Data.Bool

open import Data.Product
open import Data.Unit
open import Data.Sum

open import Relation.Binary.Core public using (_≡_; refl)

open import Util

-- Type Universe
data Type : Set -> Set where
  NatR : Type ℕ
  BoolR : Type Bool
  ListR : {a : Set} -> Type a -> Type (List a)
  TreeR : {a : Set} -> Type a -> Type (Tree a)
 
data Typed (a : Set) : Set where
  _:>_ : a -> Type a -> Typed a

infixl 1 _:>_

-- Decode Type to actual Types
decodeType : {a : Set} -> Type a -> Set
decodeType NatR = ℕ
decodeType BoolR = Bool
decodeType (ListR y) = List $ decodeType y
decodeType (TreeR y) = Tree $ decodeType y

-- Type Equality
Type_≡Type_ : {A B : Set} -> Type A -> Type B -> Maybe (A ≡ B)
Type NatR ≡Type NatR = just refl
Type BoolR ≡Type BoolR = just refl
Type (ListR A) ≡Type (ListR B) with Type A ≡Type B
... | nothing = nothing
... | just refl = just refl
Type (TreeR A)≡Type (TreeR B) with Type A ≡Type B
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
toSpine NatR n  = Con n
toSpine BoolR b = Con b
toSpine (ListR a) [] = Con []
toSpine (ListR a) (x ∷ xs) = Con _∷_ :<>: (x :> a) :<>: (xs :> ListR a) 
toSpine (TreeR a) (Leaf x) = Con Leaf :<>: (x :> a)
toSpine (TreeR a) (Node l r) = Con Node :<>: (l :> TreeR a) :<>: (r :> TreeR a)

-- Signatures
data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} -> Signature (b -> a) -> Type b -> Signature a

infixl 0 _·_

-- Convert Type to a List of Signatures
datatype : {a : Set} -> Type a -> List (Signature a)
datatype BoolR = Sig false ∷ Sig true ∷ []
datatype NatR  = Sig zero ∷ (Sig suc · NatR) ∷ []
datatype (ListR a) = (Sig []) ∷ (Sig (_∷_) · a · ListR a) ∷ []
datatype (TreeR a) = (Sig Leaf · a) ∷ (Sig Node · TreeR a · TreeR a) ∷ []


