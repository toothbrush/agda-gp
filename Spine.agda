{-# OPTIONS --type-in-type #-}

module Spine where

open import Data.Nat
open import Data.List 
open import Data.Bool
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Relation.Binary.Core public using (_≡_; refl)
open import Regular

data Type : Set -> Set where
  NatR : Type ℕ
  BoolR : Type Bool
  ListR : {a : Set} -> Type a -> Type (List a)
 
data Typed (a : Set) : Set where
  _:>_ : Type a -> a -> Typed a

data Spine : Set -> Set where
  Con : ∀ {a} -> a -> Spine a
  _:<>:_ : ∀ {a b} -> Spine (a -> b) -> Typed a -> Spine b

data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} -> Signature (b -> a) -> Type b -> Signature a

infixl 0 _·_

allNats : ℕ -> List (Signature ℕ)
allNats x = Sig x ∷ allNats (suc x)

datatype : {a : Set} -> Type a -> List (Signature a)
datatype BoolR = Sig false ∷ Sig true ∷ []
datatype NatR  = allNats zero
datatype (ListR a) = (Sig (_∷_) · a · ListR a) ∷ []

fromSpine : {a : Set} -> Spine a -> a
fromSpine (Con c) = c
fromSpine (f :<>: (_ :> x)) = (fromSpine f) x

raw : {a : Set} -> Type a -> Set
raw NatR = ℕ
raw BoolR = Bool
raw (ListR y) = List (raw y)

--replace f with 
goal : {a : Set} -> t : Type a -> C 
f : {a : Set} -> Type a -> C 
f NatR = U ⊕ I
f BoolR = U ⊕ U
f (ListR y) = U ⊕ (K (raw y) ⊗ I)

--F {a : Set} -> t : Type a -> EP a (el (f t))  

from : {A : Set} -> (ta : Type A) -> (t : A) -> (el (f ta) )
from NatR zero = inj₁ ⊤
from NatR (suc x) = inj₂ (from NatR x)
from BoolR true = inj₁ ⊤
from BoolR false = inj₂ ⊤
--from ListR [] 

proof : (t : Type a) -> a = fix (el (f t))