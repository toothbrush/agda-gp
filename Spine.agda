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

data μ_ (c : C) : Set where
  <_> : el c  (μ c) → μ c

infix 1 <_>

--replace f with 
f : {a : Set} -> Type a -> C 
f NatR = U ⊕ I
f BoolR = U ⊕ U
f (ListR {a} y) = U ⊕ (K a ⊗ I)

--F {a : Set} -> t : Type a -> EP a (el (f t))  

Nat = μ (f NatR)

ListC : {a : Set} -> Type a -> Set
ListC a = μ (f (ListR a)) 

nil : {A : Set}{a : Type A} -> ListC a
nil = < inj₁ tt >

cons : {A : Set}{a : Type A} -> A -> ListC a -> ListC a
cons x xs = < inj₂ (x , xs) >  

from : {A : Set} -> (ta : Type A) -> (t : A) -> μ (f ta)
from NatR zero = < inj₁ tt >
from NatR (suc n) = < inj₂ (from NatR n) >
from BoolR true = < inj₁ tt >
from BoolR false = < inj₂ tt >
from (ListR y) [] = < inj₁ tt >
from (ListR y) (x ∷ xs) = < inj₂ (x , from (ListR y) xs) >

to : {A : Set} -> (ta : Type A) -> μ (f ta) -> A 
to NatR < inj₁ tt > = zero
to NatR < inj₂ n > = suc (to NatR n)
to BoolR < inj₁ tt > = true
to BoolR < inj₂ tt > = false
to (ListR y) < inj₁ tt > = []
to (ListR y) < inj₂ (x , xs) > = x ∷ to (ListR y) xs