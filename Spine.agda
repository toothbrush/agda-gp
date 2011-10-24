{-# OPTIONS --type-in-type #-}

module Spine where

open import Data.Nat
open import Data.List 
open import Data.Bool
open import Exp

data Type : Set -> Set where
  NatR : Type ℕ
  BoolR : Type Bool
  ListR : {a : Set} -> Type a -> Type (List a)
  ExpR : {a : Set} -> Type a -> Type (Exp a)
 
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
datatype (ExpR BoolR) = (Sig BoolE · BoolR) ∷ (Sig IfE · ExpR BoolR · ExpR BoolR · ExpR BoolR) ∷ []
datatype (ExpR NatR)   = (Sig NatE · NatR) ∷ (Sig AddE · ExpR NatR · ExpR NatR) ∷ (Sig IfE · ExpR BoolR · ExpR NatR · ExpR NatR) ∷ []
datatype (ExpR (ListR y)) = []
datatype (ExpR (ExpR y)) = []

fromSpine : {a : Set} -> Spine a -> a
fromSpine (Con c) = c
fromSpine (f :<>: (_ :> x)) = (fromSpine f) x

{-
toSpine : {a : Set} -> Typed a -> Spine a
toSpine (NatR :> i) = Con i
toSpine (BoolR :> b) = Con b
toSpine (ListR a :> []) = Con []
toSpine (ListR a :> (x ∷ xs)) = (Con (_∷_) :<>: (a :> x)) :<>: (ListR a :> xs)
-}