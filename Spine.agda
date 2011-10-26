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

data Type : Set -> Set where
  NatR : Type ℕ
  BoolR : Type Bool
  ListR : {a : Set} -> Type a -> Type (List a)
  TreeR : {a : Set} -> Type a -> Type (Tree a)
 
data Typed (a : Set) : Set where
  _:>_ : Type a -> a -> Typed a

data Spine : Set -> Set where
  Con : ∀ {a} -> a -> Spine a
  _:<>:_ : ∀ {a b} -> Spine (a -> b) -> Typed a -> Spine b

data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} -> Signature (b -> a) -> Type b -> Signature a

infixl 0 _·_

datatype : {a : Set} -> Type a -> List (Signature a)
datatype BoolR = Sig false ∷ Sig true ∷ []
datatype NatR  = Sig zero ∷ (Sig suc · NatR) ∷ []
datatype (ListR a) = (Sig []) ∷ (Sig (_∷_) · a · ListR a) ∷ []
datatype (TreeR a) = (Sig Leaf · a) ∷ (Sig Node · TreeR a · TreeR a) ∷ []

fromSpine : {a : Set} -> Spine a -> a
fromSpine (Con c) = c
fromSpine (f :<>: (_ :> x)) = (fromSpine f) x

raw : {a : Set} -> Type a -> Set
raw NatR = ℕ
raw BoolR = Bool
raw (ListR y) = List (raw y)
raw (TreeR y) = Tree (raw y)

tEQ : {A B : Set} -> Type A -> Type B -> Maybe (A ≡ B)
tEQ NatR NatR = just refl
tEQ BoolR BoolR = just refl
tEQ (ListR A) (ListR B) with tEQ A B
... | nothing = nothing
... | just refl = just refl
tEQ (TreeR A) (TreeR B) with tEQ A B
... | nothing = nothing
... | just refl = just refl
tEQ _ _ = nothing