{-# OPTIONS --type-in-type #-}

module Exp where

open import Data.Nat
open import Data.Bool

data Exp : Set -> Set where
  NatE : ℕ -> Exp ℕ
  BoolE : Bool -> Exp Bool
  IfE : {a : Set} -> Exp Bool -> Exp a -> Exp a -> Exp a
  AddE : Exp ℕ -> Exp ℕ -> Exp ℕ
