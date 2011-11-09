{-# OPTIONS --type-in-type #-}

module Util where

data Tree (A : Set) : Set where
  Leaf : A → Tree A
  Node : Tree A → Tree A → Tree A

_$_ : ∀ {a b} -> (a -> b) -> a -> b
f $ a = f a

infixr 0 _$_
