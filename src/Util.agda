{-# OPTIONS --type-in-type #-}

module Util where

open import Relation.Binary.Core 
open import Data.Maybe
open import Data.Bool

cong : {X Y : Set} {a b : X} → (f : X → Y) → a ≡ b → f a ≡ f b
cong f refl = refl

data Tree (A : Set) : Set where
  Leaf : A → Tree A
  Node : Tree A → Tree A → Tree A

isJust : {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing = false

fromJust : {A : Set} → (x : Maybe A) → (isJust x) ≡ true → A
fromJust (just a) refl = a
fromJust nothing ()

_$_ : ∀ {a b} -> (a -> b) -> a -> b
f $ a = f a

infixr 0 _$_