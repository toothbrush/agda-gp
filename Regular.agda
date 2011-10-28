{-# OPTIONS --type-in-type #-}

module Regular where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Coinduction
open import Category.Monad.Partiality

data C : Set where
  U : C
  K : Set → C
  I : C
  _⊕_ : C → C → C
  _⊗_ : C → C → C

el : C → Set → Set
el U _ = ⊤
el (K a) _ = a
el I r = r
el (c1 ⊕ c2) r = el c1 r ⊎ el c2 r
el (c1 ⊗ c2) r = el c1 r × el c2 r
