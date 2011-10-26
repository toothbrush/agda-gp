{-# OPTIONS --type-in-type #-}

module Regular where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Coinduction
open import Category.Monad.Partiality

data C : Set where
  U : C
  K : Set -> C
  I : C
  _⊕_ : C -> C -> C
  _⊗_ : C -> C -> C

el : C -> Set -> Set
el U _ = ⊤
el (K a) r = a
el I r = r
el (c1 ⊕ c2) r = el c1 r ⊎ el c2 r
el (c1 ⊗ c2) r = el c1 r × el c2 r

{-
data List_F (a r : Set) : Set where
  nil_f : List_F a r
  cons_f : a → r → List_F a r

list_f' : Set → (Set → Set)
list_f' a = U + K a × I

data Fix (f : Set → Set) : Set where
  fin : f (Fix f) → Fix f
-}

{-
fix-aux : {a b : Set} (k : a → b ⊥) (f : (a → b ⊥) → a → b ⊥) → a → b ⊥
fix-aux k f a with f k a
... | now x = now x
... | later x = later (♯ fix-aux (f k) f a)


Fix : (x : Set → Set) → Set
Fix x = x (Fix x)


list' : Set → Set
list' a = Fix (list_f' a)
 
-}

 