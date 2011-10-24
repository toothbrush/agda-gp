{-# OPTIONS --type-in-type #-}

module Regular where

open import Coinduction
open import Category.Monad.Partiality

-- Sum
data _+_ (A B : Set → Set) (r : Set) : Set where 
  inl : A r → (A + B) r
  inr : B r → (A + B) r

infixr 5 _+_

-- Product
data _×_ (A B : Set → Set) (r : Set) : Set where
  _,_ : A r → B r → (A × B) r

infixr 6 _×_
infixr 6 _,_

data U (r : Set) : Set where
  u : U r

data I (r : Set) : Set where
  i : r → I r

data K (a r : Set) : Set where
  k : a → K a r

data List_F (a r : Set) : Set where
  nil_f : List_F a r
  cons_f : a → r → List_F a r

list_f' : Set → (Set → Set)
list_f' a = U + K a × I

data Fix (f : Set → Set) : Set where
  fin : f (Fix f) → Fix f


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

 