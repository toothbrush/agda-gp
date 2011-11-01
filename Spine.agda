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

-- Type Universe
--data Type₀ : Set → Set where
--  bool : Type₀ Bool
--  nat : Type₀ ℕ

--data Type₁ : (Set → Set) → Set → Set where
--  list : {a : Set} → Type₀ a → Type₁ List a
--  tree : {a : Set} → Type₀ a → Type₁ Tree a

--data Type : Set → Set where
--  t₀ : {A : Set} → Type₀ A → Type A
--  t₁ : {F : Set → Set} {A : Set} → Type₁ F A → Type (F A)

data Type? : Set where
  con : Type?
  rec : Type?

data Type : Set -> Set where
  bool : Type Bool
  nat  : Type ℕ
  list : {a : Set} -> Type a -> Type (List a)
 
data Typed (a : Set) : Set where
  _:>_ : a -> Type a -> Typed a

infixl 1 _:>_

-- Decode Type to actual Types
--decodeType₀ : {A : Set} → Type₀ A → Set
--decodeType₀ bool = Bool
--decodeType₀ nat = ℕ

--decodeType₁ : {F : Set → Set} {A : Set} → Type₁ F A → Set
--decodeType₁ (list a) = List (decodeType₀ a)
--decodeType₁ (tree a) = Tree (decodeType₀ a)

--decodeType : {A : Set} → Type A → Set
--decodeType (t₀ t) = decodeType₀ t
--decodeType (t₁ t) = decodeType₁ t

decodeType : {a : Set} -> Type a -> Set
decodeType nat = ℕ
decodeType bool = Bool
decodeType (list a) = List $ decodeType a

-- Type Equality
Type_≡Type_ : {A B : Set} -> Type A -> Type B -> Maybe (A ≡ B)
Type nat ≡Type nat = just refl
Type bool ≡Type bool = just refl
Type (list A) ≡Type (list B) with Type A ≡Type B
... | nothing = nothing
... | just refl = just refl
Type _ ≡Type _ = nothing

-- Spine Type Representation
data Spine : Set -> Set where
  Con : ∀ {a} -> a -> Spine a
  _:<>:_ : ∀ {a b} -> Spine (a -> b) -> Typed a -> Spine b

infixl 0 _:<>:_

-- Decode a spine value
fromSpine : {a : Set} -> Spine a -> a
fromSpine (Con c) = c
fromSpine (f :<>: (x :> _)) = (fromSpine f) x

-- Encode a spine value
--toSpine : {a : Set} -> Type a -> a -> Spine a
--toSpine NatR n  = Con n
--toSpine BoolR b = Con b
--toSpine (ListR a) [] = Con []
--toSpine (ListR a) (x ∷ xs) = Con _∷_ :<>: (x :> a) :<>: (xs :> ListR a) 
--toSpine (TreeR a) (Leaf x) = Con Leaf :<>: (x :> a)
--toSpine (TreeR a) (Node l r) = Con Node :<>: (l :> TreeR a) :<>: (r :> TreeR a)

-- Signatures
data Signature a : Set where
  Sig : a -> Signature a
--  _·_ : {b : Set} -> Signature (b -> a) -> Type b -> Signature a
  _·_ : {b : Set} → Signature (b → a) → Type? × Type b → Signature a

infixl 0 _·_

-- Convert Type to a List of Signatures
--datatype₁ : {F : Set → Set} {A : Set} → Type₁ F A → List (Signature (F A))
--datatype₁ (list a) = Sig [] ∷ (Sig _∷_ · con , t₀ a · rec , t₁ (list a)) ∷ []
--datatype₁ (tree a) = (Sig Leaf · con , t₀ a) ∷ (Sig Node · rec , t₁ (tree a) · rec , t₁ (tree a)) ∷ []

--datatype : {a : Set} → Type a → List (Signature a)
--datatype (t₀ bool) = Sig false ∷ Sig true ∷ []
--datatype (t₀ nat) = Sig zero ∷ (Sig suc · rec , t₀ nat) ∷ []
--datatype (t₁ t) = datatype₁ t


data ListNZ (A : Set) : Set where
  El  : (x : A) -> ListNZ A
  _∷_ : (x : A) (xs : ListNZ A) → ListNZ A
  

datatype : {a : Set} -> Type a -> ListNZ (Signature a)
datatype bool = Sig false ∷ El (Sig true)
datatype nat  = Sig zero ∷ El (Sig suc · rec , nat)
datatype (list a) = Sig [] ∷ El (Sig (_∷_) · con , a · rec , (list a))