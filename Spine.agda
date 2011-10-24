{-# OPTIONS --type-in-type #-}

module Spine where

open import Relation.Binary.PropositionalEquality

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool

data List a : Set where
  Nil : List a
  Cons : a -> List a -> List a

data Pair a b : Set where
  pair : a -> b -> Pair a b

data Unit : Set where
  unit : Unit

data _+_ (a : Set) (b : Set) : Set where
  L : a -> a + b
  R : b -> a + b

data _×_ (a : Set) (b : Set) : Set where
  prod : a -> b -> a × b

data SType : Set -> Set where
  SNat : SType Nat
  SBool : SType Bool
  SList : ∀ {a} -> SType a -> SType (List a)
-- Extension of the universe to represent types of LIGD
  SPair : ∀ {a b} -> SType a -> SType b -> SType (Pair a b)
  SSType : ∀ {a} -> SType a -> SType (SType a)
 
data Typed (a : Set) : Set where
  _:>_ : SType a -> a -> Typed a

data Spine : Set -> Set where
  Con : ∀ {a} -> a -> Spine a
  _:<>:_ : ∀ {a b} -> Spine (a -> b) -> Typed a -> Spine b

fromSpine : {a : Set} -> Spine a -> a
fromSpine (Con c) = c
fromSpine (f :<>: (_ :> x)) = (fromSpine f) x

record EP (a : Set) (b : Set) : Set where 
  field  from : (a -> b)
         to   : (b -> a)
    --     iso₁  : ∀ {x} → from (to x) ≡ x
    --     iso₂  : ∀ {x} → to (from x) ≡ x
                                         

data Rep : Set -> Set where -- LIGD Rep
  RUnit : Rep Unit
  RNat : Rep Nat
  RBool : Rep Bool
  RSum : ∀ {a b : Set} -> Rep a -> Rep b -> Rep (a + b)
  RProd : ∀ {a b : Set} -> Rep a -> Rep b -> Rep (a × b)
  RType : ∀ {a b} -> EP a b -> Rep b -> Rep a
 
data TypeMap : {a b : Set} -> Rep a -> SType b -> Set where -- TypeMap (RType a) (SType b) where
  ProofUnit : TypeMap RUnit SBool
  ProofNat : TypeMap RNat SNat
  ProofBool : TypeMap RBool SBool
  ProofSum : ∀ {a b c d} -> TypeMap a b -> TypeMap c d -> TypeMap (RSum a c) (SPair SBool (SPair (SSType b) (SSType d)))



repToSType : {a b : Set} -> EP (Rep a) (SType b)
repToSType RUnit = {!!}
repToSType RNat = SNat
repToSType RBool = SBool
repToSType (RSum ra rb)  = {!!} -- SSum (repToSType ra) (repToSType rb)
repToSType (RProd ra rb) = {!!} -- SProd (repToSType ra) (repToSType rb)
repToSType (RType ep rb) = {!  rb!}

toSpine : {a : Set} -> Typed a -> Spine a
toSpine (SNat :> i) = Con i
toSpine (SBool :> b) = Con b
toSpine (SList a :> Nil) = Con Nil
toSpine (SList a :> (Cons x xs)) = (Con Cons :<>: (a :> x)) :<>: (SList a :> xs)
toSpine (SPair a b :> (pair x y)) = (Con pair :<>: (a :> x)) :<>: (b :> y)
toSpine (SSType y :> y') = Con y' 
--toSpine ((SSum sa _) :> (L a)) = Con L :<>: (sa :> a)
--toSpine ((SSum _ sb) :> (R b)) = Con R :<>: (sb :> b)
--toSpine ((SProd sa sb) :> (prod a b)) = (Con prod :<>: (sa :> a)) :<>: (sb :> b)

lToS : {a : Set} -> Rep a -> a -> Spine a
lToS rep a = toSpine (repToSType rep :> a)