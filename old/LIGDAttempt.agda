{-# OPTIONS --type-in-type #-}

module JustinTest where

open import Function
-- open import Data.List

data Bool : Set where
  true : Bool
  false : Bool

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Exp : Set -> Set where
  IntE : Nat -> Exp Nat
  BoolE : Bool -> Exp Bool
  IfE : {a : Set} -> Exp Bool -> Exp a -> Exp a -> Exp a
  AddE : Exp Nat -> Exp Nat -> Exp Nat

data Type : Set → Set₁ where
  NatR    : Type Nat
  BoolR   : Type Bool
  ListR   : {A : Set} → Type A → Type (List A)
  ExpR    : {A : Set} -> Type A -> Type (Exp A)

data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} -> Signature (b -> a) -> Type b -> Signature a

infixl 0 _·_

data Unit : Set where
  tt : Unit

data Sum a b : Set where
  L : a -> Sum a b
  R : b -> Sum a b

data Prod a b : Set where
  prod : a -> b -> Prod a b

data Bottom : Set where

data EQ {A : Set} (x : A) : A -> Set where
  refl : EQ x x

record EP a b : Set where
  field
    from : a -> b
    to   : b -> a
--    proof₁ : {x : b} -> EQ (from (to x)) x
--    proof₂ : {x : a} -> EQ (to (from x)) x

data Rep : Set → Set where
  RUnit     : Rep Unit
  RBool     : Rep Bool
  RNat      : Rep Nat
  RSum      : {A B : Set} → Rep A → Rep B → Rep (Sum A B)
  RProd     : {A B : Set} → Rep A → Rep B → Rep (Prod A B)
  RType     : {A B : Set} → EP A B → Rep B → Rep A

ListS : Set -> Set
ListS A = Sum Unit (Prod A (List A))

fromList : ∀ {A} → List A → ListS A
fromList Nil          = L tt
fromList (Cons x xs)  = R (prod x xs)

toList : ∀ {A} → ListS A → List A
toList (L unit)        = Nil
toList (R (prod x xs))  = Cons x xs

listEq₁ : {B : Set} {b : ListS B} -> EQ (fromList (toList b)) b
listEq₁ {b = L tt} = refl
listEq₁ {b = R (prod x xs)} = refl

listEq₂ : {A : Set} {a : List A} -> EQ (toList (fromList a)) a
listEq₂ {a = Nil} = refl
listEq₂ {a = Cons x xs} = refl

listEP : {a : Set} -> EP (List a) (ListS a)
listEP = record {from = fromList; to = toList} --; proof₁ = listEq₁; proof₂ = listEq₂}

rList : ∀ {A} → Rep A → Rep (List A)
rList ra = RType listEP (RSum RUnit (RProd ra (rList ra)))

allNats : Nat -> List (Signature Nat)
allNats x = Cons (Sig x) (allNats (suc x))

datatype : {a : Set} -> Type a -> List (Signature a)
datatype BoolR = Cons (Sig false) (Cons (Sig true) Nil)
datatype NatR  = allNats zero
datatype (ListR a) = Cons (Sig Nil) (Cons (Sig Cons · a · ListR a) Nil)
datatype (ExpR BoolR) = Cons (Sig BoolE · BoolR) (Cons (Sig IfE · ExpR BoolR · ExpR BoolR · ExpR BoolR) Nil)
datatype (ExpR NatR)   = Cons (Sig IntE · NatR) (Cons (Sig AddE · ExpR NatR · ExpR NatR) (Cons (Sig IfE · ExpR BoolR · ExpR NatR · ExpR NatR) Nil))
datatype (ExpR (ListR y)) = Nil
datatype (ExpR (ExpR y)) = Nil

interpretSpine : {a : Set} -> Type a -> Set
interpretSpine NatR = Nat
interpretSpine BoolR = Bool
interpretSpine (ListR y) = List (interpretSpine y)
interpretSpine (ExpR y) = Exp (interpretSpine y)

makeProd : {a : Set} -> Signature a -> Set
makeProd (Sig _ · b) = interpretSpine b
makeProd (Sig _) = Unit
makeProd (c · b) = Prod (makeProd c) (interpretSpine b)

makeSum : {a : Set} -> List (Signature a) -> Set
makeSum Nil = Unit -- Undefined Case
makeSum (Cons sig Nil) = makeProd sig
makeSum (Cons sig rest) = Sum (makeProd sig) (makeSum rest)

giveEPType : {a : Set} -> Type a -> Set
giveEPType = makeSum ∘ datatype


makeEP : {a : Set} -> (b : Type a) -> EP a (giveEPType b)
makeEP t = ?



mutual 
       makeProdRep : {a : Set} -> (b : Signature a) -> Rep (makeProd b)
       makeProdRep (Sig _ · NatR) = RNat
       makeProdRep (Sig _ · BoolR) = RBool
       makeProdRep (Sig _ · (ListR y)) = RType (makeEP (ListR y)) (makeRep (ListR y))
       makeProdRep (Sig _ · (ExpR y)) = ?
       makeProdRep (Sig _) = RUnit
       makeProdRep (c · d) = RProd (makeProdRep c) (makeRep d)
       
       makeSumRep : {a : Set} -> (b : List (Signature a)) -> Rep (makeSum b)
       makeSumRep Nil = RUnit -- BAD
       makeSumRep (Cons sig Nil) = makeProdRep sig
       makeSumRep (Cons s r) = {!!} -- RSum (makeProdRep s) (makeSumRep r)

       makeRep : {a : Set} -> (b : Type a) -> Rep (giveEPType b)
       makeRep = makeSumRep ∘ datatype
  

{-
convBase : {a : Set} -> Type a -> Rep a
convBase BoolR = RBool
convBase (ListR a) = rList (convBase a)

aconv : {a : Set} -> Signature a -> Rep a
aconv (Sig _ · b) = {!!} 
aconv (Sig _) = {!!} --convBase b
aconv (a · b) = {!!} -- RProd (aconv a) (convBase b)

-- conv : {a : Set} -> List (Signature a) -> Rep a
-- conv (Cons x xs) = RSum (aconv x) (conv xs)
-- conv ()


-}