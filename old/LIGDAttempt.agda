{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module LIGDAttempt where

open import Function
open import Data.List
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Empty

-- Spine Type Universe
data Type : Set → Set₁ where
  NatR    : Type ℕ
  BoolR   : Type Bool
  ListR   : {A : Set} → Type A → Type (List A)

data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} -> Signature (b -> a) -> Type b -> Signature a

infixl 0 _·_

record EP a b : Set where
  field
    from : a -> b
    to   : b -> a

data Rep : Set → Set where
  RUnit     : Rep ⊤
  RBool     : Rep Bool
  RNat      : Rep ℕ
  RSum      : {A B : Set} → Rep A → Rep B → Rep (A ⊎ B)
  RProd     : {A B : Set} → Rep A → Rep B → Rep (A × B)
  RType     : {A B : Set} → EP A B → Rep B → Rep A

ListS : Set -> Set
ListS A = ⊤ ⊎ A × List A

Nat : Set
Nat = ⊤ ⊎ Nat

fromList : ∀ {A} → List A → ListS A
fromList []          = inj₁ tt
fromList (x ∷ xs)  = inj₂ (x , xs)

toList : ∀ {A} → ListS A → List A
toList (inj₁ tt)        = []
toList (inj₂ (x , xs))  = x ∷ xs

listEP : {a : Set} -> EP (List a) (ListS a)
listEP = record {from = fromList; to = toList}

-- LIGD code for lists
rList : ∀ {A} → Rep A → Rep (List A)
rList ra = RType listEP (RSum RUnit (RProd ra (rList ra)))

datatype : {a : Set} -> Type a -> List (Signature a)
datatype BoolR = (Sig false) ∷ ((Sig true) ∷ [])
datatype NatR  = (Sig zero) ∷ ((Sig suc · NatR) ∷ [])
datatype (ListR a) = (Sig []) ∷ ((Sig _∷_ · a · ListR a) ∷ [])

interpretSpine : {a : Set} -> Type a -> Set
interpretSpine NatR = ℕ
interpretSpine BoolR = Bool
interpretSpine (ListR y) = List (interpretSpine y)


makeProd : {a : Set} -> Signature a -> Set
makeProd (Sig _ · b) = interpretSpine b
makeProd (Sig _) = ⊤
makeProd (c · b) = (makeProd c) × (interpretSpine b)

makeSum : {a : Set} -> List (Signature a) -> Set
makeSum [] = ⊤ -- Undefined Case
makeSum  (sig ∷ []) = makeProd sig
makeSum (sig ∷ rest) = (makeProd sig) ⊎ (makeSum rest)

giveEPType : {a : Set} -> Type a -> Set
giveEPType = makeSum ∘ datatype


mutual 
       makeProdRep : {a : Set} -> (b : Signature a) -> Rep (makeProd b)
       makeProdRep (Sig _ · NatR) = RNat
       makeProdRep (Sig _ · BoolR) = RBool
       makeProdRep (Sig _ · (ListR y)) with makeRep y | interpretSpine y
       ... | ra | s = {!!}
       makeProdRep (Sig _) = RUnit
       makeProdRep (c · d) = {!!}
   
       makeSumRep : {a : Set} -> (b : List (Signature a)) -> Rep (makeSum b)
       makeSumRep [] = RUnit -- BAD
       makeSumRep (sig ∷ []) = makeProdRep sig
       makeSumRep (s ∷ r) = {!!} -- RSum (makeProdRep s) (makeSumRep r)

       makeRep : {a : Set} -> (b : Type a) -> Rep (giveEPType b)
       makeRep = makeSumRep ∘ datatype