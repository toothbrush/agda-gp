{-# OPTIONS --type-in-type #-}

module Conversion where

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty
open import Data.Bool public using (Bool; true; false; T; not)
open import Data.Unit using (⊤)

open import Data.Product
open import Data.Unit public using (tt)
open import Data.Sum

open import Relation.Binary.Core public using (_≡_; refl)

open import Regular
open import Spine
open import Util

-- Convert a signature to a code
makeProd : {B : Set} → Signature B → Code
makeProd (Sig _) = U
makeProd (Sig _ · con , t) = K $ decodeType t
makeProd (Sig _ · rec , t) = I
makeProd (s · con , t) = makeProd s ⊗ K (decodeType t)
makeProd (s · rec , t) = makeProd s ⊗ I

-- Convert a list of signatures to a code
makeSum : {A : Set} → List⁺ (Signature A) → Code
makeSum [ x ] = makeProd x
makeSum (x ∷ xs) = makeProd x ⊕ makeSum xs

-- Convert a Spine Type to a Code in Regular
convert : {A : Set} → Type A → Code
convert tyA = makeSum (sigList tyA)

-- Proof that given an Spine type A its interpretation is 
-- the type A that we initially wanted to represent in Spine
decodeType_≡A : {A : Set} -> (ty : Type A) → decodeType ty ≡ A
decodeType nat ≡A  = refl
decodeType bool ≡A = refl
decodeType (list a) ≡A with decodeType a | decodeType a ≡A
... | x | refl = refl

-- Decode function of a regular value whose type was been
-- calculated through a Spine type
to : {A : Set} → (tyA : Type A) → μ (convert tyA) → A
to nat  < inj₁ tt > = zero 
to nat  < inj₂ n >  = suc $ to nat n
to bool < inj₁ tt > = true
to bool < inj₂ tt > = false
to (list a) < inj₁ tt > = []
to (list a) < inj₂ (x , xs) > with decodeType a | decodeType a ≡A | to (list a) xs
... | p | refl | z = x ∷ z 

-- Encode function that produces a regular value correspondent
-- to a Agda value produced by fromSpine.
from : {A : Set} → (tyA : Type A) → A → μ (convert tyA)
from bool true = < inj₁ tt >
from bool false = < inj₂ tt >
from nat zero = < inj₁ tt >
from nat (suc n) = < inj₂ (from nat n) >
from (list a) [] = < inj₁ tt >
from (list a) (x ∷ xs) with decodeType a | decodeType a ≡A | from (list a) xs
... | p | refl | z = < inj₂ (x , z) >

-- Convert a spine value into a regular value
S→R : {A : Set} → (tyA : Type A) → Spine A → μ (convert tyA)
S→R tyA s = from tyA (fromSpine s) 

-- Convert a regular value into a spine value
R→S : {A : Set} → (tyA : Type A) → μ (convert tyA) → Spine A
R→S tyA r = toSpine tyA (to tyA r)
