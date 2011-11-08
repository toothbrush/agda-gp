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
-- We know that A ≡ B
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

-- After 4 hours banging head finally managed to create the proof
decodeType_≡A : {A : Set} -> (ty : Type A) → decodeType ty ≡ A
decodeType nat ≡A  = refl
decodeType bool ≡A = refl
decodeType (list a) ≡A with decodeType a | decodeType a ≡A
... | x | refl = refl

applyParams : {A : Set} → (sig : Signature A) → ⟦ makeProd sig ⟧ A → A
applyParams (Sig v) tt = v
applyParams (Sig f · con , v) k with decodeType v ≡A 
... | j = f {!!}
applyParams (Sig y · rec , proj₂) k = {!!}
applyParams (y · y' · y0) k = {!!} 

-- We need to find a way of relating the Signature A with the Type A
chooseSig : {A : Set}{tyA : Type A} → List⁺ (Signature A) → μ (convert tyA) → A
chooseSig [ sig ] < y > with y 
... | x = applyParams sig {!!}
chooseSig (x ∷ xs) < y > = {!!}

-- Naturally following the proof.
-- Main> to (list nat) z1
-- 0 ∷ []
to' : {A : Set} → (tyA : Type A) → μ (convert tyA) → A
to' tyA val with sigList tyA
... | lSig = chooseSig lSig val

to : {A : Set} → (tyA : Type A) → μ (convert tyA) → A
to nat  < inj₁ tt > = zero 
to nat  < inj₂ n >  = suc $ to nat n
to bool < inj₁ tt > = true
to bool < inj₂ tt > = false
to (list a) < inj₁ tt > = []
to (list a) < inj₂ (x , xs) > with decodeType a | decodeType a ≡A | to (list a) xs
... | p | refl | z = x ∷ z 

-- Main> from (list nat) (0 ∷ [])
-- < inj₂ (0 , < inj₁ tt >) >
from : {A : Set} → (tyA : Type A) → A → μ (convert tyA)
from bool true = < inj₁ tt >
from bool false = < inj₂ tt >
from nat zero = < inj₁ tt >
from nat (suc n) = < inj₂ (from nat n) >
from (list a) [] = < inj₁ tt >
from (list a) (x ∷ xs) with decodeType a | decodeType a ≡A | from (list a) xs
... | p | refl | z = < inj₂ (x , z) >

-- Main S→R bool (Con false) 
-- < inj₂ tt >
-- Main> S→R (list nat) (Con _∷_ :<>: (zero :> nat) :<>: ([] :> (list nat)))
-- < inj₂ (0 , < inj₁ tt >) > 
S→R : {A : Set} → (tyA : Type A) → Spine A → μ (convert tyA)
S→R tyA s = from tyA (fromSpine s) 

-- Main> R→S (list nat) (< inj₂ (0 , < inj₁ tt >) >)
-- Con _∷_ :<>: 0 :> nat :<>: [] :> list nat
R→S : {A : Set} → (tyA : Type A) → μ (convert tyA) → Spine A
R→S tyA r = toSpine tyA (to tyA r)
