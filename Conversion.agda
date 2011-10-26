{-# OPTIONS --type-in-type #-}

module Conversion where

open import Data.Nat
open import Data.List
open import Data.Bool

open import Data.Product
open import Data.Unit
open import Data.Sum

open import Relation.Binary.Core public using (_≡_; refl)

open import Regular
open import Spine
open import Util

regRep : {a : Set} -> Type a -> C
regRep NatR = U ⊕ I
regRep BoolR = U ⊕ U
regRep (ListR {a} y) = U ⊕ (K a ⊗ I)

data μ_ (c : C) : Set where
  <_> : el c (μ c) → μ c

Nat = μ (regRep NatR)

ListC : {a : Set} -> Type a -> Set
ListC a = μ (regRep (ListR a)) 

nil : {A : Set} {a : Type A} -> ListC a
nil = < inj₁ tt >

cons : {A : Set} {a : Type A} -> A -> ListC a -> ListC a
cons x xs = < inj₂ (x , xs) >  

from : {A : Set} -> (TA : Type A) -> A -> μ (regRep TA)
from NatR zero = < inj₁ tt >
from NatR (suc n) = < inj₂ (from NatR n) >
from BoolR true = < inj₁ tt >
from BoolR false = < inj₂ tt >
from (ListR y) [] = < inj₁ tt >
from (ListR y) (x ∷ xs) = < inj₂ (x , from (ListR y) xs) >

to : {A : Set} -> (ta : Type A) -> μ (regRep ta) -> A 
to NatR < inj₁ tt > = zero
to NatR < inj₂ n > = suc (to NatR n)
to BoolR < inj₁ tt > = true
to BoolR < inj₂ tt > = false
to (ListR y) < inj₁ tt > = []
to (ListR y) < inj₂ (x , xs) > = x ∷ to (ListR y) xs

record IsoProof (A : Set) : Set where
  field
    typeRep : Type A
    fromA : A -> μ (regRep typeRep)
    toA : μ (regRep typeRep) -> A
    invProofA : (x : A) -> toA (fromA x) ≡ x
    invProofRepA : (y : μ (regRep typeRep)) -> fromA (toA y) ≡ y

invNat : (x : ℕ) -> to NatR (from NatR x) ≡ x
invNat zero = refl
invNat (suc n) = cong suc (invNat n)

invRepNat : (y : μ (regRep NatR)) -> from NatR (to NatR y) ≡ y
invRepNat < inj₁ tt > = refl
invRepNat < inj₂ n > = cong (λ n -> < inj₂ n >) (invRepNat n)

natIso : IsoProof ℕ
natIso = record {typeRep = NatR;
                 fromA = from NatR;
                 toA = to NatR;
                 invProofA = invNat;
                 invProofRepA = invRepNat}