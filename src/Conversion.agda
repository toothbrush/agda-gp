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

-- open import Relation.Nullary.Decidable 
open import Relation.Binary.Core public using (_≡_; refl)

open import Regular
open import Spine
open import Util

-- Convert a signature to a code
-- We know that A ≡ B
makeProd : {B : Set} → Signature B → Code
makeProd (Sig _) = U
makeProd (Sig _ · con , t) = K $ interpretSTRep t
makeProd (Sig _ · rec , t) = I
makeProd (s · con , t) = makeProd s ⊗ K (interpretSTRep t)
makeProd (s · rec , t) = makeProd s ⊗ I

-- Convert a list of signatures to a code
makeSum : {A : Set} → List⁺ (Signature A) → Code
makeSum [ x ] = makeProd x
makeSum (x ∷ xs) = makeProd x ⊕ makeSum xs

-- Convert a Spine Type to a Code in Regular
convert : {A : Set} → Type A → Code
convert tyA = makeSum (sigList tyA)

-- After 4 hours banging head finally managed to create the proof
interpretSTRep_≡A : {A : Set} -> (ty : Type A) → interpretSTRep ty ≡ A
interpretSTRep nat ≡A  = refl
interpretSTRep bool ≡A = refl
interpretSTRep (list a) ≡A with interpretSTRep a | interpretSTRep a ≡A
... | x | refl = refl

-- Naturally following the proof.
-- Main> injectReg (list nat) z1
-- 0 ∷ []
injectReg : {A : Set} → (tyA : Type A) → μ (convert tyA) → A
injectReg nat  < inj₁ tt > = zero 
injectReg nat  < inj₂ n >  = suc $ injectReg nat n
injectReg bool < inj₁ tt > = true
injectReg bool < inj₂ tt > = false
injectReg (list a) < inj₁ tt > = []
injectReg (list a) < inj₂ (x , xs) > with interpretSTRep a | interpretSTRep a ≡A | injectReg (list a) xs
... | p | refl | z = x ∷ z 

-- Main> pullbackReg (list nat) (0 ∷ [])
-- < inj₂ (0 , < inj₁ tt >) >
pullbackReg : {A : Set} → (tyA : Type A) → A → μ (convert tyA)
pullbackReg bool true = < inj₁ tt >
pullbackReg bool false = < inj₂ tt >
pullbackReg nat zero = < inj₁ tt >
pullbackReg nat (suc n) = < inj₂ (pullbackReg nat n) >
pullbackReg (list a) [] = < inj₁ tt >
pullbackReg (list a) (x ∷ xs) with interpretSTRep a | interpretSTRep a ≡A | pullbackReg (list a) xs
... | p | refl | z = < inj₂ (x , z) >

-- Main S→R bool (Con false) 
-- < inj₂ tt >
-- Main> S→R (list nat) (Con _∷_ :<>: (zero :> nat) :<>: ([] :> (list nat)))
-- < inj₂ (0 , < inj₁ tt >) > 
S→R : {A : Set} → (tyA : Type A) → Spine A → μ (convert tyA)
S→R tyA s = pullbackReg tyA (fromSpine s) 

-- Main> R→S (list nat) (< inj₂ (0 , < inj₁ tt >) >)
-- Con _∷_ :<>: 0 :> nat :<>: [] :> list nat
R→S : {A : Set} → (tyA : Type A) → μ (convert tyA) → Spine A
R→S tyA r = toSpine tyA (injectReg tyA r)
