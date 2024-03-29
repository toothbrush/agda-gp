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
convert tyA = makeSum (datatype tyA)

Nat : Set
Nat = μ (convert nat)

zeroNat : Nat
zeroNat = < inj₁ tt >

ListNat : Set
ListNat = μ (convert $ list nat)

z : ListNat
z = < inj₁ tt >

z1 : ListNat
z1 = < inj₂ ( zero , < inj₁ tt > ) >

-- After 4 hours banging head finally managed to create the proof
decodeType_≡A : {A : Set} -> (ty : Type A) → decodeType ty ≡ A
decodeType nat ≡A  = refl
decodeType bool ≡A = refl
decodeType (list a) ≡A with decodeType a | decodeType a ≡A
... | x | refl = refl


-- Naturally following the proof.
-- Main> to (list nat) z1
-- 0 ∷ []
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

-- I suppose this is Spine to Regular
-- Main S→R bool (Con false) 
-- < inj₂ tt >
-- Main> S→R (list nat) (Con _∷_ :<>: (zero :> nat) :<>: ([] :> (list nat)))
-- < inj₂ (0 , < inj₁ tt >) > 
S→R : {A : Set} → (tyA : Type A) → Spine A → μ (convert tyA)
S→R tyA s = from tyA (fromSpine s) 

{-
record IsoProof (A : Set) : Set where
  field
    typeRep : Type A
    repProof : isJust (finalRep typeRep) ≡ true
    fromA : A → μType typeRep repProof
    toA : μType typeRep repProof → A
    invProofA : (x : A) → toA (fromA x) ≡ x
    invProofRepA : (y : μType typeRep repProof) → fromA (toA y) ≡ y

invNat : (x : ℕ) → to NatR refl (from NatR refl x) ≡ x
invNat zero = refl
invNat (suc n) = cong suc (invNat n)
 
invRepNat : (y : μType NatR refl) → from NatR refl (to NatR refl y) ≡ y
invRepNat < inj₁ tt > = refl
invRepNat < inj₂ n > = cong (λ n → < inj₂ n >) (invRepNat n) 

natIso : IsoProof ℕ
natIso = record {typeRep = NatR;
                 repProof = refl;
                 fromA = from NatR refl;
                 toA = to NatR refl;
                 invProofA = invNat;
                 invProofRepA = invRepNat}

invBool : (x : Bool) → to BoolR refl (from BoolR refl x) ≡ x
invBool false = refl
invBool true = refl

invRepBool : (y : μType BoolR refl) → from BoolR refl (to BoolR refl y) ≡ y
invRepBool < inj₁ tt > = refl
invRepBool < inj₂ tt > = refl

boolIso : IsoProof Bool
boolIso = record {typeRep = BoolR;
                  repProof = refl;
                  fromA = from BoolR refl;
                  toA = to BoolR refl;
                  invProofA = invBool;
                  invProofRepA = invRepBool}

-- invList : {A : Set} → (TA : Type A) → (x : List A) → to (ListR TA) (from (ListR TA) x) ≡ x
-- invList TA [] = refl
-- invList TA (x ∷ xs) = cong (λ xs → x ∷ xs) (invList TA xs)

-- invRepList : {A : Set} → (TA : Type A) → (y : μ (regRep (ListR TA))) → from (ListR TA) (to (ListR TA) y) ≡ y
-- invRepList TA < inj₁ tt > = refl
-- invRepList TA < inj₂ (x , xs) > = cong (λ xs → < inj₂ (x , xs) >) (invRepList TA xs)

-- listIso : {A : Set} → Type A → IsoProof (List A)
-- listIso TA = record {typeRep = ListR TA;
--                      repProof = refl;
--                      fromA = from (ListR TA);
--                      toA = to (ListR TA);
--                      invProofA = invList TA;
--                      invProofRepA = invRepList TA}

-}