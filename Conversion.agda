{-# OPTIONS --type-in-type #-}

module Conversion where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Maybe

open import Data.Product
open import Data.Unit
open import Data.Sum

open import Relation.Binary.Core public using (_≡_; refl)

open import Regular
open import Spine
open import Util

makeProd : {A B : Set} → Type A → Signature B → Code
makeProd TA (Sig y) = U
makeProd TA (Sig y · y') with tEQ TA y'
... | nothing = K (raw y')
... | just refl = I
makeProd TA (y · y') with tEQ TA y'
... | nothing = makeProd TA y ⊗ K (raw y')
... | just refl = makeProd TA y ⊗ I

makeSum : {A : Set} → Type A → List (Signature A) → Maybe Code
makeSum TA [] = nothing
makeSum TA (x ∷ []) = just (makeProd TA x)
makeSum TA (x' ∷ xs) with makeSum TA xs
... | nothing = nothing
... | just sum = just (makeProd TA x' ⊕ sum)

finalRep : {A : Set} → Type A → Maybe Code
finalRep TA = makeSum TA (datatype TA)

μType : {A : Set} → (TA : Type A) → isJust (finalRep TA) ≡ true → Set
μType TA proof = μ (fromJust (finalRep TA) proof)

to : {A : Set} → (TA : Type A) → (proof : isJust (finalRep TA) ≡ true) → μType TA proof → A 
to NatR refl < inj₁ tt > = zero
to NatR refl < inj₂ n > = suc (to NatR refl n)
to BoolR refl < inj₁ tt > = true
to BoolR refl < inj₂ tt > = false
to (ListR y) refl < inj₁ x > = []
to (ListR y) refl < inj₂ y' > = {!!}
--to (ListR y) refl < inj₁ tt > = []
--to (ListR y) refl < inj₂ (x , xs) > = {!!}
to (TreeR y) refl < inj₁ x > = {!!}
to (TreeR y) refl < inj₂ y' > = {!!}
--to (TreeR y) refl < inj₁ x > = {!x!}
--to (TreeR y) refl < inj₂ (l , r) > = {!!}

from : {A : Set} → (TA : Type A) → (proof : isJust (finalRep TA) ≡ true) → A → μType TA proof
from NatR refl zero = < inj₁ tt >
from NatR refl (suc n) = < inj₂ (from NatR refl n) >
from BoolR refl true = < inj₁ tt >
from BoolR refl false = < inj₂ tt >
from (TreeR y) refl (Leaf y') = {!!}
from (TreeR y) refl (Node l r) = {!!}
from (ListR y) refl [] = < inj₁ tt >
from (ListR y) refl (x ∷ xs) = {!!}

-- Attempted here to make TA and proof inferrable, but does gives unsolved metas when used.
-- Maybe someone can come up with something that solves this

-- to : {A : Set} {TA : Type A} {proof : isJust (finalRep TA) ≡ true} → μType TA proof → A 
-- to {TA = NatR} {proof = refl} < inj₁ tt > = zero
-- to {TA = NatR} {proof = refl} < inj₂ n > = suc (to n)
-- to {TA = BoolR} {proof = refl} < inj₁ tt > = true
-- to {TA = BoolR} {proof = refl} < inj₂ tt > = false
-- to {TA = (ListR y)} {proof = refl} < inj₁ tt > = []
-- to {TA = (ListR y)} {proof = refl} < inj₂ x > = {!!}
-- to {TA = (TreeR y)} {proof = refl} < inj₁ x > = {!!}
-- to {TA = (TreeR y)} {proof = refl} < inj₂ x > = {!!}

-- from : {A : Set} {TA : Type A} {proof : isJust (finalRep TA) ≡ true} → A → μType TA proof
-- from {TA = NatR} {proof = refl} zero = < inj₁ tt >
-- from {TA = NatR} {proof = refl} (suc n) = < inj₂ (from n) >
-- from {TA = BoolR} {proof = refl} true = < inj₁ tt >
-- from {TA = BoolR} {proof = refl} false = < inj₂ tt >
-- from {TA = (ListR y)} {proof = refl}  [] = < inj₁ tt >
-- from {TA = (ListR y)} {proof = refl} (x ∷ xs) = {!!}
-- from {TA = (TreeR y)} {proof = refl} (Leaf y') = {!!}
-- from {TA = (TreeR y)} {proof = refl} (Node l r) = {!!}

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

