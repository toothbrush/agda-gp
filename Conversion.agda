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

-- Convert a signature to a code
-- We know that A ≡ B
makeProd : {A B : Set} → Type A → Signature B → Code
makeProd tyA (Sig y) = U
makeProd tyA (Sig y · tyB) with Type tyA ≡Type tyB
... | nothing = K $ decodeType tyB
... | just refl = I
makeProd tyA (y · tyB) with Type tyA ≡Type tyB
... | nothing = makeProd tyA y ⊗ K (decodeType tyB)
... | just refl = makeProd tyA y ⊗ I

--makeProd tyA (Sig _) = U
--makeProd tyA (Sig _ · con , t) = K $ decodeType t
--makeProd tyA (Sig _ · rec , t) = I
--makeProd tyA (s · con , t) = makeProd tyA s ⊗ K (decodeType t)
--makeProd tyA (s · rec , t) = makeProd tyA s ⊗ I

-- Convert a list of signatures to a code
makeSum : {A : Set} → Type A → ListNZ (Signature A) → Code
makeSum tyA (El x) = makeProd tyA x
makeSum tyA (x ∷ xs) = makeProd tyA x ⊕ makeSum tyA xs

-- Convert a Spine Type to a Code in Regular
convert : {A : Set} → Type A → Code
convert tyA = makeSum tyA (datatype tyA)


μType : {A : Set} → (TA : Type A) → Set
μType tyA = μ (convert tyA)

Nat : Set
Nat = μType nat  

zeroNat : Nat
zeroNat = < inj₁ tt >

{--MyList : {a : Set} -> Type a -> Set
MyList a = μType (list a) refl

[x] : MyList nat
[x] = < inj₂ ( zero , < inj₁ tt > ) >

f : {a : Set}{b : Type a} -> MyList b -> MyList b
f < inj₁ tt > = < inj₁ tt >
f < inj₂ y > = {!!}

-- xx = [[]]
-- xx should be:
-- xx = < inj₂ ( < inj₁ tt > , < inj₁ tt > )
--xx : MyListList
--xx = < inj₂ ( [] , < inj₁ tt > ) >
--}
{--to₀ : {A : Set} → (T : Type₀ A) → (proof : isJust (convert (t₀ T)) ≡ true) → μType (t₀ T) proof → A
to₀ bool refl < inj₁ tt > = false
to₀ bool refl < inj₂ tt > = true
to₀ nat refl < inj₁ tt > = zero
to₀ nat refl < inj₂ n > = suc (to₀ nat refl n)

to₁ : {F : Set → Set} {A : Set} → (t : Type₁ F A) → (proof : isJust (convert (t₁ t)) ≡ true) → μType (t₁ t) proof → F A
to₁ (list _) refl < inj₁ tt > = []
to₁ (list bool) refl < inj₂ (x , xs) > = x ∷ to₁ (list bool) refl xs
to₁ (list nat) refl < inj₂ (x , xs) > = x ∷ to₁ (list nat) refl xs
to₁ (tree bool) refl < inj₁ x > = Leaf x
to₁ (tree nat) refl < inj₁ x > = Leaf x
to₁ (tree bool) refl < inj₂ (x , y) > = Node (to₁ (tree bool) refl x) (to₁ (tree bool) refl x)
to₁ (tree nat) refl < inj₂ (x , y) > = Node (to₁ (tree nat) refl x) (to₁ (tree nat) refl y)

to : {A : Set} → (TA : Type A) → (proof : isJust (convert TA) ≡ true) → μType TA proof → A
to (t₀ t) p v = to₀ t p v
to (t₁ t) p v = to₁ t p v
-}

to : {A : Set} → (tyA : Type A) → μType tyA → A 
to nat  < inj₁ tt > = zero
to nat  < inj₂ n >  = suc $ to nat n
to bool < inj₁ tt > = true
to bool < inj₂ tt > = false
to (list a) < inj₁ tt > = []
to (list _) < inj₂ x > = x

{-
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

-}