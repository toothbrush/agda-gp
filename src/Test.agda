{-# OPTIONS --type-in-type #-}

module Test where

open import Data.Sum
open import Data.Product
open import Data.Bool
open import Data.Nat
open import Data.List

open import Conversion
open import Spine
open import Regular
open import Util

-- Naturals in Regular
Nat : Set
Nat = μ (convert nat)

-- List of Natural in Regular
ListNat : Set
ListNat = μ (convert $ list nat)

z : ListNat
z = < inj₁ tt >

z1 : ListNat
z1 = < inj₂ ( zero , < inj₁ tt > ) >

True : Spine Bool
True = Con true

zeroo : Spine ℕ
zeroo = Con zero

two : Spine ℕ
two = Con suc :<>: (suc zero :> nat)
