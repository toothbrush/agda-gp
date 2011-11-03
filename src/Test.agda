{-# OPTIONS --type-in-type #-}

module Test where

open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Bool
open import Data.List
open import Conversion
open import Spine
open import Regular


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
