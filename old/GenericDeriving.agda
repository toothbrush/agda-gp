{-# OPTIONS --type-in-type #-}

module GenericDeriving where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Coinduction
open import Category.Monad.Partiality

-- Code for Generic Deriving
data Code (I : Set) : Set where
  U : Code I
  P : I -> Code I
  R : (Set -> Set) -> Code
  _⊕_ : Code I → Code I → Code I
  _⊗_ : Code I → Code I → Code I

-- Interpretation function for Generic Deriving Code
⟦_⟧_ : Code → Set → Set
⟦ U ⟧       p = ⊤
⟦ P ⟧       p = p
⟦ R f ⟧     p = f p
⟦ c1 ⊕ c2 ⟧ p = ⟦ c1 ⟧ p ⊎ ⟦ c2 ⟧ p
⟦ c1 ⊗ c2 ⟧ p = ⟦ c1 ⟧ p × ⟦ c2 ⟧ p

list : Code
list = U ⊕ (P ⊗ (R {!!}))

-- Least fix point of Codes
data μ_ {I : Set} (c : Code) : I -> Set where
  <_> : ∀ {i} -> ⟦ c ⟧ (μ c) i → μ c i
