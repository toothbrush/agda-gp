{-# OPTIONS --type-in-type #-}

module First where

  open import IO
  open import Data.Unit
  open import Data.Nat
  open import Data.Maybe
  open import Data.Bool
  open import Data.Empty
  open import Data.Sum
  open import Data.Product
  open import Data.String
  open import Relation.Binary.PropositionalEquality
  open import Function.Inverse
  open import Relation.Binary


  record EP (a : Set) (b : Set) : Set where 
    field  from : (a -> b)
           to   : (b -> a)
           iso₁  : ∀ {x} → from (to x) ≡ x
           iso₂  : ∀ {x} → to (from x) ≡ x

  sucn≡sucm : {a b : ℕ} -> (a ≡ b) -> (suc a ≡ suc b)
  sucn≡sucm (n≡m) = cong suc (n≡m)

  zero≡zero : zero ≡ zero
  zero≡zero = refl

  neg : (a : Bool) -> Bool
  neg true = true
  neg false = false

  iso1 : (x : Bool) -> neg (neg x) ≡ x
  iso1 true = refl
  iso1 false = refl

  -- The LIGD universe, ported to Agda. 
  data Code : Set -> Set₁ where
    RUnit : Code ⊤
    RNat : Code ℕ
    RSum : {a b : Set} -> Code a -> Code b -> Code (a ⊎ b)
    RProd : {a b : Set} -> Code a -> Code b -> Code (a × b) 
    RCon : {a : Set} -> String -> Code a -> Code a
    RType : {a b : Set} -> EP a b -> Code b -> Code a

  ⟦_⟧₁ : ∀ {a} -> Code a → Set
  ⟦ RUnit ⟧₁ = ⊤
  ⟦ RNat  ⟧₁ = ℕ
  ⟦ RSum a b ⟧₁ = ⟦ a ⟧₁ ⊎ ⟦ b ⟧₁
  ⟦ RProd a b ⟧₁ = ⟦ a ⟧₁ × ⟦ b ⟧₁
  ⟦ RCon s a ⟧₁ = ⟦ a ⟧₁
  ⟦ RType ep ca ⟧₁ =  ⟦ ca ⟧₁
