{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --type-in-type #-}

module LIGDAndSpine where

-- Unit
data ⊤ : Set where
  tt : ⊤

-- Booleans
data Bool : Set where
  true  : Bool
  false : Bool

-- Naturals
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

data Maybe₁ (A : Set) : Set where
  nothing₁ : Maybe₁ A
  just₁    : A → Maybe₁ A

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
infixr 6 _∷_

-- Sum
data _+_ (A B : Set) : Set where 
  inl : A → A + B
  inr : B → A + B
infixr 5 _+_

-- Product
data _×_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A × B
infixr 6 _×_
infixr 6 _,_

record _≃_ (A B : Set) : Set where
  field
    from : A → B
    to   : B → A
infix 2 _≃_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 7 _≡_

---------------------------------------------------------------------------------

data LCode : Set where
  runit : LCode
  rnat : LCode
  rsum : LCode → LCode → LCode
  rprod : LCode → LCode → LCode
  rtype : (A : Set) → (A → LCode) → (LCode → A) → LCode

L⟦_⟧ : LCode → Set
L⟦ runit ⟧ = ⊤
L⟦ rnat ⟧ = ℕ
L⟦ rsum r₁ r₂ ⟧ = L⟦ r₁ ⟧ + L⟦ r₂ ⟧
L⟦ rprod r₁ r₂ ⟧ = L⟦ r₁ ⟧ × L⟦ r₂ ⟧
L⟦ rtype t _ _ ⟧ = t

---------------------------------------------------------------------------------

data SCode : Set where
  nat : SCode
  bool : SCode
  list : SCode → SCode
  pair : SCode → SCode → SCode

R⟦_⟧ : SCode → Set
R⟦ nat ⟧ = ℕ
R⟦ bool ⟧ = Bool
R⟦ list a ⟧ = List R⟦ a ⟧
R⟦ pair a b ⟧ = R⟦ a ⟧ × R⟦ b ⟧

---------------------------------------------------------------------------------

S→L : SCode → LCode
S→L nat = rnat
S→L bool = rtype Bool {!!} {!!}
S→L (list a) = rtype (List L⟦ S→L a ⟧) {!!} {!!}
S→L (pair a b) = rtype (L⟦ S→L a ⟧ × L⟦ S→L b ⟧) {!!} {!!}

L→S : LCode → Maybe₁ SCode
L→S runit = nothing₁
L→S rnat = just₁ nat
L→S (rsum _ _) = nothing₁
L→S (rprod _ _) = nothing₁
L→S (rtype T _ _) = {!!}

---------------------------------------------------------------------------------

data Type : Set → Set where
  BoolR   : Type Bool
  NatR    : Type ℕ
  ListR   : {A : Set} → Type A → Type (List A)

data Typed : Set → Set where
  _::_ : {A : Set} → A → Type A → Typed A

infixl 1 _::_

val : {A : Set} → Typed A → A
val (v :: _) = v

typeOf : {A : Set} → Typed A → Type A
typeOf (_ :: t) = t

data Spine : Set → Set where
  Con  : {A : Set} → A → Spine A
  _⋄_  : {A B : Set} → Spine (A → B) → Typed A → Spine B
infixl 0 _⋄_

nat1    : Typed ℕ
nat1    = succ zero :: NatR

list[2] : Typed (List ℕ)
list[2] = (succ (succ zero) ∷ []) :: ListR NatR

aListSpine : Spine (List ℕ)
aListSpine = Con _∷_ ⋄ nat1 ⋄ list[2]

---------------------------------------------------------------------------------

data Rep : Set → Set where
  RUnit     : Rep ⊤
  RBool     : Rep Bool
  RNat      : Rep ℕ
  RSum      : {A B : Set} → Rep A → Rep B → Rep (A + B)
  RProd     : {A B : Set} → Rep A → Rep B → Rep (A × B)
  RType     : {A B : Set} → B ≃ A → Rep A → Rep B

ListS : Set -> Set
ListS A = ⊤ + (A × List A)

fromList : ∀ {A} → List A → ListS A
fromList []        = inl tt
fromList (x ∷ xs)  = inr (x , xs)

toList : ∀ {A} → ListS A → List A
toList (inl tt)        = []
toList (inr (x , xs))  = x ∷ xs

isoList : ∀ {A} → List A ≃ ListS A
isoList = record { from = fromList; to = toList}

rList : ∀ {A} → Rep A → Rep (List A)
rList ra = RType isoList (RSum RUnit (RProd ra (rList ra)))

---------------------------------------------------------------------------------

toRep : ∀ {A} → Type A → Rep A
toRep BoolR = RBool
toRep NatR = RNat
toRep (ListR a) = rList (toRep a)

listNatSpine2ListS : Spine (List ℕ) → Maybe (ListS ℕ)
listNatSpine2ListS (Con []) = just (inl tt)
listNatSpine2ListS (Con _ ⋄ x :: NatR ⋄ xs :: ListR NatR) = just (inr (x , xs))
listNatSpine2ListS _ = nothing

listBoolSpine2ListS : Spine (List Bool) → Maybe (ListS Bool)
listBoolSpine2ListS (Con []) = just (inl tt)
listBoolSpine2ListS (Con _ ⋄ x :: BoolR ⋄ xs :: ListR BoolR) = just (inr (x , xs))
listBoolSpine2ListS _ = nothing

listSpine2ListS : {a : Set}  -> Spine (List a) → Maybe (ListS a)
listSpine2ListS (Con []) = just (inl tt)
listSpine2ListS ((Con _) ⋄ x :: a ⋄ xs :: ListR a') = just (inr ({!x!} , {!!})) -- (x , xs)
listSpine2ListS _ = nothing