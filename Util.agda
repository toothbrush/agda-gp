module Util where

open import Relation.Binary.Core 

cong : {X Y : Set} {a b : X} -> (f : X -> Y) -> a ≡ b -> f a ≡ f b
cong f refl = refl
