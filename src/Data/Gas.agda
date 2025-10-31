module Data.Gas where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym)

private variable
  A B C T : Set

data OrTimeout (T : Set) : Set where
  Done : T → OrTimeout T
  Timeout : OrTimeout T

module OrTimeoutOps where
  _>>=_ : OrTimeout A → (A → OrTimeout B) → OrTimeout B
  Timeout >>= _ = Timeout
  Done x >>= f = f x

  bind : (A → OrTimeout B) → OrTimeout A → OrTimeout B
  bind f x = x >>= f

  return : T → OrTimeout T
  return = Done

  liftA2 : (A → B → C) → OrTimeout A → OrTimeout B → OrTimeout C
  liftA2 f ma mb = do
    a ← ma
    b ← mb
    Done (f a b)

  bindM2 : (A → B → OrTimeout C) → OrTimeout A → OrTimeout B → OrTimeout C
  bindM2 f ma mb = do
    a ← ma
    b ← mb
    f a b
