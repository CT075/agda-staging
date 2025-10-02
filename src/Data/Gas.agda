module Data.Gas where

private variable
  A B C T : Set

data OrTimeout (T : Set) : Set where
  Done : T → OrTimeout T
  Timeout : OrTimeout T

module OrTimeoutOps where
  _>>=_ : OrTimeout A → (A → OrTimeout B) → OrTimeout B
  Timeout >>= _ = Timeout
  Done x >>= f = f x

  liftA2 : (A → B → C) → OrTimeout A → OrTimeout B → OrTimeout C
  liftA2 f ma mb = do
    a ← ma
    b ← mb
    Done (f a b)

  bind : (A → OrTimeout B) → OrTimeout A → OrTimeout B
  bind f x = x >>= f

  return : T → OrTimeout T
  return = Done
