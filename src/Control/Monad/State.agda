module Control.Monad.State where

open import Data.Product using (_,_; _×_)

private variable
  A B C T : Set

record State (s : Set) (a : Set) : Set where
  constructor MkState
  field runState : s → s × a

module Ops where
  open State
  private variable S : Set

  _>>=_ : State S A → (A → State S B) → State S B
  mx >>= f = MkState (λ st →
    let (st' , x) = runState mx st
    in runState (f x) st')

  return : T → State S T
  return x = MkState (λ st → (st , x))

  liftA2 : (A → B → C) → State S A → State S B → State S C
  liftA2 f ma mb = do
    a ← ma
    b ← mb
    return (f a b)

  bind : (A → State S B) → State S A → State S B
  bind f x = x >>= f
