module Lms where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Vec.Properties using (reverse-∷)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero)

open import Data.Vec.Extensions

-- Setup

variable
  T : Set

-- Source

-- Controls whether the version of this language contains Reps and other lifted
-- operators
data W : Set where
  Base : W
  Staged : W

dW : W → Set
dW Base = ⊥
dW Staged = ⊤

data Typ : W → Set where
  N : ∀{w} → Typ w
  _=>_ : ∀{w} → Typ w → Typ w → Typ w
  --Rep : ∀{w} → {dW w} → Typ w → Typ w

Ctx : W → ℕ → Set
Ctx w = Vec (Typ w)

-- We use De Bruijin levels with *reversed* contexts. That is, index 0 refers
-- to the rightmost element of `Γ`. This is because Agda is better-behaved when
-- we use the constructor `∷` instead of the recursive function `∷ʳ` in type
-- formers.
data Tm : (w : W) → {n : ℕ} → Typ w → Ctx w n → Set where
  -- STLC
  C : ∀{w n Γ} → ℕ → Tm w {n} N Γ
  V : ∀{w n Γ} → (i : Fin n) → Tm w (rlookup Γ i) Γ
  λ' : ∀{w n τ₂} {Γ : Ctx w n} → (τ₁ : Typ w) → Tm w τ₂ (τ₁ ∷ Γ) → Tm w (τ₁ => τ₂) Γ
  _$_ : ∀{w n τ₁ τ₂} {Γ : Ctx w n} → Tm w (τ₁ => τ₂) Γ → Tm w τ₁ Γ → Tm w τ₂ Γ

  -- Cut
  Let : ∀{w n τ₁ τ₂} {Γ : Ctx w n} → Tm w τ₁ Γ → Tm w τ₂ (τ₁ ∷ Γ) → Tm w τ₂ Γ

  -- Nat
  _+'_ : ∀{w n} {Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ
  _*'_ : ∀{w n} {Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ

-- TODO: factor out all the Env lemmas

data Env : ∀ {w n} → Ctx w n → Set
data Val : (w : W) → Typ w → Set

data Env where
  nil : ∀{w} → Env {w} []
  cons : ∀{w n τ} {Γ : Ctx w n} → Val w τ → Env Γ → Env (τ ∷ Γ)

data Val where
  Const : ∀{w} → ℕ → Val w N
  Closure : ∀{w n τ₁ τ₂} {Γ : Ctx w n} →
    (env : Env Γ) → Tm w τ₂ (τ₁ ∷ Γ) →
    Val w (τ₁ => τ₂)

revEnv : ∀{w n} {Γ : Ctx w n} → Env Γ → Env (Vec.reverse Γ)
revEnv nil = nil
revEnv (cons {τ = τ} {Γ = Γ} x xs) rewrite reverse-∷ τ Γ = snoc (revEnv xs) x
  where
    _∷ʳ_ = Vec._∷ʳ_
    snoc : ∀{w n} {Γ : Ctx w n} {τ} → Env Γ → Val w τ → Env (Γ ∷ʳ τ)
    snoc nil x = cons x nil
    snoc (cons x' xs) x = cons x' (snoc xs x)

lookupEnv : ∀{w n} {Γ : Ctx w n} → Env Γ → (i : Fin n) → Val w (lookup Γ i)
lookupEnv (cons x xs) Fin.zero = x
lookupEnv (cons x xs) (Fin.suc i) = lookupEnv xs i

rlookupEnv : ∀{w n} {Γ : Ctx w n} → Env Γ → (i : Fin n) → Val w (rlookup Γ i)
rlookupEnv env i = lookupEnv (revEnv env) i

unwrapN : ∀{w} → Val w N → (ℕ → T) → T
unwrapN (Const n) k = k n

liftUnwrap2 : ∀{w} → (ℕ → ℕ → ℕ) → Val w N → Val w N → Val w N
liftUnwrap2 f cx₁ cx₂ = unwrapN cx₁ (λ x₁ → unwrapN cx₂ (λ x₂ → Const (f x₁ x₂)))

eval : ∀{n τ} {Γ : Ctx Base n} → (env : Env Γ) → Tm Base τ Γ → Val Base τ
eval env (C x) = Const x
eval env (V i) = rlookupEnv env i
eval env (λ' τ e) = Closure env e
eval env (e₁ $ e₂) = {! !}
eval {Γ = Γ} env (Let e₁ e₂) = eval (cons x env) e₂
  where x = eval env e₁
eval env (e₁ +' e₂) = liftUnwrap2 (Nat._+_) (eval env e₁) (eval env e₂)
eval env (e₁ *' e₂) = liftUnwrap2 (Nat._*_) (eval env e₁) (eval env e₂)
