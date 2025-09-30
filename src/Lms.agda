module Lms where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Vec.Properties using (reverse-∷)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl)

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

data Typ : W → Set where
  N : ∀{w} → Typ w
  _=>_ : ∀{w} → Typ w → Typ w → Typ w
  Rep : Typ Base → Typ Staged

data weakensTo : Typ Base → Typ Staged → Set where
  weaken-N : weakensTo N N

Ctx : W → ℕ → Set
Ctx w = Vec (Typ w)

-- We use De Bruijin levels with *reversed* contexts. That is, index 0 refers
-- to the rightmost element of `Γ`. This is because Agda is better-behaved when
-- we use the constructor `∷` instead of the recursive function `∷ʳ` in type
-- formers.
data Tm : (w : W) → {n : ℕ} → Typ w → Ctx w n → Set where
  -- STLC
  C : ∀{w n Γ} → ℕ → Tm w {n} N Γ
  V : ∀{w n Γ τ} → (i : Fin n) → {rlookup Γ i ≡ τ} → Tm w τ Γ
  λ' : ∀{w n τ₂} {Γ : Ctx w n} → (τ₁ : Typ w) → Tm w τ₂ (τ₁ ∷ Γ) → Tm w (τ₁ => τ₂) Γ
  _$_ : ∀{w n τ₁ τ₂} {Γ : Ctx w n} → Tm w (τ₁ => τ₂) Γ → Tm w τ₁ Γ → Tm w τ₂ Γ

  -- Cut
  Let : ∀{w n τ₁ τ₂} {Γ : Ctx w n} → Tm w τ₁ Γ → Tm w τ₂ (τ₁ ∷ Γ) → Tm w τ₂ Γ

  -- Nat
  _+'_ : ∀{w n} {Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ
  _*'_ : ∀{w n} {Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ

  lift : ∀{n} {Γ : Ctx Staged n} {τbase τ} → {wk : weakensTo τbase τ} →
    Tm Staged τ Γ → Tm Staged (Rep τbase) Γ
  _++_ : ∀{n} {Γ : Ctx Staged n} →
    Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ
  _**_ : ∀{n} {Γ : Ctx Staged n} →
    Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ

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

data OrTimeout (T : Set) : Set where
  Done : T → OrTimeout T
  Timeout : OrTimeout T

module OrTimeoutOps where
  _>>=_ : {A B : Set} → OrTimeout A → (A → OrTimeout B) → OrTimeout B
  Timeout >>= _ = Timeout
  Done x >>= f = f x

  liftA2 : {A B C : Set} → (A → B → C) → OrTimeout A → OrTimeout B → OrTimeout C
  liftA2 f ma mb = do
    a ← ma
    b ← mb
    Done (f a b)

  bind : {A B : Set} → (A → OrTimeout B) → OrTimeout A → OrTimeout B
  bind f x = x >>= f

unwrapN : ∀{w} → Val w N → (ℕ → T) → T
unwrapN (Const n) k = k n

liftValN2 : ∀{w} → (ℕ → ℕ → ℕ) → Val w N → Val w N → Val w N
liftValN2 f cx₁ cx₂ = unwrapN cx₁ (λ x₁ → unwrapN cx₂ (λ x₂ → Const (f x₁ x₂)))

unwrap=> : ∀{w τ₁ τ₂} →
  Val w (τ₁ => τ₂) →
  (∀{n} {Γ : Ctx w n} → Env Γ → Tm w τ₂ (τ₁ ∷ Γ) → T) → T
unwrap=> (Closure env e) k = k env e

eval : ∀{n τ} {Γ : Ctx Base n} → (gas : ℕ) → (env : Env Γ) → Tm Base τ Γ →
  OrTimeout (Val Base τ)
eval zero env _ = Timeout
eval (suc i) env (C x) = Done (Const x)
eval (suc _) env (V i {p}) rewrite sym p = Done (rlookupEnv env i)
eval (suc i) env (λ' τ e) = Done (Closure env e)
eval (suc i) env (e₁ $ e₂) = do
  f ← eval i env e₁
  x ← eval i env e₂
  unwrap=> f (λ env' e → eval i (cons x env') e)
  where open OrTimeoutOps
eval (suc i) env (Let e₁ e₂) = do
  x ← eval i env e₁
  eval i (cons x env) e₂
  where open OrTimeoutOps
eval (suc i) env (e₁ +' e₂) =
  OrTimeoutOps.liftA2 (liftValN2 (_+_)) (eval i env e₁) (eval i env e₂)
eval (suc i) env (e₁ *' e₂) =
  OrTimeoutOps.liftA2 (liftValN2 (_*_)) (eval i env e₁) (eval i env e₂)

data _⊢_⇓_ : ∀{n τ} {Γ : Ctx Base n} → Env Γ → Tm Base τ Γ → Val Base τ → Set where
  eval-c : ∀{n} {Γ : Ctx Base n} {env : Env Γ} x → env ⊢ C x ⇓ Const x
  eval-vl : ∀{n} {Γ : Ctx Base n} {env : Env Γ} i vl →
    {rlookupEnv env i ≡ vl} →
    env ⊢ V i {refl} ⇓ vl
  eval-λ : ∀{n} {Γ : Ctx Base n} {τ τ'} {e : Tm Base τ' (τ ∷ Γ)} (env : Env Γ) →
    env ⊢ λ' τ e ⇓ Closure env e
  eval-$ : ∀{n n' τ₁ τ₂} {Γ : Ctx Base n} {Γ' : Ctx Base n'} {env' : Env Γ'}
    {e₁ : Tm Base (τ₁ => τ₂) Γ} {e₂ x e' v}
    {env : Env Γ} →
    env ⊢ e₁ ⇓ (Closure env' e') → env ⊢ e₂ ⇓ x →
    cons x env' ⊢ e' ⇓ v →
    env ⊢ (e₁ $ e₂) ⇓ v
  eval-let : ∀{n τ₁ τ₂} {Γ : Ctx Base n}
    {e₁ : Tm Base τ₁ Γ} {e₂ : Tm Base τ₂ (τ₁ ∷ Γ)}
    {x v} {env : Env Γ} →
    env ⊢ e₁ ⇓ x → (cons x env) ⊢ e₂ ⇓ v →
    env ⊢ Let e₁ e₂ ⇓ v
  eval-+ : ∀{n} {Γ : Ctx Base n} {e₁ e₂} {x₁ x₂ x} {env : Env Γ} →
    env ⊢ e₁ ⇓ Const x₁ → env ⊢ e₂ ⇓ Const x₂ → {x₁ + x₂ ≡ x} →
    env ⊢ e₁ +' e₂ ⇓ Const x
  eval-* : ∀{n} {Γ : Ctx Base n} {e₁ e₂} {x₁ x₂ x} {env : Env Γ} →
    env ⊢ e₁ ⇓ Const x₁ → env ⊢ e₂ ⇓ Const x₂ → {x₁ * x₂ ≡ x} →
    env ⊢ e₁ *' e₂ ⇓ Const x

-- TODO: What is the relationship between env1/env2 and env?
-- with namesets, this is easy
-- with de bruijin, need to reason about interleaving
--correct : ∀{τ} → (e : Tm Staged (Rep τ)) →
--  eval env2 (evalms env1 e) ≡ eval env (forget e)
