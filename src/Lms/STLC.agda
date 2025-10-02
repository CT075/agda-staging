module Lms.STLC where

open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Vec.Properties using (reverse-∷)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl)

open import Data.Gas
open import Data.Vec.Extensions

-- Setup

private variable
  T : Set
  n : ℕ

-- Source

-- Controls whether the version of this language contains Reps and other lifted
-- operators
data W : Set where
  Base : W
  Staged : W

private variable w : W

data Typ : W → Set where
  N : Typ w
  _=>_ : Typ w → Typ w → Typ w
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
  C : ∀{Γ} → ℕ → Tm w {n} N Γ
  V : ∀{Γ τ} → (i : Fin n) → {rlookup Γ i ≡ τ} → Tm w τ Γ
  λ' : ∀{τ₂} {Γ : Ctx w n} → (τ₁ : Typ w) → Tm w τ₂ (τ₁ ∷ Γ) → Tm w (τ₁ => τ₂) Γ
  _$_ : ∀{τ₁ τ₂} {Γ : Ctx w n} → Tm w (τ₁ => τ₂) Γ → Tm w τ₁ Γ → Tm w τ₂ Γ

  -- Cut
  Let : ∀{τ₁ τ₂} {Γ : Ctx w n} → Tm w τ₁ Γ → Tm w τ₂ (τ₁ ∷ Γ) → Tm w τ₂ Γ

  -- Nat
  _+'_ : ∀{Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ
  _*'_ : ∀{Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ

  lift : ∀{Γ : Ctx Staged n} {τbase τ} → {wk : weakensTo τbase τ} →
    Tm Staged τ Γ → Tm Staged (Rep τbase) Γ
  _++_ : ∀{Γ : Ctx Staged n} →
    Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ
  _**_ : ∀{Γ : Ctx Staged n} →
    Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ

-- TODO: factor out all the Env lemmas

data Env : Ctx w n → Set
data Val : (w : W) → Typ w → Set

data Env where
  nil : Env {w} []
  cons : ∀{τ} {Γ : Ctx w n} → Val w τ → Env Γ → Env (τ ∷ Γ)

data Val where
  Const : ℕ → Val w N
  Closure : ∀{τ₁ τ₂} {Γ : Ctx w n} →
    (env : Env Γ) → Tm w τ₂ (τ₁ ∷ Γ) →
    Val w (τ₁ => τ₂)

revEnv : ∀{Γ : Ctx w n} → Env Γ → Env (Vec.reverse Γ)
revEnv nil = nil
revEnv (cons {τ = τ} {Γ = Γ} x xs) rewrite reverse-∷ τ Γ = snoc (revEnv xs) x
    where
    _∷ʳ_ = Vec._∷ʳ_
    snoc : ∀{Γ : Ctx w n} {τ} → Env Γ → Val w τ → Env (Γ ∷ʳ τ)
    snoc nil x = cons x nil
    snoc (cons x' xs) x = cons x' (snoc xs x)

lookupEnv : ∀{Γ : Ctx w n} → Env Γ → (i : Fin n) → Val w (lookup Γ i)
lookupEnv (cons x xs) Fin.zero = x
lookupEnv (cons x xs) (Fin.suc i) = lookupEnv xs i

rlookupEnv : ∀{Γ : Ctx w n} → Env Γ → (i : Fin n) → Val w (rlookup Γ i)
rlookupEnv env i = lookupEnv (revEnv env) i

unwrapN : Val w N → (ℕ → T) → T
unwrapN (Const n) k = k n

liftValN2 : (ℕ → ℕ → ℕ) → Val w N → Val w N → Val w N
liftValN2 f cx₁ cx₂ = unwrapN cx₁ (λ x₁ → unwrapN cx₂ (λ x₂ → Const (f x₁ x₂)))

unwrap=> : ∀{τ₁ τ₂} →
  Val w (τ₁ => τ₂) →
  (∀{n} {Γ : Ctx w n} → Env Γ → Tm w τ₂ (τ₁ ∷ Γ) → T) → T
unwrap=> (Closure env e) k = k env e

eval : ∀{τ} {Γ : Ctx Base n} → (gas : ℕ) → (env : Env Γ) → Tm Base τ Γ →
  OrTimeout (Val Base τ)
eval-apply : ∀{τ₁ τ₂} →
  (gas : ℕ) → Val Base (τ₁ => τ₂) → Val Base τ₁ → OrTimeout (Val Base τ₂)

eval zero env _ = Timeout
eval (suc i) env (C x) = Done (Const x)
eval (suc _) env (V i {p}) rewrite sym p = Done (rlookupEnv env i)
eval (suc i) env (λ' τ e) = Done (Closure env e)
eval (suc i) env (e₁ $ e₂) =
  OrTimeoutOps.bindM2 (eval-apply i) (eval i env e₁) (eval i env e₂)
eval (suc i) env (Let e₁ e₂) = do
  x ← eval i env e₁
  eval i (cons x env) e₂
  where open OrTimeoutOps
eval (suc i) env (e₁ +' e₂) =
  OrTimeoutOps.liftA2 (liftValN2 (_+_)) (eval i env e₁) (eval i env e₂)
eval (suc i) env (e₁ *' e₂) =
  OrTimeoutOps.liftA2 (liftValN2 (_*_)) (eval i env e₁) (eval i env e₂)

eval-apply gas f x = unwrap=> f (λ env e → eval gas (cons x env) e)

data _⊢_⇓_ : ∀{τ} {Γ : Ctx Base n} → Env Γ → Tm Base τ Γ → Val Base τ → Set where
  eval-c : ∀{Γ : Ctx Base n} {env : Env Γ} x → env ⊢ C x ⇓ Const x
  eval-vl : ∀{Γ : Ctx Base n} {env : Env Γ} i vl →
    {rlookupEnv env i ≡ vl} →
    env ⊢ V i {refl} ⇓ vl
  eval-λ : ∀{Γ : Ctx Base n} {τ τ'} {e : Tm Base τ' (τ ∷ Γ)} (env : Env Γ) →
    env ⊢ λ' τ e ⇓ Closure env e
  eval-$ : ∀{n' τ₁ τ₂} {Γ : Ctx Base n} {Γ' : Ctx Base n'} {env' : Env Γ'}
    {e₁ : Tm Base (τ₁ => τ₂) Γ} {e₂ x e' v}
    {env : Env Γ} →
    env ⊢ e₁ ⇓ (Closure env' e') → env ⊢ e₂ ⇓ x →
    cons x env' ⊢ e' ⇓ v →
    env ⊢ (e₁ $ e₂) ⇓ v
  eval-let : ∀{τ₁ τ₂} {Γ : Ctx Base n}
    {e₁ : Tm Base τ₁ Γ} {e₂ : Tm Base τ₂ (τ₁ ∷ Γ)}
    {x v} {env : Env Γ} →
    env ⊢ e₁ ⇓ x → (cons x env) ⊢ e₂ ⇓ v →
    env ⊢ Let e₁ e₂ ⇓ v
  eval-+ : ∀{Γ : Ctx Base n} {e₁ e₂} {x₁ x₂ x} {env : Env Γ} →
    env ⊢ e₁ ⇓ Const x₁ → env ⊢ e₂ ⇓ Const x₂ → {x₁ + x₂ ≡ x} →
    env ⊢ e₁ +' e₂ ⇓ Const x
  eval-* : ∀{Γ : Ctx Base n} {e₁ e₂} {x₁ x₂ x} {env : Env Γ} →
    env ⊢ e₁ ⇓ Const x₁ → env ⊢ e₂ ⇓ Const x₂ → {x₁ * x₂ ≡ x} →
    env ⊢ e₁ *' e₂ ⇓ Const x

-- TODO: What is the relationship between env1/env2 and env?
-- with namesets, this is easy
-- with de bruijin, need to reason about interleaving
--correct : ∀{τ} → (e : Tm Staged (Rep τ)) →
--  eval env2 (evalms env1 e) ≡ eval env (forget e)
