module Lms.STLC where

open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Vec.Properties using (reverse-∷)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl)

open import Data.Vec.Extensions

-- Setup

private variable
  T : Set
  n n' : ℕ

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

data IsBase : Typ Base → Typ Staged → Set where
  base-N : IsBase N N
  base-=> : ∀{A A' B B'} → IsBase A A' → IsBase B B' → IsBase (A => B) (A' => B')

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

  CC : ∀{Γ} → Tm Staged N Γ → Tm Staged {n} (Rep N) Γ
  --λλ
  _++_ : ∀{Γ : Ctx Staged n} →
    Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ
  --_$$_

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
  CConst : ℕ → Val Staged (Rep N)
  CVar : (τ : Typ Base) → ℕ → Val Staged (Rep τ)

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

data _⊢_⇓_ : ∀{τ} {Γ : Ctx Base n} → Env Γ → Tm Base τ Γ → Val Base τ → Set where
  eval-C : ∀{Γ : Ctx Base n} {env : Env Γ} x → env ⊢ C x ⇓ Const x
  eval-V : ∀{Γ : Ctx Base n} {env : Env Γ} i vl → {rlookupEnv env i ≡ vl} →
    env ⊢ V i {refl} ⇓ vl
  eval-λ : ∀{Γ : Ctx Base n} {env : Env Γ} {τ τ'} {e : Tm Base τ' _} →
    env ⊢ λ' τ e ⇓ Closure env e
  eval-$ : ∀{Γ : Ctx Base n} {env : Env Γ} {Γ' : Ctx Base n'} {env' : Env Γ'}
    {τ₁ τ₂} {e₁ : Tm Base (τ₁ => τ₂) Γ} {e₂ x e' v} →
    env ⊢ e₁ ⇓ (Closure env' e') → env ⊢ e₂ ⇓ x →
    cons x env' ⊢ e' ⇓ v →
    env ⊢ (e₁ $ e₂) ⇓ v
  eval-let : ∀{Γ : Ctx Base n} {env : Env Γ} {τ₁ τ₂}
    {e₁ : Tm Base τ₁ Γ} {e₂ : Tm Base τ₂ _} {x v} →
    env ⊢ e₁ ⇓ x → (cons x env) ⊢ e₂ ⇓ v →
    env ⊢ Let e₁ e₂ ⇓ v
  eval-+ : ∀{Γ : Ctx Base n} {env : Env Γ} {e₁ e₂ x₁ x₂ v} →
    env ⊢ e₁ ⇓ Const x₁ → env ⊢ e₂ ⇓ Const x₂ → {x₁ + x₂ ≡ v} →
    env ⊢ e₁ +' e₂ ⇓ Const v

data Block : ∀{n} → Ctx Base n → Set where
  bnil : ∀{Γ : Ctx Base n} → Block Γ
  bcons : ∀{Γ : Ctx Base n} {τ} → Tm Base τ Γ → Block Γ → Block (τ ∷ Γ)

record MState : Set where
  constructor ⟨_,:_⟩
  field
    {len} : ℕ
    {stCtx} : Ctx Base len
    stBlock : Block stCtx
    -- It's possible that there is some formulation that doesn't require tracking
    -- `stFresh` separately and uses `len` instead, but it makes tracking the context
    -- of the terms in the block more annoying.
    stFresh : ℕ

private variable
  σ σ' σ'' σ''' : MState

infix 4 _[_]⊢_⇓_▷_
data _[_]⊢_⇓_▷_ : ∀{τ} {Γ : Ctx Staged n} →
    Env Γ → MState → Tm Staged τ Γ → Val Staged τ → MState → Set
  where
  evalms-C : ∀{Γ : Ctx Staged n} {env : Env Γ} x →
    env [ σ ]⊢ C x ⇓ Const x ▷ σ
  evalms-V : ∀{Γ : Ctx Staged n} {env : Env Γ} i v → {rlookupEnv env i ≡ v} →
    env [ σ ]⊢ V i {refl} ⇓ v ▷ σ
  evalms-λ : ∀{Γ : Ctx Staged n} {env : Env Γ} {τ τ'} {e : Tm Staged τ' (τ ∷ Γ)} →
    env [ σ ]⊢ λ' τ e ⇓ Closure env e ▷ σ
  evalms-$ : ∀{Γ : Ctx Staged n} {env : Env Γ} {Γ' : Ctx Staged n'} {env' : Env Γ'}
    {τ₁ τ₂} {e₁ : Tm Staged (τ₁ => τ₂) Γ} {e₂ x e' v} →
    env [ σ ]⊢ e₁ ⇓ Closure env' e' ▷ σ' → env [ σ' ]⊢ e₂ ⇓ x ▷ σ'' →
    (cons x env')[ σ'' ]⊢ e' ⇓ v ▷ σ''' →
    env [ σ ]⊢ e₁ $ e₂ ⇓ v ▷ σ'''
  evalms-let : ∀{Γ : Ctx Staged n} {env : Env Γ} {τ₁ τ₂}
    {e₁ : Tm Staged τ₁ Γ} {e₂ : Tm Staged τ₂ _} {x v} →
    env [ σ ]⊢ e₁ ⇓ x ▷ σ' → (cons x env)[ σ' ]⊢ e₂ ⇓ v ▷ σ'' →
    env [ σ ]⊢ Let e₁ e₂ ⇓ v ▷ σ''
  evalms-+ : ∀{Γ : Ctx Staged n} {env : Env Γ} {e₁ e₂ x₁ x₂ v} → {x₁ + x₂ ≡ v} →
    env [ σ ]⊢ e₁ ⇓ Const x₁ ▷ σ' → env [ σ' ]⊢ e₂ ⇓ Const x₂ ▷ σ'' →
    env [ σ ]⊢ e₁ +' e₂ ⇓ Const v ▷ σ''

  evalms-CC : ∀{Γ : Ctx Staged n} {env : Env Γ} {e x} →
    env [ σ ]⊢ e ⇓ Const x ▷ σ' →
    env [ σ ]⊢ CC e ⇓ CConst x ▷ σ'
