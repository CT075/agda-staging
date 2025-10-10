module Lms.STLC where

open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Vec.Properties using (reverse-∷)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl)

open import Data.Gas
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
  eval-c : ∀{Γ : Ctx Base n} {env : Env Γ} x → env ⊢ C x ⇓ Const x
  eval-vl : ∀{Γ : Ctx Base n} {env : Env Γ} i vl →
    {rlookupEnv env i ≡ vl} →
    env ⊢ V i {refl} ⇓ vl
  eval-λ : ∀{Γ : Ctx Base n} {τ τ'} {e : Tm Base τ' (τ ∷ Γ)} {env : Env Γ} →
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

data Block : ∀{n} → Ctx Base n → Set where
  bnil : ∀{Γ : Ctx Base n} → Block Γ
  bcons : ∀{Γ : Ctx Base n} {τ} → Tm Base τ Γ → Block Γ → Block (τ ∷ Γ)

infix 4 _[_,_]⊢_⇓_▷⟨_,_⟩
data _[_,_]⊢_⇓_▷⟨_,_⟩ : ∀{a b τ} {Γ : Ctx Staged n} {Δ : Ctx Base a} {Δ' : Ctx Base b} →
    Env Γ → Block Δ → ℕ →
    Tm Staged τ Γ →
    Val Staged τ → Block Δ' → ℕ → Set
  where
  evalms-c : ∀{Γ : Ctx Staged n} {Δ : Ctx Base n'} {env : Env Γ} {b : Block Δ} {fresh} x →
    env [ b , fresh ]⊢ C x ⇓ Const x ▷⟨ b , fresh ⟩
  evalms-vl : ∀{Γ : Ctx Staged n} {Δ : Ctx Base n'} {env : Env Γ} {b : Block Δ} {fresh} i vl →
    {rlookupEnv env i ≡ vl} →
    env [ b , fresh ]⊢ V i {refl} ⇓ vl ▷⟨ b , fresh ⟩
  evalms-λ : ∀{Γ : Ctx Staged n} {Δ : Ctx Base n'} {τ τ'}
    {e : Tm Staged τ' (τ ∷ Γ)} {env : Env Γ} {b : Block Δ} {fresh} →
    env [ b , fresh ]⊢ λ' τ e ⇓ Closure env e ▷⟨ b , fresh ⟩
  evalms-$ : ∀{n₀ n₁ n₂ n₃}
    {Γ : Ctx Staged n} {Γ' : Ctx Staged n'} {env : Env Γ} {env' : Env Γ'}
    {τ₁ τ₂} {e₁ : Tm Staged (τ₁ => τ₂) Γ} {e₂ x e' v}
    {Δ : Ctx Base n₀} {Δ' : Ctx Base n₁} {Δ'' : Ctx Base n₂} {Δ''' : Ctx Base n₃}
    {b : Block Δ} {b' : Block Δ'} {b'' : Block Δ''} {b''' : Block Δ'''}
    {fresh fresh' fresh'' fresh'''} →
    env [ b , fresh ]⊢ e₁ ⇓ (Closure env' e') ▷⟨ b' , fresh' ⟩ →
    env [ b' , fresh' ]⊢ e₂ ⇓ x ▷⟨ b'' , fresh'' ⟩ →
    (cons x env') [ b'' , fresh'' ]⊢ e' ⇓ v ▷⟨ b''' , fresh''' ⟩ →
    env [ b , fresh ]⊢ e₁ $ e₂ ⇓ v ▷⟨ b''' , fresh''' ⟩
