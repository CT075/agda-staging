module Lms where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)

-- Setup

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
  -- By including a `dW w` term, we can't even utter the type `Rep` in the
  -- base language.
  Rep : ∀{w} → {dW w} → Typ w → Typ w

data Tm : W → ℕ → Set where
  -- STLC
  C : ∀{n w} → ℕ → Tm w n
  V : ∀{n w} → (i : Fin n) → Tm w n
  λ' : ∀{n w} → Tm w (Nat.suc n) → Tm w n
  _$_ : ∀{n w} → Tm w n → Tm w n → Tm w n

  -- Cut
  Let : ∀{n w} → Tm w n → Tm w (Nat.suc n) → Tm w n

  -- Nat
  _+_ : ∀{n w} → Tm w n → Tm w n → Tm w n

  -- Rep
  CC : ∀{n} → ℕ → Tm Staged n
  λλ : ∀{n} → Tm Staged (Nat.suc n) → Tm Staged n
  _$$_ : ∀{n} → Tm Staged n → Tm Staged n → Tm Staged n
  _++_ : ∀{n} → Tm Staged n → Tm Staged n → Tm Staged n

data Val : W → Set
Env : W → ℕ → Set

data Val where
  Cst : ∀{w} → ℕ → Val w
  Clo : ∀{w n} → Env w n → Tm w (Nat.suc n) → Val w
  Code : Val Staged
Env w = Vec (Val w)

-- Typing

Ctx : W → ℕ → Set
Ctx w = Vec (Typ w)

data _⊢_∈_ : ∀{n w} → Ctx w n → Tm w n → Typ w → Set where
  typ-lit : ∀{n w} {Γ : Ctx w n} {x} → Γ ⊢ C x ∈ N
  typ-var : ∀{n w} {Γ : Ctx w n} {i : Fin n} → Γ ⊢ V i ∈ lookup Γ i
  typ-abs : ∀{n w} {Γ : Ctx w n} {A B e} →
    (A ∷ Γ) ⊢ e ∈ B →
    Γ ⊢ λ' e ∈ (A => B)
  typ-app : ∀{n w} {Γ : Ctx w n} {A B e₁ e₂} →
    Γ ⊢ e₁ ∈ (A => B) → Γ ⊢ e₂ ∈ A →
    Γ ⊢ (e₁ $ e₂) ∈ B
  typ-let : ∀{n w} {Γ : Ctx w n} {A B e₁ e₂} →
    Γ ⊢ e₁ ∈ A → (A ∷ Γ) ⊢ e₂ ∈ B →
    Γ ⊢ Let e₁ e₂ ∈ B

  typ-add : ∀{n w} {Γ : Ctx w n} {e₁ e₂} →
    Γ ⊢ e₁ ∈ N → Γ ⊢ e₂ ∈ N →
    Γ ⊢ e₁ + e₂ ∈ N

  typ-lit2 : ∀{n} {Γ : Ctx Staged n} {x} → Γ ⊢ CC x ∈ Rep N
  typ-abs2 : ∀{n} {Γ : Ctx Staged n} {A B e} →
    (A ∷ Γ) ⊢ e ∈ B →
    Γ ⊢ λλ e ∈ Rep (A => B)
  typ-app2 : ∀{n} {Γ : Ctx Staged n} {A B e₁ e₂} →
    Γ ⊢ e₁ ∈ Rep (A => B) → Γ ⊢ e₂ ∈ Rep A →
    Γ ⊢ (e₁ $$ e₂) ∈ Rep B
  typ-add2 : ∀{n} {Γ : Ctx Staged n} {e₁ e₂} →
    Γ ⊢ e₁ ∈ Rep N → Γ ⊢ e₂ ∈ Rep N →
    Γ ⊢ e₁ ++ e₂ ∈ Rep N

-- Environment validity

data ⊢v_∈_ : ∀{w} → Val w → Typ w → Set
data _⊨_ : ∀{n w} → Ctx w n → Env w n → Set

data ⊢v_∈_ where
  typv-cst : ∀{w x} → ⊢v Cst {w} x ∈ N
  typv-clo : ∀{w n} {Γ : Ctx w n} {env : Env w n} {A B e} →
    Γ ⊨ env → (A ∷ Γ) ⊢ e ∈ B →
    ⊢v Clo env e ∈ (A => B)

data _⊨_ where
  nil-valid : ∀{w} → _⊨_ {_} {w} [] []
  cons-valid : ∀{n w} {Γ : Ctx w n} {env : Env w n} {vl : Val w} {τ} →
    ⊢v vl ∈ τ → Γ ⊨ env →
    (τ ∷ Γ) ⊨ (vl ∷ env)

env-lookup : ∀{w n} {Γ : Ctx w n} {env : Env w n} →
  Γ ⊨ env → (i : Fin n) →
  ⊢v lookup env i ∈ lookup Γ i
env-lookup (cons-valid ⊢vl∈τ Γ⊨env) Fin.zero = ⊢vl∈τ
env-lookup (cons-valid ⊢vl∈τ Γ⊨env) (Fin.suc i) = env-lookup Γ⊨env i

-- Single stage evaluator

record TypedVal (w : W) (τ : Typ w) : Set where
  constructor _by_
  field
    val : Val w
    proof : ⊢v val ∈ τ

eval : ∀{n τ} (Γ : Ctx Base n) (env : Env Base n) →
  Γ ⊨ env →
  (tm : Tm Base n) → Γ ⊢ tm ∈ τ →
  TypedVal Base τ
eval _ env _ (C x) typ-lit = Cst x by typv-cst
eval Γ env Γ⊨env (V i) typ-var = lookup env i by env-lookup Γ⊨env i
eval _ env Γ⊨env (λ' e) (typ-abs {A = A} {B = B} A∷Γ⊢e∈B) =
  Clo env e by typv-clo Γ⊨env A∷Γ⊢e∈B
eval Γ env Γ⊨env (e₁ $ e₂) (typ-app {A = A} {B = B} Γ⊢e₁∈A=>B Γ⊢e₂∈A) =
  unwrap (eval Γ env Γ⊨env e₁ Γ⊢e₁∈A=>B) k
    --{! eval (A ∷ Γ) {! right ∷ env !} {!!} {! body !} {!!} !}
  where
    unwrap : ∀{T : Set} → TypedVal Base (A => B) →
      (∀{n} → Env Base n → Tm Base (Nat.suc n) → T) → T
    unwrap (Clo env e by typv-clo Γ⊨env A∷Γ⊢e∈B) f = f env e

    k : ∀{n} → Env Base n → Tm Base (Nat.suc n) → TypedVal Base B
    k env' body =
      let v by v∈A = eval Γ env Γ⊨env e₂ Γ⊢e₂∈A
       in eval (A ∷ Γ) (v ∷ env) {!!} {! body !} {!!}
eval _ env _ (Let e₁ e₂) _ = {! !}
eval _ env _ (e₁ + e₂) _ = {! !}
