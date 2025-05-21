module Lms where

open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)
open import Data.List as List using (List) renaming (_∷_ to cons; [] to nil)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Source

data Typ : Set where
  N : Typ
  _→'_ : Typ → Typ → Typ
  Rep : Typ → Typ

Ctx : ℕ → Set
Ctx = Vec Typ

data Tm : {n : ℕ} → Typ → Ctx n → Set where
  -- STLC
  V : ∀{n Γ} → (i : Fin n) → Tm (lookup Γ i) Γ
  λ' : ∀{n τ₂} {Γ : Ctx n} → (τ₁ : Typ) → Tm τ₂ (τ₁ ∷ Γ) → Tm (τ₁ →' τ₂) Γ
  _$_ : ∀{n τ₁ τ₂} {Γ : Ctx n} → Tm (τ₁ →' τ₂) Γ → Tm τ₁ Γ → Tm τ₂ Γ

  -- Nat
  _+_ : ∀{n} {Γ : Ctx n} → Tm N Γ → Tm N Γ → Tm N Γ

  -- Rep
  lift : ∀{n τ} {Γ : Ctx n} → Tm τ Γ → Tm (Rep τ) Γ
  _++_ : ∀{n} {Γ : Ctx n} → Tm (Rep N) Γ → Tm (Rep N) Γ → Tm (Rep N) Γ

-- TODO: Internal representation of Rep-structures
data Vl : Typ → Set where
  C : ℕ → Vl N

-- TODO: split this into staged and unstaged versions of the STLC

forgetTy : Typ → Typ
forgetTy N = N
forgetTy (τ₁ →' τ₂) = forgetTy τ₁ →' forgetTy τ₂
forgetTy (Rep τ) = forgetTy τ

forgetCtx : ∀{n} → Ctx n → Ctx n
forgetCtx = Vec.map forgetTy

postulate
  forgetCtx-lemma : ∀ {n} (Γ : Ctx n) i →
    forgetTy (lookup Γ i) ≡ lookup (forgetCtx Γ) i

forgetTm : ∀{n τ} {Γ : Ctx n} → Tm τ Γ → Tm (forgetTy τ) (forgetCtx Γ)
forgetTm (V {n} {Γ} i) rewrite forgetCtx-lemma Γ i = V {n} {forgetCtx Γ} i
forgetTm (λ' τ e) = λ' (forgetTy τ) (forgetTm e)
forgetTm (e₁ $ e₂) = forgetTm e₁ $ forgetTm e₂
forgetTm (e₁ + e₂) = forgetTm e₁ + forgetTm e₂
forgetTm (lift e) = forgetTm e
forgetTm (e₁ ++ e₂) = forgetTm e₁ + forgetTm e₂

evalStlc : ∀{τ} → Tm τ [] → Vl τ
evalStlc = {!!}

-- Target

-- XXX: Is Stack even a good target here?

mutual
  data Op : Set where
    Push : ℕ → Op
    Add : Op
    Func : ℕ → Stk → Op

  Stk : Set
  Stk = List Op

-- Denotation of stack programs is, as usual, functions of type List ℕ → List ℕ
Denot : Set
Denot = List ℕ → List ℕ

-- Correctness

denot : Stk → Denot
denot = {!!}

-- TODO: this should only be allowed on STLC terms with no Reps
denotStlc : ∀{n τ} {Γ : Ctx n} → Tm τ Γ → Denot
denotStlc = {!!}

repToStack : ∀{τ} → Vl τ → Stk
repToStack = {!!}

-- XXX: since `Denot` is a function type, we should probably phrase this
-- extensionally
correct : ∀{τ} → (t : Tm τ []) → denot (repToStack (evalStlc t)) ≡ denotStlc (forgetTm t)
correct = {!!}

-- TODO: How to make this generic over the second lang?

