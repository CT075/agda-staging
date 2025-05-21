-- This file is a basic LMS-style staged calculus with an associated correctness
-- theorem, where the host language (STLC equipped with Nat and Rep) lowers to
-- the STLC with just Nat.

module LiftNat where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Vec.Bounded as Vec≤ using (Vec≤)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)
open import Data.List as List using (List) renaming (_∷_ to cons; [] to nil)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
  _→'_ : ∀{w} → Typ w → Typ w → Typ w
  -- By including a `dW w` term, we can't even utter the type `Rep` in the
  -- base language.
  Rep : ∀{w} → {dW w} → Typ w → Typ w

Ctx : W → ℕ → Set
Ctx w = Vec (Typ w)

data Tm : {n : ℕ} → (w : W) → Typ w → Ctx w n → Set where
  -- STLC
  C : ∀{n w} {Γ : Ctx w n} → (x : ℕ) → Tm w N Γ
  V : ∀{n w Γ} → (i : Fin n) → Tm w (lookup Γ i) Γ
  λ' : ∀{n w τ₂} {Γ : Ctx w n} →
    (τ₁ : Typ w) → Tm w τ₂ (τ₁ ∷ Γ) →
    Tm w (τ₁ →' τ₂) Γ
  _$_ : ∀{n w τ₁ τ₂} {Γ : Ctx w n} →
    Tm w (τ₁ →' τ₂) Γ → Tm w τ₁ Γ →
    Tm w τ₂ Γ

  -- Nat
  _+_ : ∀{n w} {Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ

  -- Rep
  liftN : ∀{n} {Γ : Ctx Staged n} → Tm Staged N Γ → Tm Staged (Rep N) Γ
  _++_ : ∀{n} {Γ : Ctx Staged n} →
    Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ →
    Tm Staged (Rep N) Γ

postulate
  -- blah blah blah
  weaken : ∀{n w τ'} {Γ : Ctx w n} τ → Tm w τ' Γ → Tm w τ' (τ ∷ Γ)

-- Target

-- In this case, we're already using `Tm Base` as the target.

-- Evaluation and correctness

forgetTy : Typ Staged → Typ Base
forgetTy N = N
forgetTy (τ₁ →' τ₂) = forgetTy τ₁ →' forgetTy τ₂
forgetTy (Rep τ) = forgetTy τ

forgetCtx : ∀{n} → Ctx Staged n → Ctx Base n
forgetCtx = Vec.map forgetTy

postulate
  forget-lookup : ∀ {n} (Γ : Ctx Staged n) i →
    forgetTy (lookup Γ i) ≡ lookup (forgetCtx Γ) i

forgetTm : ∀{n τ} {Γ : Ctx Staged n} → Tm Staged τ Γ → Tm Base (forgetTy τ) (forgetCtx Γ)
forgetTm (C n) = C n
forgetTm (V {n} {_} {Γ} i) rewrite forget-lookup Γ i = V {n} {_} {forgetCtx Γ} i
forgetTm (λ' τ e) = λ' (forgetTy τ) (forgetTm e)
forgetTm (e₁ $ e₂) = forgetTm e₁ $ forgetTm e₂
forgetTm (e₁ + e₂) = forgetTm e₁ + forgetTm e₂
forgetTm (liftN e) = forgetTm e
forgetTm (e₁ ++ e₂) = forgetTm e₁ + forgetTm e₂

T[_]⟦_⟧ : ∀{n w} → Ctx w n → Typ w → Set
T[ Γ ]⟦ N ⟧ = ℕ
T[ Γ ]⟦ τ₁ →' τ₂ ⟧ = T[ Γ ]⟦ τ₁ ⟧ → T[ Γ ]⟦ τ₂ ⟧
-- This is incorrect as-written
T[_]⟦_⟧ {_} {Staged} Γ (Rep τ) = Tm Base (forgetTy τ) (forgetCtx Γ)

-- XXX: include a store
⟦_⟧ : ∀{n w} {τ : Typ w} {Γ : Ctx w n} → Tm w τ Γ → T[ Γ ]⟦ τ ⟧
⟦ C x ⟧ = x
⟦ V i ⟧ = {! !}
⟦ λ' τ₁ e ⟧ = {! !}
⟦ e₁ $ e₂ ⟧ = ⟦ e₁ ⟧ ⟦ e₂ ⟧
⟦ e₁ + e₂ ⟧ = Nat._+_ ⟦ e₁ ⟧ ⟦ e₂ ⟧
-- this is the interesting case in the heterogeneous case
⟦ liftN e ⟧ = C ⟦ e ⟧
⟦ e₁ ++ e₂ ⟧ = ⟦ e₁ ⟧ + ⟦ e₂ ⟧

-- Having difficulty even stating this in Agda...
correct : ∀ {n τ} {Γ : Ctx Staged n} (e : Tm Staged (Rep τ) []) → ⟦ ⟦ e ⟧ ⟧ ≡ ⟦ forgetTm e ⟧
correct (e₁ $ e₂) = {!!}
correct (liftN e) = {!!}
correct (e₁ ++ e₂) = {!!}
