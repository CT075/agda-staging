module Anf.STLC where

open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _*_)
open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Vec.Properties using (reverse-∷)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl; trans)

open import Data.Gas
open import Data.Vec.Extensions

private variable
  T : Set
  n : ℕ

data Typ : Set where
  N : Typ
  _=>_ : Typ → Typ → Typ

Ctx : ℕ → Set
Ctx = Vec Typ

data Tm : {n : ℕ} → Typ → Ctx n → Set where
  -- STLC
  C : ∀{Γ} → ℕ → Tm {n} N Γ
  V : ∀{Γ τ} → (i : Fin n) → {rlookup Γ i ≡ τ} → Tm τ Γ
  λ' : ∀{τ₂} {Γ : Ctx n} → (τ₁ : Typ) → Tm τ₂ (τ₁ ∷ Γ) → Tm (τ₁ => τ₂) Γ
  _$_ : ∀{τ₁ τ₂} {Γ : Ctx n} → Tm (τ₁ => τ₂) Γ → Tm τ₁ Γ → Tm τ₂ Γ

  -- Cut
  Let : ∀{τ₁ τ₂} {Γ : Ctx n} → Tm τ₁ Γ → Tm τ₂ (τ₁ ∷ Γ) → Tm τ₂ Γ

  -- Nat
  _+'_ : ∀{Γ : Ctx n} → Tm N Γ → Tm N Γ → Tm N Γ
  _*'_ : ∀{Γ : Ctx n} → Tm N Γ → Tm N Γ → Tm N Γ

data Env : Ctx n → Set where
  nil : Env []
  cons : ∀{τ} {Γ : Ctx n} → Tm τ Γ → Env Γ → Env (τ ∷ Γ)
