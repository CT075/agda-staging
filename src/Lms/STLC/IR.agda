module Lms.STLC.IR where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec
  using (Vec; _∷_; [])
  renaming (_++_ to _++ᵥ_)
open import Data.List as List
  using (List)
  renaming (_∷_ to _∷ₗ_; [] to nilₗ; _++_ to _++ₗ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Context as Context using (_[_]=_)

open import Lms.STLC.Core

private variable
  n n' i : ℕ

data Atom : Set where
  Cₐ : ℕ → Atom
  Vₐ : ℕ → Atom

data Expr : Set where
  _+ₐ_ : Atom → Atom → Expr
  _$ₐ_ : Atom → Atom → Expr
  λₐ : Typ Base → List Expr → Atom → Expr

infix 4 _⊢v_∈_
data _⊢v_∈_ : Ctx Base n → Atom → Typ Base → Set where
  anf-c : ∀{Γ : Ctx Base n} x → Γ ⊢v Cₐ x ∈ N
  anf-v : ∀{Γ : Ctx Base n} {i τ} → Γ [ i ]= τ → Γ ⊢v Vₐ i ∈ τ

infix 4 _⊢t_∈_
infix 4 _⊢ts_∈_
data _⊢t_∈_ : Ctx Base n → Expr → Typ Base → Set
data _⊢ts_∈_ : Ctx Base n → List Expr → Ctx Base n' → Set

data _⊢t_∈_ where
  anf-+ : ∀{Γ : Ctx Base n} {e₁ e₂} →
    Γ ⊢v e₁ ∈ N → Γ ⊢v e₂ ∈ N →
    Γ ⊢t e₁ +ₐ e₂ ∈ N
  anf-λ : ∀{Γ : Ctx Base n} {Γ' : Ctx Base n'} {Γs : Ctx Base (n' + n)}
    τ {τ' es v} →
    Γ' ++ᵥ Γ ≡ Γs →
    τ ∷ Γ ⊢ts es ∈ Γ' → τ ∷ Γs ⊢v v ∈ τ' →
    Γ ⊢t λₐ τ es v ∈ τ => τ'
  anf-$ : ∀{Γ : Ctx Base n} {e₁ e₂ τ₁ τ₂} →
    Γ ⊢v e₁ ∈ τ₁ => τ₂ → Γ ⊢v e₂ ∈ τ₁ →
    Γ ⊢t e₁ $ₐ e₂ ∈ τ₂

data _⊢ts_∈_ where
  anf-nil : ∀{Γ : Ctx Base n} → Γ ⊢ts nilₗ ∈ []
  anf-cons : ∀{Γ : Ctx Base n} {Γ' : Ctx Base n'} {Γs : Ctx Base (n' + n)}
    {x xs τ} →
    Γ' ++ᵥ Γ ≡ Γs →
    Γ ⊢ts xs ∈ Γ' → Γs ⊢t x ∈ τ →
    Γ ⊢ts x ∷ₗ xs ∈ τ ∷ Γ'

data Val : Set where
  Constₐ : ℕ → Val
  Closureₐ : List Val → List Expr → Atom → Val

private variable
  env env' env'' : List Val

data _[_]↦_ : List Val → ℕ → Val → Set where
  here : ∀{v} → List.length env ≡ n → (v ∷ₗ env) [ n ]↦ v
  there : ∀{v v'} → env [ i ]↦ v → (v' ∷ₗ env)[ i ]↦ v

infix 4 _⊢v_⇓_
data _⊢v_⇓_ : List Val → Atom → Val → Set where
  eval-c : ∀ x → env ⊢v Cₐ x ⇓ Constₐ x
  eval-v : ∀{v} → env [ i ]↦ v → env ⊢v Vₐ i ⇓ v

infix 4 _⊢t_⇓_
infix 4 _⊢ts_⇓_

data _⊢t_⇓_ : List Val → Expr → Val → Set
data _⊢ts_⇓_ : List Val → List Expr → List Val → Set

data _⊢t_⇓_ where
  eval-+ : ∀{e₁ e₂ x₁ x₂ x} →
    x₁ + x₂ ≡ x →
    env ⊢v e₁ ⇓ Constₐ x₁ → env ⊢v e₂ ⇓ Constₐ x₂ →
    env ⊢t e₁ +ₐ e₂ ⇓ Constₐ x
  eval-λ : ∀{τ ts v} → env ⊢t λₐ τ ts v ⇓ Closureₐ env ts v
  eval-$ : ∀{e₁ e₂ vs es body arg v} →
    vs ++ₗ arg ∷ₗ env' ≡ env'' →
    env ⊢v e₁ ⇓ Closureₐ env' es body → env ⊢v e₂ ⇓ arg →
    (arg ∷ₗ env') ⊢ts es ⇓ vs →
    env'' ⊢v body ⇓ v →
    env ⊢t e₁ $ₐ e₂ ⇓ v

data _⊢ts_⇓_ where
  eval-nil : env ⊢ts nilₗ ⇓ nilₗ
  eval-cons : ∀{ts vs t v} →
    vs ++ₗ env ≡ env' →
    env ⊢ts ts ⇓ vs → env' ⊢t t ⇓ v →
    env ⊢ts t ∷ₗ ts ⇓ v ∷ₗ vs
