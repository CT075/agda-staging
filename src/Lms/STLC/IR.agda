module Lms.STLC.IR where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec
  using (Vec; _∷_; [])
  renaming (_++_ to _⧺_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Context as Context using (_[_]=_)

open import Lms.STLC.Core

private variable
  n n' n'' m i : ℕ

data Atom : Set where
  Cₐ : ℕ → Atom
  Vₐ : ℕ → Atom

data Expr : Set where
  _+ₐ_ : Atom → Atom → Expr
  _$ₐ_ : Atom → Atom → Expr
  λₐ : Typ Base → Vec Expr n → Atom → Expr

infix 4 _⊢v_∈_
data _⊢v_∈_ : Ctx Base n → Atom → Typ Base → Set where
  anf-c : ∀{Γ : Ctx Base n} x → Γ ⊢v Cₐ x ∈ N
  anf-v : ∀{Γ : Ctx Base n} {i τ} → Γ [ i ]= τ → Γ ⊢v Vₐ i ∈ τ

infix 4 _⊢t_∈_
infix 4 _⊢ts_∈_
data _⊢t_∈_ : Ctx Base n → Expr → Typ Base → Set
data _⊢ts_∈_ : Ctx Base n → Vec Expr m → Ctx Base m → Set

data _⊢t_∈_ where
  anf-+ : ∀{Γ : Ctx Base n} {e₁ e₂} →
    Γ ⊢v e₁ ∈ N → Γ ⊢v e₂ ∈ N →
    Γ ⊢t e₁ +ₐ e₂ ∈ N
  anf-λ : ∀{Γ : Ctx Base n} {Γ' : Ctx Base n'} {Γs : Ctx Base _}
    τ {τ' es v} →
    Γ' ⧺ τ ∷ Γ ≡ Γs →
    τ ∷ Γ ⊢ts es ∈ Γ' → Γs ⊢v v ∈ τ' →
    Γ ⊢t λₐ τ es v ∈ τ => τ'
  anf-$ : ∀{Γ : Ctx Base n} {e₁ e₂ τ₁ τ₂} →
    Γ ⊢v e₁ ∈ τ₁ => τ₂ → Γ ⊢v e₂ ∈ τ₁ →
    Γ ⊢t e₁ $ₐ e₂ ∈ τ₂

data _⊢ts_∈_ where
  anf-nil : ∀{Γ : Ctx Base n} → Γ ⊢ts [] ∈ []
  anf-cons : ∀{Γ : Ctx Base n} {Γ' : Ctx Base n'} {Γs : Ctx Base (n' + n)}
    {x xs τ} →
    Γ' ⧺ Γ ≡ Γs →
    Γ ⊢ts xs ∈ Γ' → Γs ⊢t x ∈ τ →
    Γ ⊢ts x ∷ xs ∈ τ ∷ Γ'

record Prog : Set where
  constructor MkProg
  field
    {stepc} : ℕ
    steps : Vec Expr stepc
    result : Atom

data Val : Set where
  Constₐ : ℕ → Val
  Closureₐ : Context.Ctx Val n → Vec Expr m → Atom → Val

Env = Context.Ctx Val

private variable
  env : Env n
  env' : Env n'
  env'' : Env n''

data _[_]↦_ : Vec Val n → ℕ → Val → Set where
  here : ∀{env : Vec Val n} {v} → (v ∷ env)[ n ]↦ v
  there : ∀{v v'} → env [ i ]↦ v → (v' ∷ env)[ i ]↦ v

infix 4 _⊢v_⇓_
data _⊢v_⇓_ : Env n → Atom → Val → Set where
  eval-c : ∀ x → env ⊢v Cₐ x ⇓ Constₐ x
  eval-v : ∀{v} → env [ i ]↦ v → env ⊢v Vₐ i ⇓ v

infix 4 _⊢t_⇓_
infix 4 _⊢ts_⇓_

data _⊢t_⇓_ : Env n → Expr → Val → Set
data _⊢ts_⇓_ : Env n → Vec Expr m → Vec Val m → Set

data _⊢t_⇓_ where
  eval-+ : ∀{e₁ e₂ x₁ x₂ x} →
    x₁ + x₂ ≡ x →
    env ⊢v e₁ ⇓ Constₐ x₁ → env ⊢v e₂ ⇓ Constₐ x₂ →
    env ⊢t e₁ +ₐ e₂ ⇓ Constₐ x
  eval-λ : ∀{τ} {ts : Vec Expr m} {v} → env ⊢t λₐ τ ts v ⇓ Closureₐ env ts v
  eval-$ : ∀{e₁ e₂} {es : Vec Expr m} {vs body arg v} →
    vs ⧺ arg ∷ env' ≡ env'' →
    env ⊢v e₁ ⇓ Closureₐ env' es body → env ⊢v e₂ ⇓ arg →
    (arg ∷ env') ⊢ts es ⇓ vs →
    env'' ⊢v body ⇓ v →
    env ⊢t e₁ $ₐ e₂ ⇓ v

data _⊢ts_⇓_ where
  eval-nil : env ⊢ts [] ⇓ []
  eval-cons : ∀{ts : Vec Expr n} {vs t v} →
    vs ⧺ env ≡ env' →
    env ⊢ts ts ⇓ vs → env' ⊢t t ⇓ v →
    env ⊢ts t ∷ ts ⇓ v ∷ vs
