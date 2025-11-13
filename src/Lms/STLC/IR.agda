module Lms.STLC.IR where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _<_)
open import Data.Nat.Properties as Nat
open import Data.Vec as Vec
  using (Vec; _∷_; [])
  renaming (_++_ to _⧺_)
open import Data.Vec.Extensions as Vec
open import Data.Product as Prod
open import Data.Empty as Void
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Data.Context as Context hiding (Ctx)

open import Lms.STLC.Core

private variable
  n n' n'' m i n₁ n₂ : ℕ

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
  constructor [_,_]
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

data _[_]↦_ : Env n → ℕ → Val → Set where
  here : ∀ {env : Env n} {v} → (v ∷ env)[ n ]↦ v
  there : ∀{v v'} → env [ i ]↦ v → (v' ∷ env)[ i ]↦ v

[]↦→< : ∀ {env : Env n} {v} → env [ i ]↦ v → i < n
[]↦→< here = n<1+n _
[]↦→< (there p) = m<n⇒m<1+n ([]↦→< p)

[]↦-unique : ∀{v v'} → env [ i ]↦ v → env [ i ]↦ v' → v ≡ v'
[]↦-unique here here = refl
[]↦-unique here (there p) = ⊥-elim (<-irrefl refl ([]↦→< p))
[]↦-unique (there p) here = ⊥-elim (<-irrefl refl ([]↦→< p))
[]↦-unique (there p) (there p') = []↦-unique p p'

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
    env ⊢v e₁ ⇓ Closureₐ env' es body →
    env ⊢v e₂ ⇓ arg →
    (arg ∷ env') ⊢ts es ⇓ vs →
    env'' ⊢v body ⇓ v →
    env ⊢t e₁ $ₐ e₂ ⇓ v

data _⊢ts_⇓_ where
  eval-nil : env ⊢ts [] ⇓ []
  eval-cons : ∀{ts : Vec Expr n} {vs t v} →
    vs ⧺ env ≡ env' →
    env ⊢ts ts ⇓ vs → env' ⊢t t ⇓ v →
    env ⊢ts t ∷ ts ⇓ v ∷ vs

ts⇓-join : ∀{ts₁ : Vec Expr n₁} {ts₂ : Vec Expr n₂} {vs₁ vs₂} →
  env ⊢ts ts₁ ⇓ vs₁ →
  vs₁ ⧺ env ⊢ts ts₂ ⇓ vs₂ →
  env ⊢ts ts₂ ⧺ ts₁ ⇓ vs₂ ⧺ vs₁
ts⇓-join ts₁⇓ eval-nil = ts₁⇓
ts⇓-join {env = env} {vs₁ = vs₁} ts₁⇓ (eval-cons {t = t} {v} refl ts₂⇓ t⇓) =
  eval-cons refl (ts⇓-join ts₁⇓ ts₂⇓)
    (≅-subst (_⊢t t ⇓ v) (≅-symmetric (≅-++-assoc _ vs₁ env)) t⇓)

wk-v⇓ : ∀{a v} v' → env ⊢v a ⇓ v → v' ∷ env ⊢v a ⇓ v
wk-v⇓ v' (eval-c x) = eval-c x
wk-v⇓ v' (eval-v x) = eval-v (there x)

extend-v⇓ : ∀{env : Env n} {env' : Env n'} {a v} →
  env ⊆ env' → env ⊢v a ⇓ v → env' ⊢v a ⇓ v
extend-v⇓ (⊆-refl _) a⇓v = a⇓v
extend-v⇓ (⊆-cons t env⊆env') a⇓v = wk-v⇓ t (extend-v⇓ env⊆env' a⇓v)

_⊢p_⇓_ : Env n → Prog → Val → Set
env ⊢p [ ts , e ] ⇓ v = ∃[ vs ] (env ⊢ts ts ⇓ vs × vs ⧺ env ⊢v e ⇓ v)

v⇓-unique : ∀{a v v'} → env ⊢v a ⇓ v → env ⊢v a ⇓ v' → v ≡ v'
v⇓-unique (eval-c x) (eval-c .x) = refl
v⇓-unique (eval-v env[i]=v) (eval-v env[i]=v') = []↦-unique env[i]=v env[i]=v'

t⇓-unique : ∀{t v v'} → env ⊢t t ⇓ v → env ⊢t t ⇓ v' → v ≡ v'
ts⇓-unique : ∀{ts} {vs vs' : Env m} →
  env ⊢ts ts ⇓ vs → env ⊢ts ts ⇓ vs' → vs ≡ vs'

t⇓-unique (eval-+ refl e₁⇓ e₂⇓) (eval-+ refl e₁⇓' e₂⇓')
  with refl ← v⇓-unique e₁⇓ e₁⇓'
  with refl ← v⇓-unique e₂⇓ e₂⇓' = refl
t⇓-unique eval-λ eval-λ = refl
t⇓-unique (eval-$ refl e₁⇓ e₂⇓ es⇓ a⇓) (eval-$ refl e₁⇓' e₂⇓' es⇓' a⇓')
  with refl ← v⇓-unique e₁⇓ e₁⇓'
  with refl ← v⇓-unique e₂⇓ e₂⇓'
  with refl ← ts⇓-unique es⇓ es⇓'
  with refl ← v⇓-unique a⇓ a⇓' = refl

ts⇓-unique eval-nil eval-nil = refl
ts⇓-unique (eval-cons refl ts⇓ t⇓) (eval-cons refl ts⇓' t⇓')
  with refl ← ts⇓-unique ts⇓ ts⇓'
  with refl ← t⇓-unique t⇓ t⇓' = refl
