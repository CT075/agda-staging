module Lms.STLC where

open import Data.Vec as Vec
  using (Vec; _∷_; [])
  renaming (_++_ to _++ᵥ_)
open import Data.List as List
  using (List)
  renaming (_∷_ to _∷ₗ_; [] to nilₗ; _++_ to _++ₗ_)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Product as Prod using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl)

open import Data.Context as Context using (_[_]=_)
open import Data.Store as Store using (Store; cons; nil; store-lookup-syntax)
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
Ctx w = Context.Ctx (Typ w)

-- We use De Bruijin levels with *reversed* contexts. That is, index 0 refers
-- to the rightmost element of `Γ`. This is because Agda is better-behaved when
-- we use the constructor `∷` instead of the recursive function `∷ʳ` in type
-- formers.
data Tm : (w : W) → {n : ℕ} → Typ w → Ctx w n → Set where
  -- STLC
  C : ∀{Γ} → ℕ → Tm w {n} N Γ
  V : ∀{Γ : Ctx w n} {τ} → (i : ℕ) → Γ [ i ]= τ → Tm w τ Γ
  λ' : ∀(τ₁ : Typ w) {τ₂} {Γ : Ctx w n} → Tm w τ₂ (τ₁ ∷ Γ) → Tm w (τ₁ => τ₂) Γ
  _$_ : ∀{τ₁ τ₂} {Γ : Ctx w n} → Tm w (τ₁ => τ₂) Γ → Tm w τ₁ Γ → Tm w τ₂ Γ

  -- Cut
  Let : ∀{τ₁ τ₂} {Γ : Ctx w n} → Tm w τ₁ Γ → Tm w τ₂ (τ₁ ∷ Γ) → Tm w τ₂ Γ

  -- Nat
  _+'_ : ∀{Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ

  CC : ∀{Γ} → Tm Staged N Γ → Tm Staged {n} (Rep N) Γ
  λλ : ∀ τ₁ {τ₂ bτ₁ bτ₂} {Γ : Ctx Staged n} → {IsBase bτ₁ τ₁} → {IsBase bτ₂ τ₂} →
    Tm Staged (τ₁ => τ₂) Γ → Tm Staged (Rep (bτ₁ => bτ₂)) Γ
  _++_ : ∀{Γ : Ctx Staged n} →
    Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ
  _$$_ : ∀{τ₁ τ₂} {Γ : Ctx Staged n} →
    Tm Staged (Rep (τ₁ => τ₂)) Γ → Tm Staged (Rep τ₁) Γ → Tm Staged (Rep τ₂) Γ

data AnfVal : Set where
  Constₐ : ℕ → AnfVal
  Varₐ : ℕ → AnfVal

data AnfTm : Set where
  _+ₐ_ : AnfVal → AnfVal → AnfTm
  _$ₐ_ : AnfVal → AnfVal → AnfTm
  λₐ : Typ Base → List AnfTm → AnfVal → AnfTm

infix 4 _⊢v_∈_
data _⊢v_∈_ : Ctx Base n → AnfVal → Typ Base → Set where
  anf-c : ∀{Γ : Ctx Base n} x → Γ ⊢v Constₐ x ∈ N
  anf-v : ∀{Γ : Ctx Base n} {i τ} → Γ [ i ]= τ → Γ ⊢v Varₐ i ∈ τ

infix 4 _⊢t_∈_
infix 4 _⊢ts_∈_
data _⊢t_∈_ : Ctx Base n → AnfTm → Typ Base → Set
data _⊢ts_∈_ : Ctx Base n → List AnfTm → Ctx Base n' → Set

data _⊢t_∈_ where
  anf-+ : ∀{Γ : Ctx Base n} {e₁ e₂} →
    Γ ⊢v e₁ ∈ N → Γ ⊢v e₂ ∈ N →
    Γ ⊢t e₁ +ₐ e₂ ∈ N
  anf-$ : ∀{Γ : Ctx Base n} {e₁ e₂ τ₁ τ₂} →
    Γ ⊢v e₁ ∈ τ₁ => τ₂ → Γ ⊢v e₂ ∈ τ₁ →
    Γ ⊢t e₁ +ₐ e₂ ∈ τ₂
  anf-λ : ∀{Γ : Ctx Base n} {Γ' : Ctx Base n'} {τ τ' es v} →
    Γ ⊢ts es ∈ Γ' → τ ∷ Γ' ⊢v v ∈ τ' →
    Γ ⊢t λₐ τ es v ∈ τ => τ'

data _⊢ts_∈_ where
  anf-nil : ∀{Γ : Ctx Base n} → Γ ⊢ts nilₗ ∈ []
  anf-cons : ∀{Γ : Ctx Base n} {Γ' : Ctx Base n'} {x xs τ} →
    Γ ⊢ts xs ∈ Γ' → Γ' ⊢t x ∈ τ →
    Γ ⊢ts x ∷ₗ xs ∈ τ ∷ Γ'

Env : Ctx w n → Set
data Val : (w : W) → Typ w → Set

Env {w = w} Γ = Store (Typ w) (Val w) Γ

data Val where
  Const : ℕ → Val w N
  Closure : ∀{τ₁ τ₂} {Γ : Ctx w n} →
    (env : Env Γ) → Tm w τ₂ (τ₁ ∷ Γ) →
    Val w (τ₁ => τ₂)
  Code : ∀ τ → AnfVal → Val Staged (Rep τ)

infix 4 _⊢_⇓_
data _⊢_⇓_ : ∀{τ} {Γ : Ctx Base n} → Env Γ → Tm Base τ Γ → Val Base τ → Set where
  eval-C : ∀{Γ : Ctx Base n} {env : Env Γ} x → env ⊢ C x ⇓ Const x
  eval-V : ∀{Γ : Ctx Base n} {env : Env Γ} {τ} i {p} v → env [ i ]↦ v ∈ τ →
    env ⊢ V i p ⇓ v
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
    env ⊢ e₁ ⇓ Const x₁ → env ⊢ e₂ ⇓ Const x₂ → v ≡ x₁ + x₂ →
    env ⊢ e₁ +' e₂ ⇓ Const v

private variable
  fresh fresh' fresh'' fresh''' : ℕ
  ts ts₁ ts₂ ts₃ : List AnfTm

infix 4 _⊢⟨_,_⟩⇓⟨[_,_],_⟩
data _⊢⟨_,_⟩⇓⟨[_,_],_⟩ : ∀{τ} {Γ : Ctx Staged n} →
  -- variable store
  Env Γ →
  -- term to evaluate + fresh var counter
  Tm Staged τ Γ → ℕ →
  -- lifted ANF terms + result + new fresh counter
  List AnfTm → Val Staged τ → ℕ →
  Set
  where
  evalms-C : ∀ {Γ : Ctx Staged n} {env : Env Γ} x →
    env ⊢⟨ C x , fresh ⟩⇓⟨[ nilₗ , Const x ], fresh ⟩
  evalms-V : ∀ {Γ : Ctx Staged n} {env : Env Γ} {τ} i {p} v → env [ i ]↦ v ∈ τ →
    env ⊢⟨ V i p , fresh ⟩⇓⟨[ nilₗ , v ], fresh ⟩
  evalms-λ : ∀ {Γ : Ctx Staged n} {env : Env Γ} {τ τ'}
    {e : Tm Staged τ' (τ ∷ Γ)} →
    env ⊢⟨ λ' τ e , fresh ⟩⇓⟨[ nilₗ , Closure env e ], fresh ⟩
  evalms-$ : ∀ {τ₁ τ₂ ts₁ ts₂ ts₃}
    {Γ : Ctx Staged n} {env : Env Γ}
    {Γ' : Ctx Staged n'} {env' : Env Γ'}
    {e₁ : Tm Staged (τ₁ => τ₂) Γ} {e₂ x e' v} →
    env ⊢⟨ e₁ , fresh ⟩⇓⟨[ ts₁ , Closure env' e' ], fresh' ⟩ →
    env ⊢⟨ e₂ , fresh' ⟩⇓⟨[ ts₂ , x ], fresh'' ⟩ →
    (cons x env') ⊢⟨ e' , fresh'' ⟩⇓⟨[ ts₃ , v ], fresh''' ⟩ →
    env ⊢⟨ e₁ $ e₂ , fresh ⟩⇓⟨[ ts₃ ++ₗ ts₂ ++ₗ ts₁ , v ], fresh''' ⟩
  evalms-let : ∀ {Γ : Ctx Staged n} {env : Env Γ} {τ₁ τ₂}
    {e₁ : Tm Staged τ₁ Γ} {e₂ : Tm Staged τ₂ _} {x v} →
    env ⊢⟨ e₁ , fresh ⟩⇓⟨[ ts₁ , x ], fresh' ⟩ →
    (cons x env) ⊢⟨ e₂ , fresh' ⟩⇓⟨[ ts₂ , v ], fresh'' ⟩ →
    env ⊢⟨ Let e₁ e₂ , fresh ⟩⇓⟨[ ts₂ ++ₗ ts₁ , v ], fresh'' ⟩
  evalms-+ : ∀ {Γ : Ctx Staged n} {env : Env Γ} {e₁ e₂ x₁ x₂ v} → v ≡ x₁ + x₂ →
    env ⊢⟨ e₁ , fresh ⟩⇓⟨[ ts₁ , Const x₁ ], fresh' ⟩ →
    env ⊢⟨ e₂ , fresh' ⟩⇓⟨[ ts₂ , Const x₂ ], fresh'' ⟩ →
    env ⊢⟨ e₁ +' e₂ , fresh ⟩⇓⟨[ ts₂ ++ₗ ts₁ , Const v ], fresh'' ⟩

  evalms-CC : ∀ {Γ : Ctx Staged n} {env : Env Γ} {e x} →
    env ⊢⟨ e , fresh ⟩⇓⟨[ ts , Const x ], fresh' ⟩ →
    env ⊢⟨ CC e , fresh ⟩⇓⟨[ ts , Code N (Constₐ x) ], fresh' ⟩
  --evalms-λλ

  evalms-++ : ∀{Γ : Ctx Staged n} {env : Env Γ} {e₁ e₂ a₁ a₂} →
    env ⊢⟨ e₁ , fresh ⟩⇓⟨[ ts₁ , Code N a₁ ], fresh' ⟩ →
    env ⊢⟨ e₂ , fresh' ⟩⇓⟨[ ts₂ , Code N a₂ ], fresh'' ⟩ →
    env ⊢⟨ e₁ ++ e₂ , fresh ⟩⇓⟨[
        (a₁ +ₐ a₂) ∷ₗ ts₂ ++ₗ ts₁ , Code N (Varₐ fresh'')
      ],
      suc fresh'' ⟩
