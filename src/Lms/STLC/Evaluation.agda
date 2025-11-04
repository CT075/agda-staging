module Lms.STLC.Evaluation where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec using (_∷_)
open import Data.List as List
  using (List)
  renaming (_∷_ to _∷ₗ_; [] to nilₗ; _++_ to _++ₗ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Store as Store using (Store; cons; nil; store-lookup-syntax)

open import Lms.STLC.Core
open import Lms.STLC.IR as IR renaming (Expr to AnfExpr) hiding (Val)

private variable
  n n' : ℕ
  w : W

Env : Ctx w n → Set
data Val : (w : W) → Typ w → Set

Env {w = w} Γ = Store (Typ w) (Val w) Γ

data Val where
  Const : ℕ → Val w N
  Closure : ∀{τ₁ τ₂} {Γ : Ctx w n} →
    (env : Env Γ) → Tm w τ₂ (τ₁ ∷ Γ) →
    Val w (τ₁ => τ₂)
  Code : ∀ τ → Atom → Val Staged (Rep τ)

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
  ts ts₁ ts₂ ts₃ : List AnfExpr

infix 4 _⊢⟨_,_⟩⇓⟨[_,_],_⟩
data _⊢⟨_,_⟩⇓⟨[_,_],_⟩ : ∀{τ} {Γ : Ctx Staged n} →
  -- variable store
  Env Γ →
  -- term to evaluate + fresh var counter
  Tm Staged τ Γ → ℕ →
  -- lifted ANF terms + result + new fresh counter
  List AnfExpr → Val Staged τ → ℕ →
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
    env ⊢⟨ CC e , fresh ⟩⇓⟨[ ts , Code N (Cₐ x) ], fresh' ⟩
  --evalms-λλ

  evalms-++ : ∀{Γ : Ctx Staged n} {env : Env Γ} {e₁ e₂ a₁ a₂} →
    env ⊢⟨ e₁ , fresh ⟩⇓⟨[ ts₁ , Code N a₁ ], fresh' ⟩ →
    env ⊢⟨ e₂ , fresh' ⟩⇓⟨[ ts₂ , Code N a₂ ], fresh'' ⟩ →
    env ⊢⟨ e₁ ++ e₂ , fresh ⟩⇓⟨[
        (a₁ +ₐ a₂) ∷ₗ ts₂ ++ₗ ts₁ , Code N (Vₐ fresh'')
      ],
      suc fresh'' ⟩
