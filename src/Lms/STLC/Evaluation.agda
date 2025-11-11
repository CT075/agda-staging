module Lms.STLC.Evaluation where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec using (Vec; _∷_; []) renaming (_++_ to _⧺_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Store as Store using (Store; cons; nil; store-lookup-syntax)

open import Lms.STLC.Core
open import Lms.STLC.IR as Anf hiding (Expr; Val; Env)

private variable
  n n' m m' m₁ m₂ m₃ i : ℕ
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
  eval-V : ∀{Γ : Ctx Base n} {env : Env Γ} {τ i Γ[i]=τ v} → env [ i ]↦ v ∈ τ →
    env ⊢ V i Γ[i]=τ ⇓ v
  eval-λ : ∀{Γ : Ctx Base n} (env : Env Γ) {τ τ'} (e : Tm Base τ' _) →
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
    v ≡ x₁ + x₂ →
    env ⊢ e₁ ⇓ Const x₁ → env ⊢ e₂ ⇓ Const x₂ →
    env ⊢ e₁ +' e₂ ⇓ Const v

private variable
  offs offs' offs'' : ℕ
  ts : Vec Anf.Expr m
  ts₁ : Vec Anf.Expr m₁
  ts₂ : Vec Anf.Expr m₂
  ts₃ : Vec Anf.Expr m₃

infix 4 _,_⊢_⇓[_,_]
data _,_⊢_⇓[_,_] : ∀{τ} {Γ : Ctx Staged n} →
  -- Store
  Env Γ →
  -- Fresh variable offs
  ℕ →
  -- Term to evaluate
  Tm Staged τ Γ →
  -- ANF terms ("stBlock") + result
  Vec Anf.Expr m → Val Staged τ →
  Set
  where
  evalms-C : ∀{Γ : Ctx Staged n} {env : Env Γ} x →
    env , offs ⊢ C x ⇓[ [] , Const x ]
  evalms-V : ∀{Γ : Ctx Staged n} {env : Env Γ} {τ p v} → env [ i ]↦ v ∈ τ →
    env , offs ⊢ V i p ⇓[ [] , v ]
  evalms-λ : ∀{Γ : Ctx Staged n} (env : Env Γ) {τ τ'} (e : Tm _ τ' (τ ∷ Γ)) →
    env , offs ⊢ λ' τ e ⇓[ [] , Closure env e ]
  evalms-$ :
    ∀ {Γ : Ctx Staged n} {env : Env Γ} {Γ' : Ctx Staged n'} {env' : Env Γ'}
      {ts₁ : Vec _ m₁} {ts₂ : Vec _ m₂}
      {τ₁ τ₂} {e₁ : Tm _ (τ₁ => τ₂) Γ} {e₂ x e' v} →
    offs' ≡ m₁ + offs → offs'' ≡ m₂ + offs' →
    env , offs ⊢ e₁ ⇓[ ts₁ , Closure env' e' ] →
    env , offs' ⊢ e₂ ⇓[ ts₂ , x ] →
    cons x env' , offs'' ⊢ e' ⇓[ ts₃ , v ] →
    env , offs ⊢ e₁ $ e₂ ⇓[ ts₃ ⧺ ts₂ ⧺ ts₁ , v ]
  evalms-let :
    ∀ {Γ : Ctx Staged n} {env : Env Γ} {ts₁ : Vec _ m₁}
      {τ₁ τ₂ e₁} {e₂ : Tm _ τ₂ (τ₁ ∷ Γ)} {x v} →
    offs' ≡ m₁ + offs →
    env , offs ⊢ e₁ ⇓[ ts₁ , x ] →
    cons x env , offs' ⊢ e₂ ⇓[ ts₂ , v ] →
    env , offs ⊢ Let e₁ e₂ ⇓[ ts₂ ⧺ ts₁ , v ]
  evalms-+ :
    ∀ {Γ : Ctx Staged n} {env : Env Γ} {ts₁ : Vec _ m₁} {e₁ e₂ x₁ x₂ x} →
    offs' ≡ m₁ + offs → x ≡ x₁ + x₂ →
    env , offs ⊢ e₁ ⇓[ ts₁ , Const x₁ ] →
    env , offs' ⊢ e₂ ⇓[ ts₂ , Const x₂ ] →
    env , offs ⊢ e₁ +' e₂ ⇓[ ts₂ ⧺ ts₁ , Const x ]

  evalms-CC : ∀{Γ : Ctx Staged n} {env : Env Γ} {e x} →
    env , offs ⊢ e ⇓[ ts , Const x ] →
    env , offs ⊢ CC e ⇓[ ts , Code N (Cₐ x) ]
  evalms-λλ :
    ∀ {Γ : Ctx Staged n} {env : Env Γ} {Γ' : Ctx _ n'} {env' : Env Γ'}
      {τ τ'} {e : Tm _ (Rep τ => Rep τ') Γ} {e' v}
      {ts : Vec Anf.Expr m} {tsᵢ : Vec Anf.Expr m'} →
    offs' ≡ m + offs →
    env , offs ⊢ e ⇓[ ts , Closure env' e' ] →
    (cons (Code τ (Vₐ offs')) env') , suc offs' ⊢ e' ⇓[ tsᵢ , Code τ' v ] →
    env , offs ⊢ λλ τ e ⇓[ (λₐ τ tsᵢ v) ∷ ts , Code (τ => τ') (Vₐ offs') ]

  evalms-++ :
    ∀ {Γ : Ctx Staged n} {env : Env Γ} {e₁ e₂ a₁ a₂}
      {ts₁ : Vec Anf.Expr m₁} {ts₂ : Vec Anf.Expr m₂} →
    offs' ≡ m₁ + offs → offs'' ≡ m₂ + offs' →
    env , offs ⊢ e₁ ⇓[ ts₁ , Code N a₁ ] →
    env , offs' ⊢ e₂ ⇓[ ts₂ , Code N a₂ ] →
    env , offs ⊢ e₁ ++ e₂ ⇓[ a₁ +ₐ a₂ ∷ ts₂ ⧺ ts₁ , Code N (Vₐ offs'') ]
  evalms-$$ :
    ∀ {Γ : Ctx Staged n} {env : Env Γ} {τ τ' e₁ e₂ a₁ a₂}
      {ts₁ : Vec Anf.Expr m₁} {ts₂ : Vec Anf.Expr m₂} →
    offs' ≡ m₁ + offs → offs'' ≡ m₂ + offs' →
    env , offs ⊢ e₁ ⇓[ ts₁ , Code (τ => τ') a₁ ] →
    env , offs' ⊢ e₂ ⇓[ ts₂ , Code τ a₂ ] →
    env , offs ⊢ e₁ $$ e₂ ⇓[ a₁ $ₐ a₂ ∷ ts₂ ⧺ ts₁ , Code τ' (Vₐ offs'') ]

_,_⊢r_⇓_ : ∀{Γ : Ctx Staged n} {τ} →
  Env Γ → ℕ → Tm Staged (Rep τ) Γ → Anf.Prog → Set
env , offs ⊢r e ⇓ [ ts , v ] = env , offs ⊢ e ⇓[ ts , Code _ v ]
