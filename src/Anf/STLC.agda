module Anf.STLC where

open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.List as List using (List; _++_) renaming (_∷_ to _∷ₗ_; [] to []ₗ)
open import Data.Product as Prod using (Σ; Σ-syntax; _×_) renaming (_,_ to [_∣_])
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl; trans)

open import Data.Gas
open import Data.Vec.Extensions

private variable
  T : Set
  n n' : ℕ

data Typ : Set where
  N : Typ
  _=>_ : Typ → Typ → Typ

private variable
  τ τ' τ₁ τ₂ : Typ

Ctx : ℕ → Set
Ctx = Vec Typ

data Tm : {n : ℕ} → Typ → Ctx n → Set where
  -- STLC
  C : ∀{Γ} → ℕ → Tm {n} N Γ
  V : ∀{Γ} → (i : Fin n) → {rlookup Γ i ≡ τ} → Tm τ Γ
  λ' : ∀{Γ : Ctx n} → (τ₁ : Typ) → Tm τ₂ (τ₁ ∷ Γ) → Tm (τ₁ => τ₂) Γ
  _$_ : ∀{Γ : Ctx n} → Tm (τ₁ => τ₂) Γ → Tm τ₁ Γ → Tm τ₂ Γ

  -- Cut
  Let : ∀{Γ : Ctx n} → Tm τ₁ Γ → Tm τ₂ (τ₁ ∷ Γ) → Tm τ₂ Γ

  -- Nat
  _+_ : ∀{Γ : Ctx n} → Tm N Γ → Tm N Γ → Tm N Γ

data AnfVal : Set where
  Constₐ : ℕ → AnfVal
  Varₐ : ℕ → AnfVal

data AnfTm : Set where
  _+ₐ_ : AnfVal → AnfVal → AnfTm
  _$ₐ_ : AnfVal → AnfVal → AnfTm
  λₐ : Typ → List AnfTm → AnfVal → AnfTm

[_] : ∀{T : Set} → T → List T
[ x ] = x ∷ₗ []ₗ

Env : ∀ ℕ → Set
Env = Vec AnfVal

private variable
  fresh fresh' fresh'' : ℕ

data _⊢⟨_,_⟩⇝⟨[_,_],_⟩ : ∀{Γ : Ctx n} →
  Env n → Tm τ Γ → ℕ → List AnfTm → AnfVal → ℕ → Set where

  anf-C : ∀{Γ : Ctx n} {env : Env n} {x} →
    env ⊢⟨ C {Γ = Γ} x , fresh ⟩⇝⟨[ []ₗ , Constₐ x ], fresh ⟩

  anf-V : ∀{Γ : Ctx n} {env : Env n} {i v} →
    {rlookup env i ≡ v} →
    env ⊢⟨ V {Γ = Γ} i {refl} , fresh ⟩⇝⟨[ []ₗ , v ], fresh ⟩

  anf-λ : ∀{Γ : Ctx n} {env : Env n} {tms} {e : Tm τ' (τ ∷ Γ)} {body} →
    (Varₐ fresh ∷ env) ⊢⟨ e , suc fresh ⟩⇝⟨[ tms , body ], fresh' ⟩ →
    env ⊢⟨ λ' τ e , fresh ⟩⇝⟨[ [ λₐ τ tms body ] , Varₐ fresh ], suc fresh ⟩

  anf-$ : ∀{Γ : Ctx n} {env : Env n} {e₁ : Tm (τ₁ => τ₂) Γ} {e₂ v₁ v₂ tms₁ tms₂} →
    env ⊢⟨ e₁ , fresh ⟩⇝⟨[ tms₁ , v₁ ], fresh' ⟩ →
    env ⊢⟨ e₂ , fresh' ⟩⇝⟨[ tms₂ , v₂ ], fresh'' ⟩ →
    env ⊢⟨ e₁ $ e₂ , fresh ⟩⇝⟨[ (v₁ $ₐ v₂) ∷ₗ tms₁ ++ tms₂ , Varₐ fresh'' ], suc fresh'' ⟩

  anf-+ : ∀{Γ : Ctx n} {env : Env n} {e₁ : Tm _ Γ} {e₂ v₁ v₂ tms₁ tms₂} →
    env ⊢⟨ e₁ , fresh ⟩⇝⟨[ tms₁ , v₁ ], fresh' ⟩ →
    env ⊢⟨ e₂ , fresh' ⟩⇝⟨[ tms₂ , v₂ ], fresh'' ⟩ →
    env ⊢⟨ e₁ + e₂ , fresh ⟩⇝⟨[ (v₁ +ₐ v₂) ∷ₗ tms₁ ++ tms₂ , Varₐ fresh'' ], suc fresh'' ⟩

  anf-let : ∀{Γ : Ctx n} {env : Env n} {e₁} {e₂ : Tm τ₂ (τ₁ ∷ Γ)} {v₁ v₂ tms₁ tms₂} →
    env ⊢⟨ e₁ , fresh ⟩⇝⟨[ tms₁ , v₁ ], fresh' ⟩ →
    (v₁ ∷ env) ⊢⟨ e₂ , fresh' ⟩⇝⟨[ tms₂ , v₂ ], fresh'' ⟩ →
    env ⊢⟨ Let e₁ e₂ , fresh ⟩⇝⟨[ tms₁ ++ tms₂ , v₂ ], fresh'' ⟩

{-
anf-elab : ∀{Γ : Ctx n} {env : Env n} e →
  env ⊢⟨ e , fresh ⟩⇝ tms ⟨ v , fresh' ⟩ →
  -}
