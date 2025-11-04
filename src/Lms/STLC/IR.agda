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
  n n' : ℕ

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
    Γ ⊢t e₁ $ₐ e₂ ∈ τ₂
  anf-λ : ∀{Γ : Ctx Base n} {Γ' : Ctx Base n'} {Γs : Ctx Base (n' + n)}
    τ {τ' es v} →
    Γ' ++ᵥ Γ ≡ Γs →
    τ ∷ Γ ⊢ts es ∈ Γ' → τ ∷ Γs ⊢v v ∈ τ' →
    Γ ⊢t λₐ τ es v ∈ τ => τ'

data _⊢ts_∈_ where
  anf-nil : ∀{Γ : Ctx Base n} → Γ ⊢ts nilₗ ∈ []
  anf-cons : ∀{Γ : Ctx Base n} {Γ' : Ctx Base n'} {Γs : Ctx Base (n' + n)}
    {x xs τ} →
    Γ' ++ᵥ Γ ≡ Γs →
    Γ ⊢ts xs ∈ Γ' → Γs ⊢t x ∈ τ →
    Γ ⊢ts x ∷ₗ xs ∈ τ ∷ Γ'
