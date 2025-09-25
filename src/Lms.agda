module Lms where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Vec as Vec using (Vec; lookup; _∷ʳ_; [])
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)

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
  _=>_ : ∀{w} → Typ w → Typ w → Typ w
  -- By including a `dW w` term, we can't even utter the type `Rep` in the
  -- base language.
  Rep : ∀{w} → {dW w} → Typ w → Typ w

Ctx : W → ℕ → Set
Ctx w = Vec (Typ w)

data Tm : (w : W) → {n : ℕ} → Typ w → Ctx w n → Set where
  -- STLC
  C : ∀{w n Γ} → ℕ → Tm w {n} N Γ
  V : ∀{w n Γ} → (i : Fin n) → Tm w (lookup Γ i) Γ
  λ' : ∀{w n τ₂} {Γ : Ctx w n} → (τ₁ : Typ w) → Tm w τ₂ (Γ ∷ʳ τ₁) → Tm w (τ₁ => τ₂) Γ
  _$_ : ∀{w n τ₁ τ₂} {Γ : Ctx w n} → Tm w (τ₁ => τ₂) Γ → Tm w τ₁ Γ → Tm w τ₂ Γ

  -- Nat
  _+'_ : ∀{w n} {Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ
  _*'_ : ∀{w n} {Γ : Ctx w n} → Tm w N Γ → Tm w N Γ → Tm w N Γ

  -- Rep
  lift : ∀{n τ} {Γ : Ctx Staged n} → Tm Staged τ Γ → Tm Staged (Rep τ) Γ
