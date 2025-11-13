module Lms.STLC.Core where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec using (_∷_)

open import Data.Context as Context using (_[_]=_)

private variable
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
  λλ : ∀ τ₁ {τ₂} {Γ : Ctx Staged n} →
    Tm Staged (Rep τ₁ => Rep τ₂) Γ → Tm Staged (Rep (τ₁ => τ₂)) Γ
  _++_ : ∀{Γ : Ctx Staged n} →
    Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ → Tm Staged (Rep N) Γ
  _$$_ : ∀{τ₁ τ₂} {Γ : Ctx Staged n} →
    Tm Staged (Rep (τ₁ => τ₂)) Γ → Tm Staged (Rep τ₁) Γ → Tm Staged (Rep τ₂) Γ
