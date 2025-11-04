module Lms.STLC.ValueCorrectness where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec using (Vec; []; _∷_)

open import Data.Context using (_[_]=_; here; there)

open import Lms.STLC.Core
open import Lms.STLC.IR as IR hiding (Val)
open import Lms.STLC.Evaluation

private variable
  n : ℕ

forgetTyp : Typ Staged → Typ Base
forgetTyp N = N
forgetTyp (τ₁ => τ₂) = forgetTyp τ₁ => forgetTyp τ₂
forgetTyp (Rep τ) = τ

forgetCtx : Ctx Staged n → Ctx Base n
forgetCtx = Vec.map forgetTyp

forget-lookup :
  ∀ {Γ : Ctx Staged n} {i τ} →
  Γ [ i ]= τ → (forgetCtx Γ)[ i ]= (forgetTyp τ)
forget-lookup here = here
forget-lookup (there Γ[i]=τ) = there (forget-lookup Γ[i]=τ)

forget :
  ∀ {Γ : Ctx Staged n} {τ} →
  Tm Staged τ Γ → Tm Base (forgetTyp τ) (forgetCtx Γ)
forget (C x) = C x
forget (V i Γ[i]=τ) = V i (forget-lookup Γ[i]=τ)
forget (λ' τ e) = λ' (forgetTyp τ) (forget e)
forget (e₁ $ e₂) = forget e₁ $ forget e₂
forget (Let e₁ e₂) = Let (forget e₁) (forget e₂)
forget (e₁ +' e₂) = forget e₁ +' forget e₂
forget (CC e) = forget e
--forget (λλ τ e) = λ' (forgetTyp τ) {!!}
forget (e₁ ++ e₂) = forget e₁ +' forget e₂
forget (e₁ $$ e₂) = forget e₁ $ forget e₂

data _≈_ : ∀{τ} → IR.Val → Val Base τ → Set where
  const-≈ : ∀ x → Constₐ x ≈ Const x
  abs-≈ : {!!}
