module Lms.STLC.ValueCorrectness where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Context using (_[_]=_; here; there)
open import Data.Store as Store renaming (nil to ∅)

open import Lms.STLC.Core
open import Lms.STLC.IR as IR hiding (Val)
open import Lms.STLC.Evaluation

private variable
  w : W
  n fresh fresh' : ℕ

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

data _≐_ : ∀{τ τ↑} → Val Staged τ↑ → Val Base τ → Set where
  const-≐ : ∀ x → Const x ≐ Const x

data _≈_ : ∀{τ} → IR.Val → Val Base τ → Set where
  const-≈ : ∀ x → Constₐ x ≈ Const x

canonicalForms-staged-N : ∀{Γ : Ctx _ n} {env : Env Γ} {e : Tm _ N Γ} {ts v} →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  Σ[ x ∈ ℕ ](v ≡ Const x)
canonicalForms-staged-N {v = Const x} env⊢e⇓v = x , refl

foo :
  ∀ {e : Tm Staged N []} {ts va vb} →
  ∅ ⊢⟨ e , zero ⟩⇓⟨[ ts , va ], fresh ⟩ →
  ∅ ⊢ forget e ⇓ vb →
  va ≐ vb
foo (evalms-C x) (eval-C .x) = const-≐ x
foo (evalms-$ ⊢e⇓va ⊢e⇓va₁ ⊢e⇓va₂) ⊢f[e]⇓vb = {! !}
foo (evalms-let ⊢e⇓va ⊢e⇓va₁) ⊢f[e]⇓vb = {! !}
foo (evalms-+ x ⊢e⇓va ⊢e⇓va₁) ⊢f[e]⇓vb = {! !}

valueCorrectness :
  ∀ {τ e e' ts a va vb} → e' ≡ forget e →
  ∅ ⊢⟨ e , zero ⟩⇓⟨[ ts , Code τ a ], fresh ⟩ → ⊢p⟨ ts , a ⟩⇓ va →
  ∅ ⊢ e' ⇓ vb →
  va ≈ vb
valueCorrectness {e = e₁ $ e₂} refl ⊢e⇓⟨ts,a⟩ ⊢⟨ts,a⟩⇓va ⊢f[e]⇓vb = {! !}
valueCorrectness {e = Let e₁ e₂} refl ⊢e⇓⟨ts,a⟩ ⊢⟨ts,a⟩⇓va ⊢f[e]⇓vb = {! !}
-- TODO: show that, if `CC e` evaluates to anything, `e` evaluates to `Const x`.
valueCorrectness {e = CC e} refl (evalms-CC ⊢e⇓⟨ts,a⟩) (eval-prog eval-ts (eval-c x)) ⊢f[e]⇓vb = {! !}
valueCorrectness {e = e₁ ++ e₂} refl ⊢e⇓⟨ts,a⟩ ⊢⟨ts,a⟩⇓va ⊢f[e]⇓vb = {! !}
