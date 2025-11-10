module Lms.STLC.ValueCorrectness where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality using (refl)

open import Data.Product.Extensions
open import Data.Context using (_[_]=_; here; there)

open import Lms.STLC.Core
open import Lms.STLC.IR as Anf hiding (Val; Env)
open import Lms.STLC.Evaluation

private variable
  n : ℕ
  fresh fresh' fresh'' : ℕ

forgetTyp : Typ Staged → Typ Base
forgetTyp N = N
forgetTyp (τ₁ => τ₂) = forgetTyp τ₁ => forgetTyp τ₂
forgetTyp (Rep τ) = τ

forgetCtx : Ctx Staged n → Ctx Base n
forgetCtx = Vec.map forgetTyp

forget-lookup : ∀{Γ : Ctx Staged n} {i τ} →
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
forget (λλ τ e) = forget e
forget (e₁ ++ e₂) = forget e₁ +' forget e₂
forget (e₁ $$ e₂) = forget e₁ $ forget e₂

liftCtx : Ctx Base n → Ctx Staged n
liftCtx = Vec.map Rep

lift-lookup : ∀{Γ : Ctx Base n} {i τ} →
  Γ [ i ]= τ → (liftCtx Γ)[ i ]= Rep τ
lift-lookup here = here
lift-lookup (there Γ[i]=τ) = there (lift-lookup Γ[i]=τ)

lift : ∀{Γ : Ctx Base n} {τ} → Tm Base τ Γ → Tm Staged (Rep τ) (liftCtx Γ)
lift (C x) = CC (C x)
lift (V i Γ[i]=τ) = V i (lift-lookup Γ[i]=τ)
lift (λ' τ e) = λλ τ (λ' (Rep τ) (lift e))
lift (e₁ $ e₂) = lift e₁ $$ lift e₂
lift (Let e₁ e₂) = Let (lift e₁) (lift e₂)
lift (e₁ +' e₂) = lift e₁ ++ lift e₂

data _≈_ : ∀{τ} → Val Base τ → Anf.Val → Set where
  ≈-N : ∀ x → Const x ≈ Constₐ x

{-
lift-correct : ∀ {Γ : Ctx Base n} {env : Env Γ} {τ} {e : Tm Base τ Γ} →
  env ⊢ e ⇓ v → {!!}
-}

{-
valueCorrectness :
  ∀ {τ e ts a va vb} →
  ∅ ⊢⟨ e , zero ⟩⇓⟨[ ts , Code τ a ], fresh ⟩ →
  ∃[ va , vb ](⊢p⟨ ts , a ⟩⇓ va × ∅ ⊢ forget e ⇓ vb × va ≈ vb)
-}
