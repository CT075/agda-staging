module Lms.STLC.Specialization where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties as Nat
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Empty as Void
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Data.Context as Context hiding (Ctx)

open import Lms.STLC.Core

private variable
  n nₛ nₜ : ℕ
  offs : ℕ
  τₛ : Typ Staged
  τₜ : Typ Base
  Γₛ : Ctx Staged n
  Γₜ : Ctx Base n

infix 4 _≤_ _≤Ty_ _≤Ctx_

data _≤Ty_ : Typ Staged → Typ Base → Set where
  ≤-Rep : ∀{τ} → Rep τ ≤Ty τ
  ≤-N : N ≤Ty N
  ≤-<= : ∀{τ₁ τ₂ τ₁' τ₂'} → τ₁ ≤Ty τ₁' → τ₂ ≤Ty τ₂' → τ₁ => τ₂ ≤Ty τ₁' => τ₂'

data _≤Ctx_ : Ctx Staged n → Ctx Base n → Set where
  ≤-nil : [] ≤Ctx []
  ≤-cons : τₛ ≤Ty τₜ → Γₛ ≤Ctx Γₜ → τₛ ∷ Γₛ ≤Ctx τₜ ∷ Γₜ

≤Ctx-lookup : ∀ {i} → Γₛ ≤Ctx Γₜ → Γₛ [ i ]= τₛ → Γₜ [ i ]= τₜ → τₛ ≤Ty τₜ
≤Ctx-lookup (≤-cons τₛ≤τₜ _) here here = τₛ≤τₜ
≤Ctx-lookup (≤-cons _ Γₛ≤Γₜ) (there Γₛ[i]=τₛ) (there Γₜ[i]=τₜ) =
  ≤Ctx-lookup Γₛ≤Γₜ Γₛ[i]=τₛ Γₜ[i]=τₜ
≤Ctx-lookup {Γₜ = _ ∷ _} (≤-cons τₛ≤τₜ Γₛ≤Γₜ) here (there Γₜ[i]=τₜ) =
  ⊥-elim (<-irrefl refl ([]=→< Γₜ[i]=τₜ))
≤Ctx-lookup {Γₛ = _ ∷ _} (≤-cons τₛ≤τₜ Γₛ≤Γₜ) (there Γₛ[i]=τₛ) here =
  ⊥-elim (<-irrefl refl ([]=→< Γₛ[i]=τₛ))

data _≤_ : Tm _ τₛ Γₛ → Tm _ τₜ Γₜ → Set
  where
  ≤-C : ∀ x → _≤_ {Γₛ = Γₛ} {Γₜ = Γₜ} (C x) (C x)
  ≤-V : ∀ i Γₛ[i]=τₛ Γₜ[i]=τₜ → Γₛ ≤Ctx Γₜ →
    _≤_ {τₛ = τₛ} {Γₛ = Γₛ} {τₜ} {Γₜ = Γₜ} (V i Γₛ[i]=τₛ) (V i Γₜ[i]=τₜ)
  ≤-λ :
    ∀ {τ₁ τ₂ τ₁' τ₂'}
      {eₛ : Tm Staged τ₂ (τ₁ ∷ Γₛ)} {eₜ : Tm Base τ₂' (τ₁' ∷ Γₜ)} →
    τ₁ ≤Ty τ₁' → eₛ ≤ eₜ →
    λ' τ₁ eₛ ≤ λ' τ₁' eₜ
  ≤-$ :
    ∀ {τ₁ τ₂ τ₁' τ₂'}
      {e₁ : Tm Staged (τ₁ => τ₂) Γₛ} {e₂}
      {e₁' : Tm Base (τ₁' => τ₂') Γₜ} {e₂'} →
    e₁ ≤ e₁' → e₂ ≤ e₂' →
    e₁ $ e₂ ≤ e₁' $ e₂'
  ≤-let :
    ∀ {τ₁ τ₁' τ₂ τ₂'}
      {e₁} {e₂ : Tm _ τ₂ (τ₁ ∷ Γₛ)} {e₁'} {e₂' : Tm _ τ₂' (τ₁' ∷ Γₜ)} →
    e₁ ≤ e₁' → e₂ ≤ e₂' →
    Let e₁ e₂ ≤ Let e₁' e₂'
  ≤-+ :
    ∀ {e₁ : Tm _ _ Γₛ} {e₂} {e₁' : Tm _ _ Γₜ} {e₂'} →
    e₁ ≤ e₁' → e₂ ≤ e₂' →
    e₁ +' e₂ ≤ e₁' +' e₂'

  ≤-CC :
    ∀ {Γₛ : Ctx Staged n} {eₛ : Tm _ _ Γₛ}
      {Γₜ : Ctx Base n} {eₜ : Tm _ N Γₜ} →
    eₛ ≤ eₜ →
    CC eₛ ≤ eₜ
  ≤-λλ :
    ∀ {τ τ'}
      {Γₛ : Ctx Staged n} {eₛ : Tm _ (Rep τ => Rep τ') Γₛ}
      {Γₜ : Ctx Base n} {eₜ : Tm _ (τ => τ') Γₜ} →
    λλ τ eₛ ≤ eₜ
  ≤-++ :
    ∀ {e₁ : Tm _ _ Γₛ} {e₂} {e₁' : Tm _ _ Γₜ} {e₂'} →
    e₁ ≤ e₁' → e₂ ≤ e₂' →
    e₁ ++ e₂ ≤ e₁' +' e₂'
  ≤-$$ :
    ∀ {τ₁ τ₂ τ₁' τ₂'}
      {e₁ : Tm _ (Rep (τ₁ => τ₂)) Γₛ} {e₂}
      {e₁' : Tm _ (τ₁' => τ₂') Γₜ} {e₂'} →
    e₁ ≤ e₁' → e₂ ≤ e₂' →
    e₁ $$ e₂ ≤ e₁' $ e₂'

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

forgetTyp-≤ : (τ : Typ Staged) → τ ≤Ty forgetTyp τ
forgetTyp-≤ N = ≤-N
forgetTyp-≤ (τ₁ => τ₂) = ≤-<= (forgetTyp-≤ τ₁) (forgetTyp-≤ τ₂)
forgetTyp-≤ (Rep τ) = ≤-Rep

forgetCtx-≤ : (Γ : Ctx Staged n) → Γ ≤Ctx forgetCtx Γ
forgetCtx-≤ [] = ≤-nil
forgetCtx-≤ (τ ∷ Γ) = ≤-cons (forgetTyp-≤ τ) (forgetCtx-≤ Γ)

forget-≤ : ∀{Γ : Ctx Staged n} {τ} → (e : Tm Staged τ Γ) → e ≤ forget e
forget-≤ (C x) = ≤-C _
forget-≤ (V i Γ[i]=τ) = ≤-V i _ _ (forgetCtx-≤ _)
forget-≤ (λ' τ e) = ≤-λ (forgetTyp-≤ τ) (forget-≤ e)
forget-≤ (e₁ $ e₂) = ≤-$ (forget-≤ e₁) (forget-≤ e₂)
forget-≤ (Let e₁ e₂) = ≤-let (forget-≤ e₁) (forget-≤ e₂)
forget-≤ (e₁ +' e₂) = ≤-+ (forget-≤ e₁) (forget-≤ e₂)
forget-≤ (CC e) = ≤-CC (forget-≤ e)
forget-≤ (λλ τ e) = ≤-λλ
forget-≤ (e₁ ++ e₂) = ≤-++ (forget-≤ e₁) (forget-≤ e₂)
forget-≤ (e₁ $$ e₂) = ≤-$$ (forget-≤ e₁) (forget-≤ e₂)
