module Lms.STLC.Lemmas where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _*_)
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import Data.Gas
open import Data.Gas.Lemmas
open import Lms.STLC

private variable n : ℕ

eval-weaken-gas : ∀{τ} {Γ : Ctx Base n} {env : Env Γ} {v}
  gas (e : Tm Base τ Γ) →
  eval gas env e ≡ Done v → eval (suc gas) env e ≡ Done v

eval-apply-weaken-gas : ∀{τ₁ τ₂} {v}
  gas (f : Val Base (τ₁ => τ₂)) (x : Val Base τ₁) →
  eval-apply gas f x ≡ Done v →
  eval-apply (suc gas) f x ≡ Done v

eval-weaken-gas zero _ ()
eval-weaken-gas (suc g) (C x) p = p
eval-weaken-gas (suc g) (V i) p = p
eval-weaken-gas (suc g) (λ' τ e) p = p
eval-weaken-gas {env = env} {v = v} (gas @ (suc g)) (e₁ $ e₂) p = begin
  eval (suc gas) env (e₁ $ e₂)
    ≡⟨⟩
  bindM2 (eval-apply gas) (eval gas env e₁) (eval gas env e₂)
    ≡⟨ bindM2-sub-both (eval-apply gas) fp xp ⟩
  bindM2 (eval-apply gas) (Done f) (Done x)
    ≡⟨⟩
  eval-apply gas f x
    ≡⟨ eval-apply-weaken-gas g f x (bindM2-done (proj₂ mfp) (proj₂ mxp) p) ⟩
  Done v
    ∎
  where
    open OrTimeoutOps
    open ≡-Reasoning

    mfp : ∃[ f ](eval g env e₁ ≡ Done f)
    mfp = bindM2-done₁ _ (eval g env e₁) (eval g env e₂) p
    f = proj₁ mfp
    fp : eval gas env e₁ ≡ Done f
    fp = eval-weaken-gas g e₁ (proj₂ mfp)

    mxp : ∃[ x ](eval g env e₂ ≡ Done x)
    mxp = bindM2-done₂ _ (eval g env e₁) (eval g env e₂) p
    x = proj₁ mxp
    xp : eval gas env e₂ ≡ Done x
    xp = eval-weaken-gas g e₂ (proj₂ mxp)
eval-weaken-gas (suc g) (Let e₁ e₂) p = {!!}
eval-weaken-gas (suc g) (e₁ +' e₂) p = {!!}
eval-weaken-gas (suc g) (e₁ *' e₂) p = {!!}

eval-apply-weaken-gas gas f x p = {!!}
