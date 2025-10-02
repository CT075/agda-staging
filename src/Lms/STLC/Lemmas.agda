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
    ≡⟨ bindM2-sub2 (eval-apply gas) eval₁→f eval₂→x ⟩
  bindM2 (eval-apply gas) (Done f) (Done x)
    ≡⟨⟩
  eval-apply gas f x
    ≡⟨ eval-apply-weaken-gas g f x app→v ⟩
  Done v
    ∎
  where
    open OrTimeoutOps
    open ≡-Reasoning

    intermediates : bindM2Intermediates (eval-apply g) (eval g env e₁) (eval g env e₂) v
    intermediates = bindM2-done (eval g env e₁) (eval g env e₂) p

    open bindM2Intermediates
    f = fst intermediates
    x = snd intermediates
    eval₁→f = eval-weaken-gas g e₁ (mfst→fst intermediates)
    eval₂→x = eval-weaken-gas g e₂ (msnd→snd intermediates)
    app→v = run-f intermediates
eval-weaken-gas (suc g) (Let e₁ e₂) p = {!!}
eval-weaken-gas {env = env} {v = v} (gas @ (suc g)) (e₁ +' e₂) p = begin
  eval (suc gas) env (e₁ +' e₂)
    ≡⟨⟩
  liftA2 (liftValN2 Nat._+_) (eval gas env e₁) (eval gas env e₂)
    ≡⟨ liftA2-sub2 (liftValN2 Nat._+_) eval₁→x₁ eval₂→x₂ ⟩
  liftA2 (liftValN2 Nat._+_) (Done x₁) (Done x₂)
    ≡⟨⟩
  Done (liftValN2 Nat._+_ x₁ x₂)
    ≡⟨ cong Done x₁+x₂≡v ⟩
  Done v
    ∎
  where
    open OrTimeoutOps
    open ≡-Reasoning

    intermediates : liftA2Intermediates (liftValN2 Nat._+_) (eval g env e₁) (eval g env e₂) v
    intermediates = liftA2-done (eval g env e₁) (eval g env e₂) p

    open liftA2Intermediates
    x₁ = fst intermediates
    x₂ = snd intermediates
    eval₁→x₁ = eval-weaken-gas g e₁ (afst→fst intermediates)
    eval₂→x₂ = eval-weaken-gas g e₂ (asnd→snd intermediates)
    x₁+x₂≡v = run-f intermediates
eval-weaken-gas {env = env} {v = v} (gas @ (suc g)) (e₁ *' e₂) p = begin
  eval (suc gas) env (e₁ *' e₂)
    ≡⟨⟩
  liftA2 (liftValN2 Nat._*_) (eval gas env e₁) (eval gas env e₂)
    ≡⟨ liftA2-sub2 (liftValN2 Nat._*_) eval₁→x₁ eval₂→x₂ ⟩
  liftA2 (liftValN2 Nat._*_) (Done x₁) (Done x₂)
    ≡⟨⟩
  Done (liftValN2 Nat._*_ x₁ x₂)
    ≡⟨ cong Done x₁*x₂≡v ⟩
  Done v
    ∎
  where
    open OrTimeoutOps
    open ≡-Reasoning

    intermediates : liftA2Intermediates (liftValN2 Nat._*_) (eval g env e₁) (eval g env e₂) v
    intermediates = liftA2-done (eval g env e₁) (eval g env e₂) p

    open liftA2Intermediates
    x₁ = fst intermediates
    x₂ = snd intermediates
    eval₁→x₁ = eval-weaken-gas g e₁ (afst→fst intermediates)
    eval₂→x₂ = eval-weaken-gas g e₂ (asnd→snd intermediates)
    x₁*x₂≡v = run-f intermediates

eval-apply-weaken-gas gas f x p = {!!}
