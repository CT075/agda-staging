module Lms.Arith where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Nat as Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data W : Set where
  Base : W
  Staged : W

data Typ : W → Set where
  N : ∀{w} → Typ w
  Rep : Typ Base → Typ Staged

data weakensTo : Typ Base → Typ Staged → Set where
  weaken-N : weakensTo N N

data Exp : (w : W) → Typ w → Set where
  C : ∀{w} → ℕ → Exp w N
  _+'_ : ∀{w} → Exp w N → Exp w N → Exp w N
  _*'_ : ∀{w} → Exp w N → Exp w N → Exp w N

  lift : ∀{τbase τ} → {wk : weakensTo τbase τ} → Exp Staged τ → Exp Staged (Rep τbase)
  _++_ : Exp Staged (Rep N) → Exp Staged (Rep N) → Exp Staged (Rep N)
  _**_ : Exp Staged (Rep N) → Exp Staged (Rep N) → Exp Staged (Rep N)

⟦_⟧ : ∀{w} → Typ w → Set
⟦ N ⟧ = ℕ
⟦ Rep τ ⟧ = Exp Base τ

eval : ∀{τ} → Exp Base τ → ⟦ τ ⟧
eval (C x) = x
eval (e₁ +' e₂) = eval e₁ + eval e₂
eval (e₁ *' e₂) = eval e₁ * eval e₂

unrep : Typ Staged → Typ Base
unrep N = N
unrep (Rep τ) = τ

evalms : ∀{τ} → Exp Staged τ → ⟦ τ ⟧
evalms (C x) = x
evalms (e₁ +' e₂) = evalms e₁ + evalms e₂
evalms (e₁ *' e₂) = evalms e₁ * evalms e₂
evalms (lift {wk = weaken-N} e) = C (evalms e)
evalms (e₁ ++ e₂) = evalms e₁ +' evalms e₂
evalms (e₁ ** e₂) = evalms e₁ *' evalms e₂

forget : ∀{τ} → Exp Staged τ → Exp Base (unrep τ)
forget (C x) = C x
forget (e₁ +' e₂) = forget e₁ +' forget e₂
forget (e₁ *' e₂) = forget e₁ *' forget e₂
forget (lift {wk = weaken-N} e) = forget e
forget (e₁ ++ e₂) = forget e₁ +' forget e₂
forget (e₁ ** e₂) = forget e₁ *' forget e₂

lemma : (e : Exp Staged N) → evalms e ≡ eval (forget e)
lemma (C x) = refl
lemma (e₁ +' e₂) rewrite lemma e₁ rewrite lemma e₂ = refl
lemma (e₁ *' e₂) rewrite lemma e₁ rewrite lemma e₂ = refl

correct : ∀{τ} → (e : Exp Staged (Rep τ)) → eval (evalms e) ≡ eval (forget e)
correct (lift {wk = weaken-N} e) rewrite lemma e = refl
correct (e₁ ++ e₂) rewrite correct e₁ rewrite correct e₂ = refl
correct (e₁ ** e₂) rewrite correct e₁ rewrite correct e₂ = refl
