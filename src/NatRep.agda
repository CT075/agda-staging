module NatRep where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Nat as Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data W : Set where
  Base : W
  Staged : W

dW : W → Set
dW Base = ⊥
dW Staged = ⊤

data Typ : W → Set where
  N : ∀{w} → Typ w
  -- `dW Base` is empty, so we can't build `Rep τ : Typ Base`
  Rep : ∀{w} → {dW w} → Typ Base → Typ w

data Exp : (w : W) → Typ w → Set where
  C : ∀{w} → ℕ → Exp w N
  _+'_ : ∀{w} → Exp w N → Exp w N → Exp w N
  _*'_ : ∀{w} → Exp w N → Exp w N → Exp w N

  lift : Exp Base N → Exp Staged (Rep N)
  _++_ : Exp Staged (Rep N) → Exp Staged (Rep N) → Exp Staged (Rep N)
  _**_ : Exp Staged (Rep N) → Exp Staged (Rep N) → Exp Staged (Rep N)

eval : Exp Base N → ℕ
eval (C x) = x
eval (e₁ +' e₂) = eval e₁ + eval e₂
eval (e₁ *' e₂) = eval e₁ * eval e₂

⟦_⟧ : ∀{w} → Typ w → Set
⟦ N ⟧ = ℕ
⟦ Rep τ ⟧ = Exp Base τ

evalms : ∀{τ} → Exp Staged τ → ⟦ τ ⟧
evalms (C x) = x
evalms (e₁ +' e₂) = evalms e₁ + evalms e₂
evalms (e₁ *' e₂) = evalms e₁ * evalms e₂
evalms (lift e) = C (eval e)
evalms (e₁ ++ e₂) = evalms e₁ +' evalms e₂
evalms (e₁ ** e₂) = evalms e₁ *' evalms e₂

forget : Exp Staged (Rep N) → Exp Base N
forget (lift e) = e
forget (e₁ ++ e₂) = forget e₁ +' forget e₂
forget (e₁ ** e₂) = forget e₁ *' forget e₂

correct : (e : Exp Staged (Rep N)) → eval (evalms e) ≡ eval (forget e)
correct (lift e) = refl
correct (e₁ ++ e₂) rewrite correct e₁ rewrite correct e₂ = refl
correct (e₁ ** e₂) rewrite correct e₁ rewrite correct e₂ = refl
