module Lms.STLC.Surface where

open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Vec as Vec using (_∷_)
open import Data.Product as Prod
open import Data.Maybe as Maybe
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong)

open import Data.Context as Context using (_[_]=_)

open import Lms.STLC.Core as Core hiding (Tm; Ctx; Typ)

Typ = Core.Typ Staged
Ctx = Core.Ctx Staged

private variable
  w : W
  n i : ℕ
  τ τ' τ₁ τ₂ : Typ
  β β' : Core.Typ Base
  Γ : Ctx n

data Tm : Set where
  C : ℕ → Tm
  V : ℕ → Tm
  λ' : Typ → Tm → Tm
  _$_ : Tm → Tm → Tm
  _+'_ : Tm → Tm → Tm
  Let : Tm → Tm → Tm
  λλ : Tm → Tm

private variable
  e e₁ e₂ : Tm

infix 4 _⊢↑_⇝_ _⊢↓_⇝_

data _⊢↑_⇝_ : Ctx n → Tm → Core.Tm Staged τ Γ → Set
data _⊢↓_⇝_ : Ctx n → Tm → Core.Tm Staged τ Γ → Set

data _⊢↑_⇝_ where
  synth-N : ∀ x → Γ ⊢↑ C x ⇝ C {Γ = Γ} x
  synth-V : ∀{i} → (p : Γ [ i ]= τ) → Γ ⊢↑ V i ⇝ V i p
  synth-λ : ∀{e' : Core.Tm _ τ' (τ ∷ Γ)} →
    τ ∷ Γ ⊢↑ e ⇝ e' →
    Γ ⊢↑ λ' τ e ⇝ λ' τ e'
  synth-$ : ∀{e₁' : Core.Tm _ (τ => τ') Γ} {e₂' : Core.Tm _ τ Γ} →
    Γ ⊢↑ e₁ ⇝ e₁' →
    Γ ⊢↓ e₂ ⇝ e₂' →
    Γ ⊢↑ e₁ $ e₂ ⇝ e₁' $ e₂'
  synth-$$ : ∀{e₁' : Core.Tm _ (Rep (β => β')) Γ} {e₂' : Core.Tm _ (Rep β) Γ} →
    Γ ⊢↑ e₁ ⇝ e₁' →
    Γ ⊢↓ e₂ ⇝ e₂' →
    Γ ⊢↑ e₁ $ e₂ ⇝ e₁' $$ e₂'
  synth-+ : ∀{e₁' : Core.Tm _ N Γ} {e₂' : Core.Tm _ N Γ} →
    Γ ⊢↓ e₁ ⇝ e₁' →
    Γ ⊢↓ e₂ ⇝ e₂' →
    Γ ⊢↑ e₁ +' e₂ ⇝ e₁' +' e₂'
  synth-++ₗ : ∀{e₁' : Core.Tm _ (Rep N) Γ} {e₂' : Core.Tm _ (Rep N) Γ} →
    Γ ⊢↑ e₁ ⇝ e₁' →
    Γ ⊢↓ e₂ ⇝ e₂' →
    Γ ⊢↑ e₁ +' e₂ ⇝ e₁' ++ e₂'
  synth-++ᵣ : ∀{e₁' : Core.Tm _ (Rep N) Γ} {e₂' : Core.Tm _ (Rep N) Γ} →
    Γ ⊢↓ e₁ ⇝ e₁' →
    Γ ⊢↑ e₂ ⇝ e₂' →
    Γ ⊢↑ e₁ +' e₂ ⇝ e₁' ++ e₂'
  synth-λλ : ∀{e' : Core.Tm _ (Rep β => Rep β') Γ} →
    Γ ⊢↑ e ⇝ e' →
    Γ ⊢↑ λλ e ⇝ λλ β e'
  synth-let : ∀{e₁' : Core.Tm _ τ₁ Γ} {e₂' : Core.Tm _ τ₂ (τ₁ ∷ Γ)} →
    Γ ⊢↑ e₁ ⇝ e₁' →
    (τ₁ ∷ Γ) ⊢↑ e₂ ⇝ e₂' →
    Γ ⊢↑ Let e₁ e₂ ⇝ Let e₁' e₂'

data _⊢↓_⇝_ where
  check-refl : ∀{e' : Core.Tm _ τ Γ} → Γ ⊢↑ e ⇝ e' → Γ ⊢↓ e ⇝ e'
  check-CC : ∀{e' : Core.Tm _ N Γ} → Γ ⊢↑ e ⇝ e' → Γ ⊢↓ e ⇝ CC e'
  check-λλ : ∀{e' : Core.Tm _ (Rep β => Rep β') Γ} →
    Γ ⊢↑ e ⇝ e' →
    Γ ⊢↓ e ⇝ λλ β e'

_==_ : (τ₁ : Core.Typ w) → (τ₂ : Core.Typ w) → Maybe (τ₁ ≡ τ₂)
N == N = just refl
(A => B) == (A' => B') = do
  refl ← A == A'
  refl ← B == B'
  just refl
Rep β == Rep β' = Maybe.map (cong Rep) (β == β')
_ == _ = nothing

synth : (Γ : Ctx n) → (e : Tm) → Maybe (∃[ τ ](Σ[ e' ∈ Core.Tm _ τ Γ ](Γ ⊢↑ e ⇝ e')))
check : (Γ : Ctx n) → (e : Tm) → (τ : Typ) → Maybe (Σ[ e' ∈ Core.Tm _ τ Γ ](Γ ⊢↓ e ⇝ e'))

synth Γ (C x) = just (N , C x , synth-N x)
synth Γ (V i) = do
  _ , p ← Context.lookup Γ i
  just (_ , V i p , synth-V p)
synth Γ (λ' τ e) = do
  _ , _ , Γ⊢e⇝e' ← synth (τ ∷ Γ) e
  just ((τ => _) , λ' τ _ , synth-λ Γ⊢e⇝e')
synth Γ (e₁ $ e₂) = do
  N , _ , _ ← synth Γ e₁
    where
      τ => τ' , _ , Γ⊢e₁⇝e₁' → do
        _ , Γ⊢e₂⇝e₂' ← check Γ e₂ τ
        just (τ' , (_ $ _) , synth-$ Γ⊢e₁⇝e₁' Γ⊢e₂⇝e₂')
      Rep (β => β') , _ , Γ⊢e₁⇝e₁' → do
        _ , Γ⊢e₂⇝e₂' ← check Γ e₂ (Rep β)
        just (Rep β' , (_ $$ _) , synth-$$ Γ⊢e₁⇝e₁' Γ⊢e₂⇝e₂')
      Rep N , _ , _ → nothing
  nothing
synth Γ (e₁ +' e₂) = do
  _ => _ , _ , _ ← synth Γ e₁
    where
      Rep (_ => _) , _ , _ → nothing
      Rep N , _ , Γ⊢e₁⇝e₁' → do
        _ , Γ⊢e₂⇝e₂ ← check Γ e₂ (Rep N)
        just (Rep N , (_ ++ _) , synth-++ₗ Γ⊢e₁⇝e₁' Γ⊢e₂⇝e₂)
      N , _ , Γ⊢e₁⇝e₁' → do
        _ => _ , _ , _ ← synth Γ e₂
          where
            Rep (_ => _) , _ , _ → nothing
            Rep N , _ , Γ⊢e₂⇝e₂' →
              just (Rep N , (CC _ ++ _) , synth-++ᵣ (check-CC Γ⊢e₁⇝e₁') Γ⊢e₂⇝e₂')
            N , _ , Γ⊢e₂⇝e₂' →
              just (N , (_ +' _) , synth-+ (check-refl Γ⊢e₁⇝e₁') (check-refl Γ⊢e₂⇝e₂'))
        nothing
  nothing
synth Γ (Let e₁ e₂) = do
  τ₁ , _ , Γ⊢e₁⇝e₁' ← synth Γ e₁
  τ₂ , _ , Γ⊢e₂⇝e₂' ← synth (τ₁ ∷ Γ) e₂
  just (τ₂ , Let _ _ , synth-let Γ⊢e₁⇝e₁' Γ⊢e₂⇝e₂')
synth Γ (λλ e) = do
  Rep β => Rep β' , _ , Γ⊢e⇝e' ← synth Γ e
    where _ , _ , _ → nothing
  just (Rep (β => β') , λλ β _ , synth-λλ Γ⊢e⇝e')

check Γ e τ with synth Γ e
... | nothing = nothing
... | just (τ' , _ , Γ⊢e⇝e') = inner τ τ' Γ⊢e⇝e'
  where
    inner : (τ : Typ) → (τ' : Typ) → {e' : Core.Tm _ τ' Γ} →
        (Γ ⊢↑ e ⇝ e') →
        Maybe (Σ[ e'' ∈ Core.Tm _ τ Γ ](Γ ⊢↓ e ⇝ e''))
    inner (Rep N) N Γ⊢e⇝e' = just (CC _ , check-CC Γ⊢e⇝e')
    inner (Rep (β₁ => β₂)) (Rep β₁' => Rep β₂') Γ⊢e⇝e' with β₁ == β₁'
    ... | nothing = nothing
    ... | just refl with β₂ == β₂'
    ...   | nothing = nothing
    ...   | just refl =
              just (λλ β₁ _ , check-λλ Γ⊢e⇝e')
    inner τ τ' Γ⊢e⇝e' with τ == τ'
    ... | nothing = nothing
    ... | just refl = just (_ , check-refl Γ⊢e⇝e')
