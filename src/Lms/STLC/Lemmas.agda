module Lms.STLC.Lemmas where

open import Data.Nat as Nat
open import Data.Nat.Properties as Nat
open import Data.Product
open import Data.Vec as Vec
  using ([])
  renaming (_∷_ to _∷ᵥ_; _++_ to _++ᵥ_)
open import Data.List as List
  using (List; length)
  renaming (_∷_ to _∷ₗ_; [] to nilₗ; _++_ to _++ₗ_)
open import Data.List.Properties as List
open import Relation.Binary.PropositionalEquality

open import Data.Context
  using (_⊆_; ⊆-refl; ⊆-cons)
  renaming (here to chere; there to cthere)

open import Data.Nat.Extensions
open import Data.Vec.Extensions
open import Lms.STLC

private variable
  T : Set
  n n' n'' : ℕ
  fresh fresh' fresh'' fresh''' : ℕ
  ts ts₁ ts₂ ts₃ : List AnfTm

vl-typ-wk : ∀{Δ : Ctx Base n} {v τ} τ' → Δ ⊢v v ∈ τ → τ' ∷ᵥ Δ ⊢v v ∈ τ
vl-typ-wk τ (anf-c x) = anf-c x
vl-typ-wk τ (anf-v pf) = anf-v (cthere pf)

vl-typ-extend : ∀{Δ : Ctx Base n} {Δs : Ctx Base n'} {v τ} →
  Δ ⊆ Δs → Δ ⊢v v ∈ τ →
  Δs ⊢v v ∈ τ
vl-typ-extend (⊆-refl Δ) Δ⊢v∈τ = Δ⊢v∈τ
vl-typ-extend (⊆-cons τ' Δ⊆Δ') Δ⊢v∈τ = vl-typ-wk τ' (vl-typ-extend Δ⊆Δ' Δ⊢v∈τ)

tm-typ-wk : ∀{Δ : Ctx Base n} {t τ} τ' → Δ ⊢t t ∈ τ → τ' ∷ᵥ Δ ⊢t t ∈ τ
tm-typ-wk τ (anf-+ Δ⊢x₁∈N Δ⊢x₂∈N) =
  anf-+
    (vl-typ-wk τ Δ⊢x₁∈N)
    (vl-typ-wk τ Δ⊢x₂∈N)
tm-typ-wk τ (anf-$ x x₁) = {! !}
tm-typ-wk τ (anf-λ x x₁ x₂) = {! !}

tm-typ-extend : ∀{Δ : Ctx Base n} {Δs : Ctx Base n'} {t τ} →
  Δ ⊆ Δs → Δ ⊢t t ∈ τ →
  Δs ⊢t t ∈ τ
tm-typ-extend (⊆-refl Δ) Δ⊢t∈τ = Δ⊢t∈τ
tm-typ-extend (⊆-cons τ' Δ⊆Δ') Δ⊢t∈τ = tm-typ-wk τ' (tm-typ-extend Δ⊆Δ' Δ⊢t∈τ)

block-typ-size : ∀{Δ : Ctx Base n} {Δ' : Ctx Base n'} →
  Δ ⊢ts ts ∈ Δ' →
  length ts ≡ n'
block-typ-size anf-nil = refl
block-typ-size (anf-cons Δ'++Δ≡Δs Δ⊢xs∈Δ' Δs⊢x∈τ) =
  cong suc (block-typ-size Δ⊢xs∈Δ')

block-typ-extend : ∀{Δ : Ctx Base n} {Δ' : Ctx Base n'} {Δ'' : Ctx Base n''} →
  Δ ⊢ts ts₁ ∈ Δ' → Δ' ++ᵥ Δ ⊢ts ts₂ ∈ Δ'' →
  Δ ⊢ts ts₂ ++ₗ ts₁ ∈ Δ'' ++ᵥ Δ'
block-typ-extend Δ⊢ts₁∈Δ' anf-nil = Δ⊢ts₁∈Δ'
block-typ-extend {Δ = Δ} {Δ' = Δ'} {Δ'' = τ ∷ᵥ Δ''}
    Δ⊢ts₁∈Δ' (anf-cons Δ''++Δ'≡Δs Δ'⊢xs∈Δ'' Δs⊢x∈τ) =
  anf-cons {Γs = (Δ'' ++ᵥ Δ') ++ᵥ Δ}
    refl
    (block-typ-extend Δ⊢ts₁∈Δ' Δ'⊢xs∈Δ'')
    {!!}


evalms-fresh-grows : ∀{Γ : Ctx Staged n} {env : Env Γ} {τ} {e : Tm _ τ _} {v} →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  fresh ≤ fresh'
evalms-fresh-grows (evalms-C x) = ≤-refl
evalms-fresh-grows (evalms-V i v x) = ≤-refl
evalms-fresh-grows evalms-λ = ≤-refl
evalms-fresh-grows (evalms-$ e₁⇓ e₂⇓ body⇓) =
  ≤-trans₃
    (evalms-fresh-grows e₁⇓)
    (evalms-fresh-grows e₂⇓)
    (evalms-fresh-grows body⇓)
evalms-fresh-grows (evalms-let e₁⇓ e₂⇓) =
  ≤-trans (evalms-fresh-grows e₁⇓) (evalms-fresh-grows e₂⇓)
evalms-fresh-grows (evalms-+ _ e₁⇓ e₂⇓) =
  ≤-trans (evalms-fresh-grows e₁⇓) (evalms-fresh-grows e₂⇓)
evalms-fresh-grows (evalms-CC e⇓) = evalms-fresh-grows e⇓
evalms-fresh-grows (evalms-++ e₁⇓ e₂⇓) =
  a≤b⇒a≤1+b (≤-trans (evalms-fresh-grows e₁⇓) (evalms-fresh-grows e₂⇓))

evalms-typed : ∀{Γ : Ctx Staged n} {env : Env Γ} {τ} {e : Tm _ τ _} {v} →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  (Δ : Ctx Base fresh) →
  Σ[ Δ' ∈ Ctx Base (fresh' ∸ fresh) ](Δ ⊢ts ts ∈ Δ')
evalms-typed {fresh = i} (evalms-C _) Δ rewrite n∸n≡0 i = [] , anf-nil
evalms-typed {fresh = i} (evalms-V _ _ _) Δ rewrite n∸n≡0 i = [] , anf-nil
evalms-typed {fresh = i} evalms-λ Δ rewrite n∸n≡0 i = [] , anf-nil
evalms-typed (evalms-$ x x₁ x₂) Δ = {! !}
evalms-typed
  (evalms-let
    {fresh = i} {fresh' = i'} {fresh'' = i''}
    e₁⇓[ts₁,x] e₂⇓[ts₂,v]) Δ = Δout , {!!}
  where
    IH₁ = evalms-typed e₁⇓[ts₁,x] Δ
    i≤i' = evalms-fresh-grows e₁⇓[ts₁,x]
    Δ' = proj₁ IH₁
    Δ⊢ts₁∈Δ' = proj₂ IH₁

    Δs : Ctx Base i'
    Δs rewrite sym (m∸n+n≡m i≤i') =  Δ' ++ᵥ Δ

    IH₂ = evalms-typed e₂⇓[ts₂,v] Δs
    i'≤i'' = evalms-fresh-grows e₂⇓[ts₂,v]
    Δ'' = proj₁ IH₂
    Δ'⊢ts₂∈Δ'' = proj₂ IH₂

    Δout : Ctx Base (i'' ∸ i)
    Δout rewrite sym (a∸b+b∸c≡a∸c i'≤i'' i≤i') = Δ'' ++ᵥ Δ'
evalms-typed (evalms-+ x x₁ x₂) Δ = {! !}
evalms-typed (evalms-CC e) Δ = evalms-typed e Δ
evalms-typed (evalms-++ x x₁) Δ = {! !}
