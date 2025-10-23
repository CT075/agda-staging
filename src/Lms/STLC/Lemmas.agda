module Lms.STLC.Lemmas where

open import Data.Nat as Nat
open import Data.Nat.Properties as Nat
open import Data.Product
open import Data.List as List
  using (List)
  renaming (_∷_ to _∷ₗ_; [] to nilₗ; _++_ to _++ₗ_)
open import Relation.Binary.PropositionalEquality

open import Data.Vec.Extensions
open import Lms.STLC

private variable
  T : Set
  n n' : ℕ
  fresh fresh' fresh'' fresh''' : ℕ
  ts ts₁ ts₂ ts₃ : List AnfTm

evalms-fresh : ∀{Γ : Ctx Staged n} {env : Env Γ} {τ} {e : Tm _ τ _} {v} →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  fresh ≤ fresh' × ∣ fresh' - fresh ∣ ≡ List.length ts
evalms-fresh {fresh = fresh} (evalms-C _) = ≤-refl , ∣n-n∣≡0 fresh
evalms-fresh {fresh = fresh} {Γ = Γ} {τ = .(rlookup Γ i)} {e = V i refl} (evalms-V _ _ refl) = ? --≤-refl , ∣n-n∣≡0 fresh
