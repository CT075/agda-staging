module Data.Nat.Extensions where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

private variable
  a b c : ℕ

∣a-b∣+|b-c∣≡∣a-c∣ : ∀{a b c} → b ≤ a → c ≤ b → ∣ a - b ∣ + ∣ b - c ∣ ≡ ∣ a - c ∣
∣a-b∣+|b-c∣≡∣a-c∣ {a} {b} {c} b≤a c≤b = begin
  ∣ a - b ∣ + ∣ b - c ∣ ≡⟨ cong₂ (_+_) (m≤n⇒∣n-m∣≡n∸m b≤a) (m≤n⇒∣n-m∣≡n∸m c≤b) ⟩
  (a ∸ b) + (b ∸ c) ≡⟨ sym (+-∸-assoc _ c≤b) ⟩
  ((a ∸ b) + b) ∸ c ≡⟨ cong (_∸ c) (sym (+-∸-comm b b≤a)) ⟩
  ((a + b) ∸ b) ∸ c ≡⟨ cong (_∸ c) (m+n∸n≡m a b) ⟩
  a ∸ c ≡⟨ sym (m≤n⇒∣n-m∣≡n∸m (≤-trans c≤b b≤a)) ⟩
  ∣ a - c ∣
  ∎
  where
    open ≡-Reasoning
