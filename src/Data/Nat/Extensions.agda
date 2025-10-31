module Data.Nat.Extensions where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

private variable
  a b c d : ℕ

a∸b+b∸c≡a∸c : ∀{a b c} → b ≤ a → c ≤ b → (a ∸ b) + (b ∸ c) ≡ a ∸ c
a∸b+b∸c≡a∸c {a} {b} {c} b≤a c≤b = begin
  (a ∸ b) + (b ∸ c) ≡⟨ sym (+-∸-assoc _ c≤b) ⟩
  ((a ∸ b) + b) ∸ c ≡⟨ cong (_∸ c) (sym (+-∸-comm b b≤a)) ⟩
  ((a + b) ∸ b) ∸ c ≡⟨ cong (_∸ c) (m+n∸n≡m a b) ⟩
  a ∸ c ∎
  where
    open ≡-Reasoning

a≤b⇒a≤1+b : a ≤ b → a ≤ suc b
a≤b⇒a≤1+b z≤n = z≤n
a≤b⇒a≤1+b (s≤s m≤n) = s≤s (a≤b⇒a≤1+b m≤n)

≤-trans₃ : a ≤ b → b ≤ c → c ≤ d → a ≤ d
≤-trans₃ a≤b b≤c c≤d = ≤-trans (≤-trans a≤b b≤c) c≤d

1+[a∸b]≡[1+a]∸b : ∀{a b} → b ≤ a → suc (a ∸ b) ≡ suc a ∸ b
1+[a∸b]≡[1+a]∸b z≤n = refl
1+[a∸b]≡[1+a]∸b (s≤s b≤a) = 1+[a∸b]≡[1+a]∸b b≤a
