module Data.Vec.Extensions where

open import Data.Vec
open import Data.Vec.Properties
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality

private variable
  T : Set
  n : ℕ

rlookup : Vec T n → Fin n → T
rlookup xs i = lookup (reverse xs) i

rlookup-defn : (xs : Vec T n) → (i : Fin n) →
  rlookup xs i ≡ lookup (reverse xs) i
rlookup-defn xs i = refl

lookup-snoc : ∀ (xs : Vec T n) x (i : Fin n) →
  lookup (xs ∷ʳ x) (Fin.inject₁ i) ≡ lookup xs i
lookup-snoc (x' ∷ xs) x Fin.zero = refl
lookup-snoc (x' ∷ xs) x (Fin.suc i) = begin
  lookup ((x' ∷ xs) ∷ʳ x) (Fin.inject₁ (Fin.suc i)) ≡⟨⟩
  lookup (x' ∷ (xs ∷ʳ x)) (Fin.suc (Fin.inject₁ i)) ≡⟨⟩
  lookup (xs ∷ʳ x) (Fin.inject₁ i) ≡⟨ lookup-snoc xs x i ⟩
  lookup xs i ≡⟨⟩
  lookup (x' ∷ xs) (Fin.suc i)
  ∎
  where open ≡-Reasoning

rlookup-cons : ∀ x → (xs : Vec T n) → (i : Fin n) →
  rlookup (x ∷ xs) (Fin.inject₁ i) ≡ rlookup xs i
rlookup-cons x xs i = begin
  rlookup (x ∷ xs) (Fin.inject₁ i) ≡⟨⟩
  lookup (reverse (x ∷ xs)) (Fin.inject₁ i) ≡⟨ lemma ⟩
  lookup (reverse xs ∷ʳ x) (Fin.inject₁ i) ≡⟨ lookup-snoc (reverse xs) x i ⟩
  lookup (reverse xs) i ≡⟨⟩
  rlookup xs i
  ∎
  where
    open ≡-Reasoning
    lemma = cong (λ t → lookup t (Fin.inject₁ i)) (reverse-∷ x xs)
