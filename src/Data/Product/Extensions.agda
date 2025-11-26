{-# OPTIONS --safe #-}

module Data.Product.Extensions where

open import Level
open import Data.Product

private variable
  a b c : Level

Σ₂-syntax :
  (A : Set a) → (B : A → Set b) → ((x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
Σ₂-syntax A B P = Σ[ x ∈ A ](Σ[ y ∈ B x ](P x y))

-- This isn't a real dependent triple, because `P` cannot depend on `x`
-- directly.
syntax Σ₂-syntax A (λ x → B) (λ _ y → P) = Σ₂[ x ∈ A , y ∈ B ] P
