module Data.Store where

open import Data.Nat
open import Level renaming (suc to lsuc; zero to lzero)

open import Data.Context renaming (here to chere; there to cthere)

private variable
  ℓ : Level
  Typ : Set ℓ
  Val : Typ → Set ℓ
  n i : ℕ

data Store (Typ : Set ℓ) (Val : Typ → Set ℓ) : Ctx Typ n → Set ℓ where
  nil : Store Typ Val []
  cons : ∀{t} {Γ : Ctx Typ n} → Val t → Store Typ Val Γ → Store Typ Val (t ∷ Γ)

-- This can't be defined as `env[i]↦v∈τ` directly because `v` depends on `τ`.
data MapsTo {Typ : Set ℓ} {Val : Typ → Set ℓ} : {Γ : Ctx Typ n} →
  Store Typ Val Γ → ℕ → (τ : Typ) → Val τ → Set ℓ
  where
  here : ∀{Γ : Ctx Typ n} {env : Store Typ Val Γ} {τ v} →
    MapsTo (cons v env) n τ v
  there : ∀{Γ : Ctx Typ n} {env : Store Typ Val Γ} {τ τ' v} {v' : Val τ'} →
    MapsTo env i τ v →
    MapsTo (cons v' env) i τ v

store-lookup-syntax = MapsTo
syntax store-lookup-syntax env i τ v = env [ i ]↦ v ∈ τ

store-typing : ∀{Typ : Set ℓ} {Val} {Γ : Ctx Typ n}
  {env : Store Typ Val Γ} {i τ v} →
  env [ i ]↦ v ∈ τ → Γ [ i ]= τ
store-typing here = chere
store-typing (there env[i]↦v) = cthere (store-typing env[i]↦v)
