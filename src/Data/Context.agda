module Data.Context where

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Level renaming (suc to lsuc; zero to lzero)
import Data.Vec as Vec

open Vec using ([]; _∷_) public
open Vec hiding (_[_]=_)

private variable
  ℓ : Level
  T : Set ℓ
  n i : ℕ

-- We use De Bruijin levels with *reversed* contexts. That is, index 0 refers
-- to the rightmost element of `Γ`. This is because Agda is better-behaved when
-- we use the constructor `∷` instead of the recursive function `∷ʳ` in type
-- formers.

Ctx : Set ℓ → ℕ → Set ℓ
Ctx = Vec

data _[_]=_ {T : Set ℓ} : Ctx T n → ℕ → T → Set ℓ where
  here : ∀{Γ : Ctx T n} {t} → (t ∷ Γ)[ n ]= t
  there : ∀{Γ : Ctx T n} {t t'} → Γ [ i ]= t → (t' ∷ Γ)[ i ]= t

[]=→< : ∀{Γ : Ctx T n} {t : T} → Γ [ i ]= t → i < n
[]=→< here = n<1+n _
[]=→< (there Γ[i]=t) = m<n⇒m<1+n ([]=→< Γ[i]=t)
