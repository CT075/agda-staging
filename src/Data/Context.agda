module Data.Context where

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Level renaming (suc to lsuc; zero to lzero)
import Data.Vec as Vec
open import Data.Empty as Void
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Data.Vec.Extensions

open Vec using ([]; _∷_) public
open Vec hiding (_[_]=_)

private variable
  ℓ : Level
  T : Set ℓ
  t t' : T
  m n n' o i : ℕ

-- We use De Bruijin levels with *reversed* contexts. That is, index 0 refers
-- to the rightmost element of `Γ`. This is because Agda is better-behaved when
-- we use the constructor `∷` instead of the recursive function `∷ʳ` in type
-- formers.

Ctx : Set ℓ → ℕ → Set ℓ
Ctx = Vec

data _[_]=_ {T : Set ℓ} : Ctx T n → ℕ → T → Set ℓ where
  here : ∀{Γ : Ctx T n} → (t ∷ Γ)[ n ]= t
  there : ∀{Γ : Ctx T n} → Γ [ i ]= t → (t' ∷ Γ)[ i ]= t

[]=→< : ∀{Γ : Ctx T n} {t : T} → Γ [ i ]= t → i < n
[]=→< here = n<1+n _
[]=→< (there Γ[i]=t) = m<n⇒m<1+n ([]=→< Γ[i]=t)

[]=-unique : ∀{Γ : Ctx T n} {i t₁ t₂} → Γ [ i ]= t₁ → Γ [ i ]= t₂ → t₁ ≡ t₂
[]=-unique here here = refl
[]=-unique here (there Γ[i]=t) = ⊥-elim (<-irrefl refl ([]=→< Γ[i]=t))
[]=-unique (there Γ[i]=t) here = ⊥-elim (<-irrefl refl ([]=→< Γ[i]=t))
[]=-unique (there p₁) (there p₂) = []=-unique p₁ p₂

launder-[]= : ∀{Γ : Ctx T n} {Δ : Ctx T m} {i t} →
  Γ ≅ Δ → Γ [ i ]= t → Δ [ i ]= t
launder-[]= = ≅-subst _

infix 4 _⊆_
data _⊆_ {T : Set ℓ} : Ctx T n → Ctx T n' → Set ℓ where
  ⊆-refl : (Γ : Ctx T n) → Γ ⊆ Γ
  ⊆-cons : ∀{Γ : Ctx T n} {Γ' : Ctx T n'} → (t : T) → Γ ⊆ Γ' → Γ ⊆ (t ∷ Γ')

⊆-uncons : ∀ {Γ : Ctx T n} {Γ' : Ctx T n'} {t} → t ∷ Γ ⊆ Γ' → Γ ⊆ Γ'
⊆-uncons (⊆-refl _) = ⊆-cons _ (⊆-refl _)
⊆-uncons (⊆-cons t t∷Γ⊆Γ') = ⊆-cons t (⊆-uncons t∷Γ⊆Γ')

++-⊆ : ∀(Γ : Ctx T n) (Γ' : Ctx T n') → Γ ⊆ (Γ' ++ Γ)
++-⊆ Γ [] = ⊆-refl Γ
++-⊆ Γ (t ∷ Γ') = ⊆-cons t (++-⊆ Γ Γ')

xs⊆ys⇒xs++zs⊆ys++zs : ∀{xs : Ctx T n} {ys : Ctx T m} {zs : Ctx T o} →
  xs ⊆ ys → (xs ++ zs) ⊆ (ys ++ zs)
xs⊆ys⇒xs++zs⊆ys++zs (⊆-refl xs) = ⊆-refl (xs ++ _)
xs⊆ys⇒xs++zs⊆ys++zs (⊆-cons t xs⊆ys) = ⊆-cons t (xs⊆ys⇒xs++zs⊆ys++zs xs⊆ys)
