module Data.Vec.Extensions where

open import Level using (Level)
open import Data.Vec
open import Data.Vec.Properties
open import Data.Product
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Relation.Binary.Definitions using (Reflexive; Symmetric)
open import Relation.Binary.PropositionalEquality

private variable
  ℓ : Level
  T : Set ℓ
  m n n' o : ℕ

infix 4 _≅_
data _≅_ {T : Set ℓ} : Vec T n → Vec T m → Set ℓ where
  ≅-nil : [] ≅ []
  ≅-cons : ∀{xs : Vec T n} {ys : Vec T m} {v} → xs ≅ ys → v ∷ xs ≅ v ∷ ys

≅-reflexive : ∀{xs ys : Vec T n} → xs ≡ ys → xs ≅ ys
≅-reflexive {xs = []} refl = ≅-nil
≅-reflexive {xs = v ∷ xs} refl = ≅-cons (≅-reflexive refl)

≅-refl : Reflexive (_≅_ {T = T} {n = n})
≅-refl = ≅-reflexive refl

launder : (xs : Vec T n) → n ≡ m → Σ[ xs' ∈ Vec T m ](xs ≅ xs')
launder xs refl = xs , ≅-refl

≅-symmetric : ∀{xs : Vec T n} {ys : Vec T m} → xs ≅ ys → ys ≅ xs
≅-symmetric ≅-nil = ≅-nil
≅-symmetric (≅-cons xs≅ys) = ≅-cons (≅-symmetric xs≅ys)

≅-len : ∀{xs : Vec T n} {ys : Vec T m} → xs ≅ ys → n ≡ m
≅-len ≅-nil = refl
≅-len (≅-cons xs≅ys) = cong suc (≅-len xs≅ys)

++-assoc-≅ : ∀ (xs : Vec T n) (ys : Vec T m) (zs : Vec T o) →
  (xs ++ ys) ++ zs ≅ xs ++ ys ++ zs
++-assoc-≅ [] ys zs = ≅-reflexive refl
++-assoc-≅ (x ∷ xs) ys zs = ≅-cons (++-assoc-≅ xs ys zs)

++-subst-≅ₗ : ∀ {xs : Vec T n} {xs' : Vec T n'} {ys : Vec T m} {zs} →
  xs ≅ xs' → xs ++ ys ≡ zs → zs ≅ xs' ++ ys
++-subst-≅ₗ ≅-nil refl = ≅-refl
++-subst-≅ₗ (≅-cons xs≅xs') refl = ≅-cons (++-subst-≅ₗ xs≅xs' refl)

++-subst-≅ᵣ : ∀ (xs : Vec T m) {ys : Vec T n} {ys' : Vec T n'} {zs} →
  ys ≅ ys' → xs ++ ys ≡ zs → zs ≅ xs ++ ys'
++-subst-≅ᵣ [] ys≅ys' refl = ys≅ys'
++-subst-≅ᵣ (x ∷ xs) ys≅ys' refl = ≅-cons (++-subst-≅ᵣ xs ys≅ys' refl)
