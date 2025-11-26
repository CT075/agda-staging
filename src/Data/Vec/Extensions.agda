{-# OPTIONS --safe #-}

module Data.Vec.Extensions where

open import Level using (Level; _⊔_)
open import Data.Vec
open import Data.Vec.Properties
open import Data.Product
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Relation.Binary.Definitions using (Reflexive; Transitive)
open import Relation.Binary.PropositionalEquality

private variable
  ℓ ℓ' : Level
  T : Set ℓ
  m n n' o : ℕ

infix 4 _≅_
data _≅_ {T : Set ℓ} : Vec T n → Vec T m → Set ℓ where
  ≅-nil : [] ≅ []
  ≅-cons : ∀{xs : Vec T n} {ys : Vec T m} {v} → xs ≅ ys → v ∷ xs ≅ v ∷ ys

≅⇒≡ : ∀ {xs : Vec T n} {ys : Vec T n} → xs ≅ ys → xs ≡ ys
≅⇒≡ ≅-nil = refl
≅⇒≡ (≅-cons xs≅ys) = cong _ (≅⇒≡ xs≅ys)

≅-len : ∀{xs : Vec T n} {ys : Vec T m} → xs ≅ ys → n ≡ m
≅-len ≅-nil = refl
≅-len (≅-cons xs≅ys) = cong suc (≅-len xs≅ys)

≅-subst : ∀ {T : Set ℓ} {xs : Vec T n} {ys : Vec T m} →
  (P : ∀ {len} → Vec T len → Set ℓ') → xs ≅ ys → P xs → P ys
≅-subst P xs≅ys Pxs with ≅-len xs≅ys
... | refl rewrite ≅⇒≡ xs≅ys = Pxs

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

≅-trans : ∀{xs : Vec T n} {ys : Vec T m} {zs : Vec T o} →
  xs ≅ ys → ys ≅ zs → xs ≅ zs
≅-trans xs≅ys ys≅zs with ≅-len xs≅ys | ≅-len ys≅zs
... | refl | refl = ≅-reflexive (trans (≅⇒≡ xs≅ys) (≅⇒≡ ys≅zs))

≅-cong : ∀{xs : Vec T n} {ys : Vec T m} {f : ℕ → ℕ} →
  (P : ∀ {len} → Vec T len → Vec T (f len)) → xs ≅ ys → P xs ≅ P ys
≅-cong {xs = xs} P xs≅ys with ≅-len xs≅ys
... | refl rewrite ≅⇒≡ xs≅ys = ≅-refl

≅-++-assoc : ∀ (xs : Vec T n) (ys : Vec T m) (zs : Vec T o) →
  (xs ++ ys) ++ zs ≅ xs ++ ys ++ zs
≅-++-assoc [] ys zs = ≅-reflexive refl
≅-++-assoc (x ∷ xs) ys zs = ≅-cons (≅-++-assoc xs ys zs)

++-subst-≅ₗ : ∀ {xs : Vec T n} {xs' : Vec T n'} {ys : Vec T m} {zs} →
  xs ≅ xs' → xs ++ ys ≡ zs → zs ≅ xs' ++ ys
++-subst-≅ₗ ≅-nil refl = ≅-refl
++-subst-≅ₗ (≅-cons xs≅xs') refl = ≅-cons (++-subst-≅ₗ xs≅xs' refl)

++-subst-≅ᵣ : ∀ (xs : Vec T m) {ys : Vec T n} {ys' : Vec T n'} {zs} →
  ys ≅ ys' → xs ++ ys ≡ zs → zs ≅ xs ++ ys'
++-subst-≅ᵣ [] ys≅ys' refl = ys≅ys'
++-subst-≅ᵣ (x ∷ xs) ys≅ys' refl = ≅-cons (++-subst-≅ᵣ xs ys≅ys' refl)

module ≅-Reasoning where
  begin_ : ∀{xs : Vec T n} {ys : Vec T m} → xs ≅ ys → xs ≅ ys
  begin xs≅ys = xs≅ys

  _∎ : (xs : Vec T n) → xs ≅ xs
  _∎ xs = ≅-refl

  _≅⟨⟩_ : ∀(xs : Vec T n) {ys : Vec T m} → xs ≅ ys → xs ≅ ys
  xs ≅⟨⟩ xs≅ys = xs≅ys

  step-syntax : ∀(xs : Vec T n) {ys : Vec T m} {zs : Vec T o} →
    xs ≅ ys → ys ≅ zs → xs ≅ zs
  step-syntax xs = ≅-trans

  infix 1 begin_
  infixr 2 _≅⟨⟩_ step-syntax
  infix 3 _∎

  syntax step-syntax xs xs≅ys ys≅zs = xs ≅⟨ xs≅ys ⟩ ys≅zs

infixr 4 _,ᵥ_
record ∃ᵥ-syntax {a b : Level} {T : Set a} (P : ∀{n} → Vec T n → Set b) :
    Set (a ⊔ b)
  where
  constructor _,ᵥ_
  field
    {len} : ℕ
    prjᵥ : Vec T len
    prjₒ : P prjᵥ

syntax ∃ᵥ-syntax (λ xs → P) = ∃ᵥ[ xs ] P
