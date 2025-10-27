module Lms.STLC.Lemmas where

open import Data.Nat as Nat
open import Data.Nat.Properties as Nat
open import Data.Product
open import Data.Vec as Vec
  using ([])
  renaming (_∷_ to _∷ᵥ_; _++_ to _++ᵥ_)
open import Data.Vec.Properties as Vec using ()
open import Data.List as List
  using (List; length)
  renaming (_∷_ to _∷ₗ_; [] to nilₗ; _++_ to _++ₗ_)
open import Data.List.Properties as List using ()
open import Relation.Binary.PropositionalEquality

open import Data.Context
  renaming (here to chere; there to cthere)
  hiding (Ctx)

open import Data.Nat.Extensions
open import Data.Vec.Extensions as Vec
open import Lms.STLC

private variable
  T : Set
  n n' n'' m : ℕ
  fresh fresh' fresh'' fresh''' : ℕ
  ts ts₁ ts₂ ts₃ : List AnfTm

vl-launder-ctx : ∀{Δ : Ctx Base n} {Δ' : Ctx Base m} {v τ} →
  Δ ≅ Δ' → Δ ⊢v v ∈ τ →
  Δ' ⊢v v ∈ τ
vl-launder-ctx Δ≅Δ' (anf-c x) = anf-c x
vl-launder-ctx Δ≅Δ' (anf-v Δ[i]=τ) = anf-v (launder-[]= Δ≅Δ' Δ[i]=τ)

tm-launder-ctx : ∀{Δ : Ctx Base n} {Δ' : Ctx Base m} {t τ} →
  Δ ≅ Δ' → Δ ⊢t t ∈ τ →
  Δ' ⊢t t ∈ τ

block-launder-ctx : ∀{Δ : Ctx Base n} {Δ' : Ctx Base m} {Δout : Ctx Base n'} →
  Δ ≅ Δ' → Δ ⊢ts ts ∈ Δout →
  Δ' ⊢ts ts ∈ Δout

tm-launder-ctx Δ≅Δ' (anf-+ Δ⊢v₁∈N Δ⊢v₂∈N) =
  anf-+ (vl-launder-ctx Δ≅Δ' Δ⊢v₁∈N) (vl-launder-ctx Δ≅Δ' Δ⊢v₂∈N)
tm-launder-ctx Δ≅Δ' (anf-$ Δ⊢t₁∈τ₁=>τ₂ Δ⊢t₂∈τ₁) =
  anf-$ (vl-launder-ctx Δ≅Δ' Δ⊢t₁∈τ₁=>τ₂) (vl-launder-ctx Δ≅Δ' Δ⊢t₂∈τ₁)
tm-launder-ctx {Δ = Δ} {Δ' = Δ'}
    Δ≅Δ' (anf-λ {Γ' = Δout} τ refl Δ⊢ts∈Δout Δs⊢v∈τ') =
  anf-λ {Γs = Δout ++ᵥ Δ'}
    τ
    refl
    (block-launder-ctx (≅-cons Δ≅Δ') Δ⊢ts∈Δout)
    (vl-launder-ctx (≅-cons (++-subst-≅ᵣ Δout Δ≅Δ' refl)) Δs⊢v∈τ')

block-launder-ctx Δ≅Δ' anf-nil = anf-nil
block-launder-ctx Δ≅Δ' (anf-cons refl Δ⊢ts∈Δout Δout++Δ⊢v∈τ) =
  anf-cons
    refl
    (block-launder-ctx Δ≅Δ' Δ⊢ts∈Δout)
    (tm-launder-ctx (++-subst-≅ᵣ _ Δ≅Δ' refl) Δout++Δ⊢v∈τ)

block-launder-out : ∀{Δ : Ctx Base m} {Γ : Ctx Base n} {Γ' : Ctx Base n'} {ts} →
  Γ ≅ Γ' → Δ ⊢ts ts ∈ Γ →
  Δ ⊢ts ts ∈ Γ'
block-launder-out ≅-nil anf-nil = anf-nil
block-launder-out (≅-cons Γ≅Γ') (anf-cons refl Δ⊢ts∈Γ Γ++Δ⊢x∈τ) =
  anf-cons
    refl
    (block-launder-out Γ≅Γ' Δ⊢ts∈Γ)
    (tm-launder-ctx (++-subst-≅ₗ Γ≅Γ' refl) Γ++Δ⊢x∈τ)

vl-typ-wk : ∀{Δ : Ctx Base n} {v τ} τ' → Δ ⊢v v ∈ τ → τ' ∷ᵥ Δ ⊢v v ∈ τ
vl-typ-wk τ (anf-c x) = anf-c x
vl-typ-wk τ (anf-v pf) = anf-v (cthere pf)

vl-typ-extend : ∀{Δ : Ctx Base n} {Δs : Ctx Base n'} {v τ} →
  Δ ⊆ Δs → Δ ⊢v v ∈ τ →
  Δs ⊢v v ∈ τ
vl-typ-extend (⊆-refl Δ) Δ⊢v∈τ = Δ⊢v∈τ
vl-typ-extend (⊆-cons τ' Δ⊆Δ') Δ⊢v∈τ = vl-typ-wk τ' (vl-typ-extend Δ⊆Δ' Δ⊢v∈τ)

block-typ-size : ∀{Δ : Ctx Base n} {Δ' : Ctx Base n'} →
  Δ ⊢ts ts ∈ Δ' →
  length ts ≡ n'
block-typ-size anf-nil = refl
block-typ-size (anf-cons Δ'++Δ≡Δs Δ⊢xs∈Δ' Δs⊢x∈τ) =
  cong suc (block-typ-size Δ⊢xs∈Δ')

block-typ-join : ∀{Δ : Ctx Base n} {Δ' : Ctx Base n'} {Δ'' : Ctx Base n''} →
  Δ ⊢ts ts₁ ∈ Δ' → Δ' ++ᵥ Δ ⊢ts ts₂ ∈ Δ'' →
  Δ ⊢ts ts₂ ++ₗ ts₁ ∈ Δ'' ++ᵥ Δ'
block-typ-join Δ⊢ts₁∈Δ' anf-nil = Δ⊢ts₁∈Δ'
block-typ-join {Δ = Δ} {Δ' = Δ'} {Δ'' = τ ∷ᵥ Δ''}
    Δ⊢ts₁∈Δ' (anf-cons {Γs = Δs} {x = x} refl Δ'⊢xs∈Δ'' Δs⊢x∈τ) =
  anf-cons {Γs = (Δ'' ++ᵥ Δ') ++ᵥ Δ}
    refl
    (block-typ-join Δ⊢ts₁∈Δ' Δ'⊢xs∈Δ'')
    [Δ''++Δ']++Δ⊢x∈τ
  where
    [Δ''++Δ']++Δ⊢x∈τ : (Δ'' ++ᵥ Δ') ++ᵥ Δ ⊢t x ∈ τ
    [Δ''++Δ']++Δ⊢x∈τ = tm-launder-ctx (≅-symmetric (++-assoc-≅ Δ'' Δ' Δ)) Δs⊢x∈τ

evalms-fresh-grows : ∀{Γ : Ctx Staged n} {env : Env Γ} {τ} {e : Tm _ τ _} {v} →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  fresh ≤ fresh'
evalms-fresh-grows (evalms-C x) = ≤-refl
evalms-fresh-grows (evalms-V i v x) = ≤-refl
evalms-fresh-grows evalms-λ = ≤-refl
evalms-fresh-grows (evalms-$ e₁⇓ e₂⇓ body⇓) =
  ≤-trans₃
    (evalms-fresh-grows e₁⇓)
    (evalms-fresh-grows e₂⇓)
    (evalms-fresh-grows body⇓)
evalms-fresh-grows (evalms-let e₁⇓ e₂⇓) =
  ≤-trans (evalms-fresh-grows e₁⇓) (evalms-fresh-grows e₂⇓)
evalms-fresh-grows (evalms-+ _ e₁⇓ e₂⇓) =
  ≤-trans (evalms-fresh-grows e₁⇓) (evalms-fresh-grows e₂⇓)
evalms-fresh-grows (evalms-CC e⇓) = evalms-fresh-grows e⇓
evalms-fresh-grows (evalms-++ e₁⇓ e₂⇓) =
  a≤b⇒a≤1+b (≤-trans (evalms-fresh-grows e₁⇓) (evalms-fresh-grows e₂⇓))

evalms-chain : ∀
  {Γ₁ : Ctx Staged n} {env₁ : Env Γ₁}
  {Γ₂ : Ctx Staged n'} {env₂ : Env Γ₂}
  {τ₁ τ₂}
  {e₁ : Tm _ τ₁ _} {e₂ : Tm _ τ₂ _} {x v} →
  env₁ ⊢⟨ e₁ , fresh ⟩⇓⟨[ ts₁ , x ], fresh' ⟩ →
  env₂ ⊢⟨ e₂ , fresh' ⟩⇓⟨[ ts₂ , v ], fresh'' ⟩ →
  (Δ : Ctx Base fresh) →
  Σ[ Δ' ∈ Ctx Base (fresh'' ∸ fresh) ](Δ ⊢ts ts₂ ++ₗ ts₁ ∈ Δ')

evalms-typed : ∀{Γ : Ctx Staged n} {env : Env Γ} {τ} {e : Tm _ τ _} {v} →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  (Δ : Ctx Base fresh) →
  Σ[ Δ' ∈ Ctx Base (fresh' ∸ fresh) ](Δ ⊢ts ts ∈ Δ')

-- The reason this is so complicated despite basically being "cite the
-- inductive hypothesis twice" is due to Agda not pushing equalities through
-- "two levels" of types. If we have `Δ₁ : Ctx Base n₁` and `Δ₂ : Ctx Base n₂`
-- where `Δ₁` and `Δ₂` appear in the *type*, it's difficult to even state the
-- equality `Δ₁ ≡ Δ₂` (e.g. for a rewrite) because `n₁` and `n₂` aren't
-- syntactically the same, even if we know that `n₁ ≡ n₂`.
--
-- Typically, this is resolved via chained `with`-clauses, where we first match
-- on `n₁ ≡ n₂` so that the type `Δ₁ ≡ Δ₂` can be formed, then further matching
-- on that evidence to allow for unification. However, I tend to find that
-- style frustrating to actually write due to the error messages rapidly
-- becoming unreadable (especially in this proof that requires unwrapping a
-- bunch of dependent sums).
--
-- Instead, we manipulate the "length-agnostic" equality `_≅_` to get terms of
-- the expected (syntactic) type.
evalms-chain
    {fresh = i} {ts₁ = ts₁}
    {fresh' = i'} {ts₂ = ts₂}
    {fresh'' = i''}
    e₁⇓[ts₁,x] e₂⇓[ts₂,v] Δ = Δout , proof
  where
    IH₁ = evalms-typed e₁⇓[ts₁,x] Δ
    i≤i' = evalms-fresh-grows e₁⇓[ts₁,x]
    Δ' = proj₁ IH₁
    Δ⊢ts₁∈Δ' : Δ ⊢ts ts₁ ∈ Δ'
    Δ⊢ts₁∈Δ' = proj₂ IH₁

    Δs,Δ'++Δ≅Δs = Vec.launder (Δ' ++ᵥ Δ) (m∸n+n≡m i≤i')

    Δs : Ctx Base i'
    Δs = proj₁ Δs,Δ'++Δ≅Δs

    Δ'++Δ≅Δs : Δ' ++ᵥ Δ ≅ Δs
    Δ'++Δ≅Δs = proj₂ Δs,Δ'++Δ≅Δs

    IH₂ = evalms-typed e₂⇓[ts₂,v] Δs
    i'≤i'' = evalms-fresh-grows e₂⇓[ts₂,v]
    Δ'' = proj₁ IH₂
    Δs⊢ts₂∈Δ'' : Δs ⊢ts ts₂ ∈ Δ''
    Δs⊢ts₂∈Δ'' = proj₂ IH₂

    Δ'++Δ⊢ts₂∈Δ'' : Δ' ++ᵥ Δ ⊢ts ts₂ ∈ Δ''
    Δ'++Δ⊢ts₂∈Δ'' = block-launder-ctx (≅-symmetric Δ'++Δ≅Δs) Δs⊢ts₂∈Δ''

    Δout,Δ''++Δ'≅Δout = Vec.launder (Δ'' ++ᵥ Δ') (a∸b+b∸c≡a∸c i'≤i'' i≤i')

    Δout : Ctx Base (i'' ∸ i)
    Δout = proj₁ Δout,Δ''++Δ'≅Δout

    Δ''++Δ'≅Δout : Δ'' ++ᵥ Δ' ≅ Δout
    Δ''++Δ'≅Δout = proj₂ Δout,Δ''++Δ'≅Δout

    Δ⊢ts₂++ts₂∈Δ''++Δ' : Δ ⊢ts ts₂ ++ₗ ts₁ ∈ Δ'' ++ᵥ Δ'
    Δ⊢ts₂++ts₂∈Δ''++Δ' = block-typ-join Δ⊢ts₁∈Δ' Δ'++Δ⊢ts₂∈Δ''

    proof : Δ ⊢ts ts₂ ++ₗ ts₁ ∈ Δout
    proof = block-launder-out Δ''++Δ'≅Δout Δ⊢ts₂++ts₂∈Δ''++Δ'

evalms-typed {fresh = i} (evalms-C _) Δ rewrite n∸n≡0 i = [] , anf-nil
evalms-typed {fresh = i} (evalms-V _ _ _) Δ rewrite n∸n≡0 i = [] , anf-nil
evalms-typed {fresh = i} evalms-λ Δ rewrite n∸n≡0 i = [] , anf-nil
evalms-typed (evalms-$ x x₁ x₂) Δ = {! !}
evalms-typed (evalms-let e₁⇓[ts₁,x] e₂⇓[ts₂,v]) Δ =
  evalms-chain e₁⇓[ts₁,x] e₂⇓[ts₂,v] Δ
evalms-typed (evalms-+ refl e₁⇓[ts₁,x] e₂⇓[ts₂,v]) Δ =
  evalms-chain e₁⇓[ts₁,x] e₂⇓[ts₂,v] Δ
evalms-typed (evalms-CC e) Δ = evalms-typed e Δ
evalms-typed (evalms-++ e₁⇓[ts₁,x] e₂⇓[ts₂,v]) Δ = {!!} , {!!}
