module Lms.STLC.Properties where

-- Metatheory and miscellaneous properties of λLMS.
--
-- The key theorems are the various `evalms-_-typed` terms, which establish that
-- the IR produced by evaluating a staged λLMS term is well-typed.

open import Data.Nat as Nat
open import Data.Nat.Properties as Nat
open import Data.Product as Prod
open import Data.Vec as Vec
  using ([])
  renaming (_∷_ to _∷ᵥ_; _++_ to _++ᵥ_)
open import Data.Vec.Properties as Vec using ()
open import Data.List as List
  using (List; length)
  renaming (_∷_ to _∷ₗ_; [] to nilₗ; _++_ to _++ₗ_)
open import Data.List.Properties as List using ()
open import Relation.Binary.PropositionalEquality

open import Data.Context as Context
  renaming (here to chere; there to cthere)
  hiding (Ctx)
open import Data.Store as Store

open import Data.Nat.Extensions
open import Data.Vec.Extensions as Vec
open import Data.Product.Extensions as Prod
open import Lms.STLC

private variable
  T : Set
  w : W
  n n' n'' m m' : ℕ
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

infix 4 _⊩_
data _⊩_ : ∀ {τ : Typ Staged} → Ctx Base n → Val Staged τ → Set
data _⋖_ : ∀ {Γ : Ctx Staged n} → (env : Env Γ) → (Δ : Ctx Base m) → Set

data _⊩_ where
  -- Constants don't interact with Δ at all
  admit-N : ∀(Δ : Ctx Base n) v → Δ ⊩ Const v
  -- Closures must contain some context against which their closed-over
  -- environment is valid
  admit-=> :
    ∀ {Δ : Ctx Base n} {τ₁ τ₂}
      {Γ : Ctx Staged m} {env : Env Γ} (body : Tm _ τ₂ (τ₁ ∷ Γ)) →
    Σ₂[ inner ∈ ℕ , Δ' ∈ Ctx Base inner ](env ⋖ Δ') →
    Δ ⊩ Closure env body
  -- Code snippets should be well-typed against Δ
  admit-Code : ∀{Δ : Ctx Base n} {v τ} → Δ ⊢v v ∈ τ → Δ ⊩ Code τ v

infix 4 _⋖_
data _⋖_ where
  nil-valid : (Δ : Ctx Base m) → nil ⋖ Δ
  cons-valid :
    ∀ {Γ : Ctx Staged n} {env : Env Γ} {τ}
      {Δ : Ctx Base m} {v : Val Staged τ} → Δ ⊩ v →
    env ⋖ Δ → cons v env ⋖ Δ

⋖-lookup :
  ∀{Γ : Ctx Staged n} {env : Env Γ} {Δ : Ctx Base m} {τ i v} →
  env ⋖ Δ → env [ i ]↦ v ∈ τ →
  Δ ⊩ v
⋖-lookup (cons-valid Δ⊩v env⋖Δ) here = Δ⊩v
⋖-lookup (cons-valid _ env⋖Δ) (there env[i]=v) = ⋖-lookup env⋖Δ env[i]=v

⋖-lookup-closure :
  ∀ {Γ : Ctx Staged n} {env : Env Γ}
    {Γ' : Ctx Staged n'} {env' : Env Γ'}
    {Δ : Ctx Base m}
    {i τ₁ τ₂} {body : Tm _ τ₂ (τ₁ ∷ Γ')} →
  env ⋖ Δ → env [ i ]↦ Closure env' body ∈ (τ₁ => τ₂) →
  (Σ₂[ m' ∈ ℕ , Δ' ∈ Ctx Base m' ](env' ⋖ Δ'))
⋖-lookup-closure (cons-valid (admit-=> body result) env⋖Δ) here = result
⋖-lookup-closure (cons-valid (admit-N _ _) env⋖Δ) (there env[i]=v) =
  ⋖-lookup-closure env⋖Δ env[i]=v
⋖-lookup-closure (cons-valid (admit-=> _ _) env⋖Δ) (there env[i]=v) =
  ⋖-lookup-closure env⋖Δ env[i]=v
⋖-lookup-closure (cons-valid (admit-Code _) env⋖Δ) (there env[i]=v) =
  ⋖-lookup-closure env⋖Δ env[i]=v

launder-⋖ :
  ∀ {Γ : Ctx Staged n} {env : Env Γ}
    {Δ : Ctx Base m} {Δ' : Ctx Base m'} →
  Δ ≅ Δ' → env ⋖ Δ →
  env ⋖ Δ'
launder-⋖ Δ≅Δ' (nil-valid Δ) = nil-valid _
launder-⋖ Δ≅Δ' (cons-valid (admit-N Δ v) env⋖Δ) =
  cons-valid (admit-N _ v) (launder-⋖ Δ≅Δ' env⋖Δ)
launder-⋖ Δ≅Δ' (cons-valid (admit-=> body info) env⋖Δ) =
  cons-valid (admit-=> body info) (launder-⋖ Δ≅Δ' env⋖Δ)
launder-⋖ Δ≅Δ' (cons-valid (admit-Code Δ⊢v∈τ) env⋖Δ) =
  cons-valid (admit-Code (vl-launder-ctx Δ≅Δ' Δ⊢v∈τ)) (launder-⋖ Δ≅Δ' env⋖Δ)

wk-⊩ : ∀{Δ : Ctx Base n} {τ} τ' {v : Val Staged τ} → Δ ⊩ v → τ' ∷ Δ ⊩ v
wk-⊩ τ' (admit-N Δ v) = admit-N (τ' ∷ Δ) v
-- The added var τ is definitely not closed-over, so we don't need to traverse
-- inside the inner proof.
wk-⊩ τ' (admit-=> body info) = admit-=> body info
wk-⊩ τ' (admit-Code Δ⊢v∈τ) = admit-Code (vl-typ-wk τ' Δ⊢v∈τ)

wk-⋖ : ∀{Γ : Ctx Staged n} {env : Env Γ} {Δ : Ctx Base m} τ →
  env ⋖ Δ → env ⋖ τ ∷ Δ
wk-⋖ τ (nil-valid Δ) = nil-valid (τ ∷ Δ)
wk-⋖ τ (cons-valid Δ⊩v env⋖Δ) = cons-valid (wk-⊩ τ Δ⊩v) (wk-⋖ τ env⋖Δ)

extend-⋖ :
  ∀ {Γ : Ctx Staged n} {env : Env Γ} {Δ : Ctx Base m} {Δ' : Ctx Base m'} →
  env ⋖ Δ → Δ ⊆ Δ' →
  env ⋖ Δ'
extend-⋖ env⋖Δ (⊆-refl Γ) = env⋖Δ
extend-⋖ env⋖Δ (⊆-cons τ Δ⊆Δ') = wk-⋖ τ (extend-⋖ env⋖Δ Δ⊆Δ')

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

evalms-block-typed :
  ∀ {Γ : Ctx Staged n} {env : Env Γ} {τ} {e : Tm _ τ _} {v} →
  (Δ : Ctx Base fresh) →
  env ⋖ Δ →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  Σ[ Δ' ∈ Ctx Base (fresh' ∸ fresh) ](Δ ⊢ts ts ∈ Δ')

evalms-admissible :
  ∀ {Γ : Ctx Staged n} {env : Env Γ}
    {τ e} {v : Val Staged τ} {Δ' : Ctx Base (fresh' ∸ fresh)} →
  (Δ : Ctx Base fresh) →
  env ⋖ Δ →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  Δ ⊢ts ts ∈ Δ' →
  Δ' ++ᵥ Δ ⊩ v

-- A surprisingly-messy lemma for chaining two evaluations together.
evalms-chain :
  ∀ {Γ₁ : Ctx Staged n} {env₁ : Env Γ₁}
    {Γ₂ : Ctx Staged n'} {env₂ : Env Γ₂}
    {τ₁ τ₂} {e₁ : Tm _ τ₁ _} {e₂ : Tm _ τ₂ _}
    {fresh fresh' fresh'' x₁ x₂} →
  (Δ : Ctx Base fresh) →
  env₁ ⋖ Δ →
  ((Δ' : Ctx Base (fresh' ∸ fresh)) → Δ ⊢ts ts₁ ∈ Δ' → env₂ ⋖ Δ' ++ᵥ Δ) →
  env₁ ⊢⟨ e₁ , fresh ⟩⇓⟨[ ts₁ , x₁ ], fresh' ⟩ →
  env₂ ⊢⟨ e₂ , fresh' ⟩⇓⟨[ ts₂ , x₂ ], fresh'' ⟩ →
  Σ[ Δ' ∈ Ctx Base (fresh'' ∸ fresh) ]
    (Δ ⊢ts ts₂ ++ₗ ts₁ ∈ Δ' × Δ' ++ᵥ Δ ⊩ x₁ × Δ' ++ᵥ Δ ⊩ x₁)

evalms-block-typed {fresh = i} Δ env⋖Δ (evalms-C _) rewrite n∸n≡0 i =
  [] , anf-nil
evalms-block-typed {fresh = i} Δ env⋖Δ (evalms-V _ _ _) rewrite n∸n≡0 i =
  [] , anf-nil
evalms-block-typed {fresh = i} Δ env⋖Δ evalms-λ rewrite n∸n≡0 i =
  [] , anf-nil
evalms-block-typed Δ env⋖Δ (evalms-$ x x₁ x₂) = {! !}
evalms-block-typed {env = env}
    Δ env⋖Δ
    (evalms-let
      {fresh = i} {ts₁ = ts₁} {fresh' = i'} {τ₁ = τ} {e₁ = e₁} {x = x}
      e₁⇓[ts₁,x] e₂⇓[ts₂,v]) =
  let Δ' , Δ⊢ts₂++ts₂∈Δ' , _ , _ =
        evalms-chain Δ env⋖Δ (ext-env e₁⇓[ts₁,x]) e₁⇓[ts₁,x] e₂⇓[ts₂,v]
   in Δ' , Δ⊢ts₂++ts₂∈Δ'
  where
    ext-env : {x : Val Staged τ} → env ⊢⟨ e₁ , i ⟩⇓⟨[ ts₁ , x ], i' ⟩ →
      (Δ' : Ctx Base (i' ∸ i)) → Δ ⊢ts ts₁ ∈ Δ' → cons x env ⋖ Δ' ++ᵥ Δ
    ext-env e₁⇓x Δ' Δ⊢ts₁∈Δ' =
      cons-valid (evalms-admissible Δ env⋖Δ e₁⇓x Δ⊢ts₁∈Δ') (extend-⋖ env⋖Δ (++-⊆ _ Δ'))
evalms-block-typed Δ env⋖Δ (evalms-+ refl e₁⇓[ts₁,x] e₂⇓[ts₂,v]) =
  let Δ' , Δ⊢ts₂++ts₁∈Δ' , _ , _ =
        evalms-chain Δ env⋖Δ ext-env e₁⇓[ts₁,x] e₂⇓[ts₂,v]
   in Δ' , Δ⊢ts₂++ts₁∈Δ'
  where
    ext-env = λ Δ' Δ⊢ts₁∈Δ' → extend-⋖ env⋖Δ (++-⊆ Δ Δ')
evalms-block-typed Δ env⋖Δ (evalms-CC e) = evalms-block-typed Δ env⋖Δ e
evalms-block-typed Δ env⋖Δ (evalms-++ e₁⇓[ts₁,x₁] e₂⇓[ts₂,x₂]) = {!!}

evalms-admissible Δ env⋖Δ (evalms-C x) Δ⊢ts∈Δ' = admit-N _ x
evalms-admissible Δ env⋖Δ (evalms-V i v env[i]=v) Δ⊢ts∈Δ' =
  ⋖-lookup {! env⋖Δ !} env[i]=v
evalms-admissible Δ env⋖Δ evalms-λ Δ⊢ts∈Δ' = admit-=> _ (_ , Δ , env⋖Δ)
evalms-admissible Δ env⋖Δ (evalms-$ e⇓[ts,v] e⇓[ts,v]₁ e⇓[ts,v]₂) Δ⊢ts∈Δ' = {! !}
evalms-admissible Δ env⋖Δ (evalms-let e⇓[ts,v] e⇓[ts,v]₁) Δ⊢ts∈Δ' = {! !}
evalms-admissible Δ env⋖Δ (evalms-+ x e⇓[ts,v] e⇓[ts,v]₁) Δ⊢ts∈Δ' = {! !}
evalms-admissible Δ env⋖Δ (evalms-CC e⇓[ts,v]) Δ⊢ts∈Δ' = {! !}
evalms-admissible Δ env⋖Δ (evalms-++ e⇓[ts,v] e⇓[ts,v]₁) Δ⊢ts∈Δ' = {! !}

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
    {ts₁ = ts₁} {ts₂ = ts₂}
    {env₂ = env₂}
    {fresh = i} {fresh' = i'} {fresh'' = i''}
    Δ env₁⋖Δ mk-env₂-lemma e₁⇓[ts₁,x] e₂⇓[ts₂,v] = Δout , proof , {!!} , {!!}
  where
    IH₁ = evalms-block-typed Δ env₁⋖Δ e₁⇓[ts₁,x]
    i≤i' = evalms-fresh-grows e₁⇓[ts₁,x]
    Δ' = proj₁ IH₁
    Δ⊢ts₁∈Δ' : Δ ⊢ts ts₁ ∈ Δ'
    Δ⊢ts₁∈Δ' = proj₂ IH₁

    Δs,Δ'++Δ≅Δs = Vec.launder (Δ' ++ᵥ Δ) (m∸n+n≡m i≤i')

    Δs : Ctx Base i'
    Δs = proj₁ Δs,Δ'++Δ≅Δs

    Δ'++Δ≅Δs : Δ' ++ᵥ Δ ≅ Δs
    Δ'++Δ≅Δs = proj₂ Δs,Δ'++Δ≅Δs

    env₂⋖Δ'++Δ : env₂ ⋖ Δ' ++ᵥ Δ
    env₂⋖Δ'++Δ = mk-env₂-lemma Δ' Δ⊢ts₁∈Δ'

    env₂⋖Δs : env₂ ⋖ Δs
    env₂⋖Δs = launder-⋖ Δ'++Δ≅Δs env₂⋖Δ'++Δ

    IH₂ = evalms-block-typed Δs env₂⋖Δs e₂⇓[ts₂,v]
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
