module Lms.STLC.WellFormed where

-- Metatheory and miscellaneous properties of λLMS, establishing that generated
-- code is well-scoped and well-typed.
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

open import Lms.STLC.Core
open import Lms.STLC.IR renaming (Expr to AnfExpr)
open import Lms.STLC.Evaluation

private variable
  T : Set
  w : W
  n n' n'' m m' : ℕ
  fresh fresh' fresh'' fresh''' : ℕ
  ts ts₁ ts₂ ts₃ : List AnfExpr

-- All these `launder` lemmas were written before I figured out how to write
-- `≅-subst`, and removing them makes inference messier.

vl-launder-ctx : ∀{Δ : Ctx Base n} {Δ' : Ctx Base m} {v τ} →
  Δ ≅ Δ' → Δ ⊢v v ∈ τ →
  Δ' ⊢v v ∈ τ
vl-launder-ctx = ≅-subst _

tm-launder-ctx : ∀{Δ : Ctx Base n} {Δ' : Ctx Base m} {t τ} →
  Δ ≅ Δ' → Δ ⊢t t ∈ τ →
  Δ' ⊢t t ∈ τ
tm-launder-ctx = ≅-subst _

block-launder-ctx : ∀{Δ : Ctx Base n} {Δ' : Ctx Base m} {Δout : Ctx Base n'} →
  Δ ≅ Δ' → Δ ⊢ts ts ∈ Δout →
  Δ' ⊢ts ts ∈ Δout
block-launder-ctx = ≅-subst _

block-launder-out : ∀{Δ : Ctx Base m} {Γ : Ctx Base n} {Γ' : Ctx Base n'} {ts} →
  Γ ≅ Γ' → Δ ⊢ts ts ∈ Γ →
  Δ ⊢ts ts ∈ Γ'
block-launder-out = ≅-subst _

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
    [Δ''++Δ']++Δ⊢x∈τ = tm-launder-ctx (≅-symmetric (≅-++-assoc Δ'' Δ' Δ)) Δs⊢x∈τ

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
    env ⋖ Δ →
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
  env' ⋖ Δ
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
launder-⋖ = ≅-subst _

wk-⊩ : ∀{Δ : Ctx Base n} {τ} τ' {v : Val Staged τ} → Δ ⊩ v → τ' ∷ Δ ⊩ v
wk-⋖ : ∀{Γ : Ctx Staged n} {env : Env Γ} {Δ : Ctx Base m} τ →
  env ⋖ Δ → env ⋖ τ ∷ Δ

wk-⊩ τ' (admit-N Δ v) = admit-N (τ' ∷ Δ) v
-- The added var τ is definitely not closed-over, so we don't need to traverse
-- inside the inner proof.
wk-⊩ τ' (admit-=> body env⋖Δ) = admit-=> body (wk-⋖ τ' env⋖Δ)
wk-⊩ τ' (admit-Code Δ⊢v∈τ) = admit-Code (vl-typ-wk τ' Δ⊢v∈τ)

extend-⊩ :
  ∀ {Δ : Ctx Base n} {Δ' : Ctx Base m} {τ} {v : Val Staged τ} →
  Δ ⊩ v → Δ ⊆ Δ' →
  Δ' ⊩ v
extend-⊩ Δ⊩v (⊆-refl Δ) = Δ⊩v
extend-⊩ env⊩Δ (⊆-cons τ Δ⊆Δ') = wk-⊩ τ (extend-⊩ env⊩Δ Δ⊆Δ')

wk-⋖ τ (nil-valid Δ) = nil-valid (τ ∷ Δ)
wk-⋖ τ (cons-valid Δ⊩v env⋖Δ) = cons-valid (wk-⊩ τ Δ⊩v) (wk-⋖ τ env⋖Δ)

extend-⋖ :
  ∀ {Γ : Ctx Staged n} {env : Env Γ} {Δ : Ctx Base m} {Δ' : Ctx Base m'} →
  env ⋖ Δ → Δ ⊆ Δ' →
  env ⋖ Δ'
extend-⋖ env⋖Δ (⊆-refl Δ) = env⋖Δ
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

evalms-wf :
  ∀ {Γ : Ctx Staged n} {env : Env Γ} {τ} {e : Tm _ τ _} {v} →
  (Δ : Ctx Base fresh) →
  env ⋖ Δ →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  Σ[ Δ' ∈ Ctx Base (fresh' ∸ fresh) ](Δ ⊢ts ts ∈ Δ' × Δ' ++ᵥ Δ ⊩ v)

-- A lemma for handling evaluations in sequence.
evalms-chain :
  ∀ {Γ : Ctx Staged n} {env : Env Γ} {τ} {e : Tm _ τ Γ} {v}
    (Δ : Ctx Base fresh) {Δ' : Ctx Base (fresh' ∸ fresh)} →
  fresh ≤ fresh' →
  Δ ⊢ts ts₁ ∈ Δ' → env ⋖ Δ' ++ᵥ Δ →
  env ⊢⟨ e , fresh' ⟩⇓⟨[ ts₂ , v ], fresh'' ⟩ →
  Σ[ Δout ∈ Ctx Base (fresh'' ∸ fresh) ]
    (Δ' ⊆ Δout × Δ ⊢ts ts₂ ++ₗ ts₁ ∈ Δout × Δout ++ᵥ Δ ⊩ v)

evalms-wf {fresh = i} Δ env⋖Δ (evalms-C x) rewrite n∸n≡0 i =
  [] , anf-nil , admit-N _ x
evalms-wf {fresh = i} Δ env⋖Δ (evalms-V _ _ env[i]=v) rewrite n∸n≡0 i =
  -- This `extend` is a no-op, because `Δ' : Ctx Base (fresh ∸ fresh)` is
  -- always empty. Getting Agda to realize this is quite verbose, so it's
  -- simpler to just write it this way.
  [] , anf-nil , ⋖-lookup (extend-⋖ env⋖Δ (++-⊆ _ _)) env[i]=v
evalms-wf {fresh = i} Δ env⋖Δ evalms-λ rewrite n∸n≡0 i =
  [] , anf-nil , admit-=> _ (extend-⋖ env⋖Δ (++-⊆ _ _))
evalms-wf Δ env⋖Δ
  (evalms-$
    {fresh = fresh} {fresh'' = fresh'} {fresh''' = fresh''}
    {ts₁ = ts₁} {ts₂ = ts₂} {ts₃ = ts₃}
    {env' = env'} {e' = body} {v = v}
    e₁⇓[ts₁,f] e₂⇓[ts₂,x] body⇓[ts₃,v]) = cont Δ'++Δ⊩f
  where
    IH₁ = evalms-wf Δ env⋖Δ e₁⇓[ts₁,f]
    Δ' = proj₁ IH₁
    Δ⊢ts₁∈Δ' = proj₁ (proj₂ IH₁)
    Δ'++Δ⊩f = proj₂ (proj₂ IH₁)
    fresh≤fresh' = evalms-fresh-grows e₁⇓[ts₁,f]

    IH₂ = evalms-chain Δ fresh≤fresh'
            Δ⊢ts₁∈Δ' (extend-⋖ env⋖Δ (++-⊆ _ Δ'))
            e₂⇓[ts₂,x]
    Δ'' = proj₁ IH₂
    Δ'⊆Δ'' = proj₁ (proj₂ IH₂)
    Δ⊢ts₂++ts₁∈Δ'' = proj₁ (proj₂ (proj₂ IH₂))
    Δ''++Δ⊩x = proj₂ (proj₂ (proj₂ IH₂))
    fresh≤fresh'' = ≤-trans fresh≤fresh' (evalms-fresh-grows e₂⇓[ts₂,x])

    cont : Δ' ++ᵥ Δ ⊩ (Closure env' body) →
      Σ[ Δ'' ∈ Ctx Base (fresh'' ∸ fresh) ]
        (Δ ⊢ts (ts₃ ++ₗ ts₂ ++ₗ ts₁) ∈ Δ'' × Δ'' ++ᵥ Δ ⊩ v)
    cont (admit-=> body env'⋖Δ'++Δ) =
      let Δout , _ , ts-typed , v-typed = IH₃
       in Δout , ts-typed , v-typed
      where
        IH₃ = evalms-chain
                Δ fresh≤fresh'' Δ⊢ts₂++ts₁∈Δ''
                (cons-valid
                  Δ''++Δ⊩x
                  (extend-⋖ env'⋖Δ'++Δ (xs⊆ys⇒xs++zs⊆ys++zs Δ'⊆Δ'')))
                body⇓[ts₃,v]
evalms-wf Δ env⋖Δ (evalms-let e₁⇓[ts₁,x₁] e₂⇓[ts₂,x₂]) =
  let Δout , _ , ts-typed , v-typed = IH₂
   in Δout , ts-typed , v-typed
  where
    IH₁ = evalms-wf Δ env⋖Δ e₁⇓[ts₁,x₁]
    Δ' = proj₁ IH₁
    Δ⊢ts₁∈Δ' = proj₁ (proj₂ IH₁)
    Δ'++Δ⊩x₁ = proj₂ (proj₂ IH₁)
    fresh≤fresh' = evalms-fresh-grows e₁⇓[ts₁,x₁]

    IH₂ = evalms-chain Δ fresh≤fresh'
            Δ⊢ts₁∈Δ' (cons-valid Δ'++Δ⊩x₁ (extend-⋖ env⋖Δ (++-⊆ _ Δ')))
            e₂⇓[ts₂,x₂]
evalms-wf Δ env⋖Δ (evalms-+ refl e₁⇓[ts₁,x₁] e₂⇓[ts₂,x₂]) =
  let Δout , _ , ts-typed , _ = IH₂
   in Δout , ts-typed , admit-N _ _
  where
    IH₁ = evalms-wf Δ env⋖Δ e₁⇓[ts₁,x₁]
    Δ' = proj₁ IH₁
    Δ⊢ts₁∈Δ' = proj₁ (proj₂ IH₁)
    Δ'++Δ⊩x₁ = proj₂ (proj₂ IH₁)
    fresh≤fresh' = evalms-fresh-grows e₁⇓[ts₁,x₁]

    IH₂ = evalms-chain Δ fresh≤fresh'
            Δ⊢ts₁∈Δ' (extend-⋖ env⋖Δ (++-⊆ _ Δ'))
            e₂⇓[ts₂,x₂]
evalms-wf Δ env⋖Δ (evalms-CC e⇓[ts,x]) =
  let Δ' , Δ⊢ts∈Δ' , _ = evalms-wf Δ env⋖Δ e⇓[ts,x]
   in Δ' , Δ⊢ts∈Δ' , admit-Code (anf-c _)
evalms-wf Δ env⋖Δ
  (evalms-++
    {fresh = fresh} {ts₁ = ts₁} {ts₂ = ts₂}
    {fresh'' = fresh''} {a₁ = a₁} {a₂ = a₂}
    e₁⇓[ts₁,a₁] e₂⇓[ts₂,a₂]) = Δout , Δ⊢a₁+a₂∷ts₂++ts₁∈Δout , Δout++Δ⊩fresh''
  where
    IH₁ = evalms-wf Δ env⋖Δ e₁⇓[ts₁,a₁]
    Δ' = proj₁ IH₁
    Δ⊢ts₁∈Δ' = proj₁ (proj₂ IH₁)
    Δ'++Δ⊩a₁ = proj₂ (proj₂ IH₁)
    fresh≤fresh' = evalms-fresh-grows e₁⇓[ts₁,a₁]

    IH₂ = evalms-chain Δ fresh≤fresh'
            Δ⊢ts₁∈Δ' (extend-⋖ env⋖Δ (++-⊆ _ Δ'))
            e₂⇓[ts₂,a₂]
    Δ'' = proj₁ IH₂
    Δ'⊆Δ'' = proj₁ (proj₂ IH₂)
    Δ⊢ts₂++ts₁∈Δ'' = proj₁ (proj₂ (proj₂ IH₂))
    Δ''++Δ⊩a₂ = proj₂ (proj₂ (proj₂ IH₂))

    Δ''++Δ⊩a₁ = extend-⊩ Δ'++Δ⊩a₁ (xs⊆ys⇒xs++zs⊆ys++zs Δ'⊆Δ'')

    fresh≤fresh'' = ≤-trans fresh≤fresh' (evalms-fresh-grows e₂⇓[ts₂,a₂])

    unwrap : ∀{a} → Δ'' ++ᵥ Δ ⊩ Code N a → Δ'' ++ᵥ Δ ⊢v a ∈ N
    unwrap (admit-Code Δ⊢a∈N) = Δ⊢a∈N

    Δ''++Δ⊢a₁+a₂∈N = anf-+ (unwrap Δ''++Δ⊩a₁) (unwrap Δ''++Δ⊩a₂)
    Δ⊢a₁+a₂∷ts₂++ts₁∈N∷Δ'' = anf-cons refl Δ⊢ts₂++ts₁∈Δ'' Δ''++Δ⊢a₁+a₂∈N

    Δall,Δ''++Δ≅Δall = Vec.launder (Δ'' ++ᵥ Δ) (m∸n+n≡m fresh≤fresh'')

    Δall = proj₁ Δall,Δ''++Δ≅Δall
    Δ''++Δ≅Δall = proj₂ Δall,Δ''++Δ≅Δall

    N∷Δall[fresh'']=N : (N ∷ Δall)[ fresh'' ]= N
    N∷Δall[fresh'']=N = chere

    Δout,N∷Δ''≅Δout = Vec.launder (N ∷ᵥ Δ'') (1+[a∸b]≡[1+a]∸b fresh≤fresh'')

    Δout : Ctx Base (suc fresh'' ∸ fresh)
    Δout = proj₁ Δout,N∷Δ''≅Δout
    N∷Δ''≅Δout = proj₂ Δout,N∷Δ''≅Δout

    Δ⊢a₁+a₂∷ts₂++ts₁∈Δout : Δ ⊢ts a₁ +ₐ a₂ ∷ₗ ts₂ ++ₗ ts₁ ∈ Δout
    Δ⊢a₁+a₂∷ts₂++ts₁∈Δout =
      ≅-subst (Δ ⊢ts a₁ +ₐ a₂ ∷ₗ ts₂ ++ₗ ts₁ ∈_)
        N∷Δ''≅Δout
        Δ⊢a₁+a₂∷ts₂++ts₁∈N∷Δ''

    N∷Δall≅Δout++Δ : N ∷ Δall ≅ Δout ++ᵥ Δ
    N∷Δall≅Δout++Δ = begin
      N ∷ Δall ≅⟨ ≅-cong (N ∷_) (≅-symmetric Δ''++Δ≅Δall) ⟩
      N ∷ Δ'' ++ᵥ Δ ≅⟨⟩
      (N ∷ Δ'') ++ᵥ Δ ≅⟨ ≅-cong (_++ᵥ Δ) N∷Δ''≅Δout ⟩
      Δout ++ᵥ Δ ∎
      where
        open ≅-Reasoning

    Δout++Δ[fresh'']=N : (Δout ++ᵥ Δ)[ fresh'' ]= N
    Δout++Δ[fresh'']=N = ≅-subst (_[ fresh'' ]= N) N∷Δall≅Δout++Δ N∷Δall[fresh'']=N

    Δout++Δ⊩fresh'' : Δout ++ᵥ Δ ⊩ Code N (Vₐ fresh'')
    Δout++Δ⊩fresh'' = admit-Code (anf-v Δout++Δ[fresh'']=N)

-- This lemma is effectively "cite the IH and then weaken". The reason it's so
-- complicated is because we need to do a lot of vector length munging. We can't
-- use regular rewrites because values like `(i' ∸ i) + i` are not syntactically
-- equal to `i'' ∸ i`, which prevents us from even uttering something like
-- `evalms-wf (Δ' ++ᵥ Δ) _ e₂⇓[ts₂,x₂]`.
evalms-chain {fresh = fresh} {fresh' = fresh'} {ts₁} {ts₂}
    {fresh'' = fresh''} {env = env} {v = v}
    Δ {Δ' = Δ'} fresh≤fresh' Δ⊢ts₁∈Δ' env⋖Δ'++Δ e⇓[ts₂,v] =
  Δout , Δ'⊆Δout , proof , Δout++Δ⊩v
  where
    Δs,Δ'++Δ≅Δs = Vec.launder (Δ' ++ᵥ Δ) (m∸n+n≡m fresh≤fresh')

    Δs : Ctx Base fresh'
    Δs = proj₁ Δs,Δ'++Δ≅Δs
    Δ'++Δ≅Δs = proj₂ Δs,Δ'++Δ≅Δs

    env⋖Δs = ≅-subst (env ⋖_) Δ'++Δ≅Δs env⋖Δ'++Δ

    IH = evalms-wf Δs env⋖Δs e⇓[ts₂,v]
    fresh'≤fresh'' = evalms-fresh-grows e⇓[ts₂,v]
    Δ'' = proj₁ IH
    Δs⊢ts₂∈Δ'' = proj₁ (proj₂ IH)
    Δ''++Δs⊩v = proj₂ (proj₂ IH)

    Δout,Δ''++Δ'≅Δout =
      Vec.launder (Δ'' ++ᵥ Δ') (a∸b+b∸c≡a∸c fresh'≤fresh'' fresh≤fresh')

    Δout = proj₁ Δout,Δ''++Δ'≅Δout
    Δ''++Δ'≅Δout = proj₂ Δout,Δ''++Δ'≅Δout
    Δ'++Δ⊢ts₂∈Δ'' = block-launder-ctx (≅-symmetric Δ'++Δ≅Δs) Δs⊢ts₂∈Δ''
    Δ⊢ts₂++ts₂∈Δ''++Δ' = block-typ-join Δ⊢ts₁∈Δ' Δ'++Δ⊢ts₂∈Δ''

    Δ'⊆Δout : Δ' ⊆ Δout
    Δ'⊆Δout = ≅-subst (Δ' ⊆_) Δ''++Δ'≅Δout (++-⊆ Δ' Δ'')

    proof : Δ ⊢ts ts₂ ++ₗ ts₁ ∈ Δout
    proof = block-launder-out Δ''++Δ'≅Δout Δ⊢ts₂++ts₂∈Δ''++Δ'

    Δ''++Δs≅Δout++Δ : Δ'' ++ᵥ Δs ≅ Δout ++ᵥ Δ
    Δ''++Δs≅Δout++Δ = begin
      Δ'' ++ᵥ Δs ≅⟨ ≅-cong (Δ'' ++ᵥ_) (≅-symmetric Δ'++Δ≅Δs) ⟩
      Δ'' ++ᵥ (Δ' ++ᵥ Δ) ≅⟨ ≅-symmetric (≅-++-assoc Δ'' Δ' Δ) ⟩
      (Δ'' ++ᵥ Δ') ++ᵥ Δ ≅⟨ ≅-cong (_++ᵥ Δ) Δ''++Δ'≅Δout ⟩
      Δout ++ᵥ Δ ∎
      where
        open ≅-Reasoning

    Δout++Δ⊩v : Δout ++ᵥ Δ ⊩ v
    Δout++Δ⊩v = ≅-subst (_⊩ v) Δ''++Δs≅Δout++Δ Δ''++Δs⊩v
