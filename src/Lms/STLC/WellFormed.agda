module Lms.STLC.WellFormed where

-- Metatheory and miscellaneous properties of λLMS, establishing that generated
-- code is well-scoped and well-typed.
--
-- The key theorems are the various `evalms-_-typed` terms, which establish that
-- the IR produced by evaluating a staged λLMS term is well-typed.

open import Data.Nat as Nat
open import Data.Nat.Properties as Nat
open import Data.Product as Prod
open import Data.Vec as Vec renaming (_++_ to _⧺_) hiding (_[_]=_)
open import Data.Vec.Properties as Vec
open import Relation.Binary.PropositionalEquality

open import Data.Context as Context hiding (Ctx; here; there)
open import Data.Store as Store

open import Data.Nat.Extensions
open import Data.Vec.Extensions as Vec
open import Data.Product.Extensions as Prod

open import Lms.STLC.Core
open import Lms.STLC.IR as Anf hiding (Val; Env)
open import Lms.STLC.Evaluation

private variable
  T : Set
  w : W
  n n' n'' n₁ n₂ m m' : ℕ
  offs : ℕ

vl-typ-wk : ∀{Δ : Ctx Base n} {v τ} τ' → Δ ⊢v v ∈ τ → τ' ∷ Δ ⊢v v ∈ τ
vl-typ-wk τ (anf-c x) = anf-c x
vl-typ-wk τ (anf-v pf) = anf-v (Context.there pf)

vl-typ-extend : ∀{Δ : Ctx Base n} {Δs : Ctx Base n'} {v τ} →
  Δ ⊆ Δs → Δ ⊢v v ∈ τ →
  Δs ⊢v v ∈ τ
vl-typ-extend (⊆-refl Δ) Δ⊢v∈τ = Δ⊢v∈τ
vl-typ-extend (⊆-cons τ' Δ⊆Δ') Δ⊢v∈τ = vl-typ-wk τ' (vl-typ-extend Δ⊆Δ' Δ⊢v∈τ)

block-typ-join :
  ∀ {Δ : Ctx Base n} {Δ' : Ctx Base n₁} {Δ'' : Ctx Base n₂} →
    {ts₁ : Vec _ n₁} {ts₂ : Vec _ n₂} →
  Δ ⊢ts ts₁ ∈ Δ' → Δ' ⧺ Δ ⊢ts ts₂ ∈ Δ'' →
  Δ ⊢ts ts₂ ⧺ ts₁ ∈ Δ'' ⧺ Δ'
block-typ-join Δ⊢ts₁∈Δ' anf-nil = Δ⊢ts₁∈Δ'
block-typ-join {Δ = Δ} {Δ' = Δ'} {Δ'' = τ ∷ Δ''}
    Δ⊢ts₁∈Δ' (anf-cons {Γs = Δs} {x = x} refl Δ'⊢xs∈Δ'' Δs⊢x∈τ) =
  anf-cons {Γs = (Δ'' ⧺ Δ') ⧺ Δ}
    refl
    (block-typ-join Δ⊢ts₁∈Δ' Δ'⊢xs∈Δ'')
    [Δ''⧺Δ']⧺Δ⊢x∈τ
  where
    [Δ''⧺Δ']⧺Δ⊢x∈τ : (Δ'' ⧺ Δ') ⧺ Δ ⊢t x ∈ τ
    [Δ''⧺Δ']⧺Δ⊢x∈τ =
      ≅-subst (_⊢t x ∈ τ) (≅-symmetric (≅-++-assoc Δ'' Δ' Δ)) Δs⊢x∈τ

infix 4 _⊩_ _⋖_
data _⊩_ : ∀ {τ : Typ Staged} → Ctx Base n → Val Staged τ → Set
data _⋖_ : ∀ {Γ : Ctx Staged n} → (env : Env Γ) → (Δ : Ctx Base m) → Set

data _⊩_ where
  -- Constants don't interact with Δ at all
  admit-N : ∀(Δ : Ctx Base n) v → Δ ⊩ Const v
  -- Every closed-over value must be valid against Δ
  admit-=> :
    ∀ {Δ : Ctx Base n} {τ τ'}
      {Γ : Ctx Staged m} {env : Env Γ} (body : Tm _ τ' (τ ∷ Γ)) →
    env ⋖ Δ →
    Δ ⊩ Closure env body
  -- Code snippets should be well-typed against Δ
  admit-Code : ∀{Δ : Ctx Base n} {v τ} → Δ ⊢v v ∈ τ → Δ ⊩ Code τ v

un⊩-=> :
  ∀ {Δ : Ctx Base n} {τ τ'}
    {Γ : Ctx Staged m} {env : Env Γ} {body : Tm _ τ' (τ ∷ Γ)} →
  Δ ⊩ Closure env body →
  env ⋖ Δ
un⊩-=> (admit-=> _ env⋖Δ) = env⋖Δ

un⊩-Code : ∀{Δ : Ctx Base n} {v τ} → Δ ⊩ Code τ v → Δ ⊢v v ∈ τ
un⊩-Code (admit-Code Δ⊢v∈τ) = Δ⊢v∈τ

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

evalms-wf : ∀{Γ : Ctx _ n} {env : Env Γ} {τ e} {v : Val _ τ} {ts : Vec _ m} →
  (Δ : Ctx Base offs) →
  env ⋖ Δ →
  env , offs ⊢ e ⇓[ ts , v ] →
  Σ[ Δ' ∈ Ctx Base m ](Δ ⊢ts ts ∈ Δ' × Δ' ⧺ Δ ⊩ v)
evalms-wf Δ env⋖Δ (evalms-C x) = [] , anf-nil , admit-N _ _
evalms-wf Δ env⋖Δ (evalms-V env[i]=v) =
  [] , anf-nil , ⋖-lookup env⋖Δ env[i]=v
evalms-wf Δ env⋖Δ (evalms-λ _ _) =
  [] , anf-nil , admit-=> _ env⋖Δ
evalms-wf Δ env⋖Δ
  (evalms-$
    {ts₃ = ts₃} {env' = env'} {v = v}
    refl refl e₁⇓[ts₁,f] e₂⇓[ts₂,x] body⇓[ts₃,v]) =
  let
    Δ' , Δ⊢ts₁∈Δ' , Δ'⧺Δ⊩f = evalms-wf Δ env⋖Δ e₁⇓[ts₁,f]
    env⋖Δ'⧺Δ = extend-⋖ env⋖Δ (++-⊆ _ _)
    Δ'' , Δ'⧺Δ⊢ts₂∈Δ'' , Δ''⧺Δ'⧺Δ⊩x = evalms-wf (Δ' ⧺ Δ) env⋖Δ'⧺Δ e₂⇓[ts₂,x]
    env'⋖Δ'⧺Δ = un⊩-=> Δ'⧺Δ⊩f
    env'⋖Δ''⧺Δ'⧺Δ = extend-⋖ env'⋖Δ'⧺Δ (++-⊆ _ Δ'')
    Δ''' , Δ''⧺Δ'⧺Δ⊢ts₃∈Δ''' , Δ'''⧺Δ''⧺Δ'⧺Δ⊩v =
      evalms-wf
        (Δ'' ⧺ Δ' ⧺ Δ)
        (cons-valid Δ''⧺Δ'⧺Δ⊩x env'⋖Δ''⧺Δ'⧺Δ)
        body⇓[ts₃,v]
    Δ⊢ts₂⧺ts₁∈Δ''⧺Δ' = block-typ-join Δ⊢ts₁∈Δ' Δ'⧺Δ⊢ts₂∈Δ''
    [Δ''⧺Δ']⧺Δ⊢ts₃∈Δ''' =
      ≅-subst (_⊢ts ts₃ ∈ Δ''') (≅-symmetric (≅-++-assoc Δ'' Δ' Δ))
        Δ''⧺Δ'⧺Δ⊢ts₃∈Δ'''
    Δ⊢ts₃⧺ts₂⧺ts₁∈Δ'''⧺Δ''⧺Δ' =
      block-typ-join Δ⊢ts₂⧺ts₁∈Δ''⧺Δ' [Δ''⧺Δ']⧺Δ⊢ts₃∈Δ'''
    [Δ'''⧺Δ''⧺Δ']⧺Δ⊩v =
      ≅-subst (_⊩ v) (reassoc Δ''' Δ'' Δ' Δ) Δ'''⧺Δ''⧺Δ'⧺Δ⊩v
  in
    Δ''' ⧺ Δ'' ⧺ Δ' , Δ⊢ts₃⧺ts₂⧺ts₁∈Δ'''⧺Δ''⧺Δ' , [Δ'''⧺Δ''⧺Δ']⧺Δ⊩v
  where
    reassoc : ∀ xs ys zs ws → xs ⧺ ys ⧺ zs ⧺ ws ≅ (xs ⧺ ys ⧺ zs) ⧺ ws
    reassoc xs ys zs ws = begin
      xs ⧺ ys ⧺ zs ⧺ ws ≅⟨ ≅-cong (xs ⧺_) (≅-symmetric (≅-++-assoc ys zs ws)) ⟩
      xs ⧺ (ys ⧺ zs) ⧺ ws ≅⟨ ≅-symmetric (≅-++-assoc xs (ys ⧺ zs) ws) ⟩
      (xs ⧺ ys ⧺ zs) ⧺ ws ∎
      where
        open ≅-Reasoning
evalms-wf Δ env⋖Δ (evalms-let {v = x₂} refl e₁⇓[ts₁,x₁] e₂⇓[ts₂,x₂]) =
  let
    Δ' , Δ⊢ts₁∈Δ' , Δ'⧺Δ⊩x₁ = evalms-wf Δ env⋖Δ e₁⇓[ts₁,x₁]
    x₁∷env⋖Δ'⧺Δ = cons-valid Δ'⧺Δ⊩x₁ (extend-⋖ env⋖Δ (++-⊆ _ _))
    Δ'' , Δ'⧺Δ⊢ts₂∈Δ'' , Δ''⧺Δ'⧺Δ⊩x₂ =
      evalms-wf (Δ' ⧺ Δ) x₁∷env⋖Δ'⧺Δ e₂⇓[ts₂,x₂]
    [Δ''⧺Δ']⧺Δ⊩x₂ =
      ≅-subst (_⊩ x₂) (≅-symmetric (≅-++-assoc Δ'' Δ' Δ)) Δ''⧺Δ'⧺Δ⊩x₂
  in
    Δ'' ⧺ Δ' , block-typ-join Δ⊢ts₁∈Δ' Δ'⧺Δ⊢ts₂∈Δ'' , [Δ''⧺Δ']⧺Δ⊩x₂
evalms-wf Δ env⋖Δ (evalms-+ refl refl e₁⇓[ts₁,x₁] e₂⇓[ts₂,x₂]) =
  let
    Δ' , Δ⊢ts₁∈Δ' , Δ'⧺Δ⊩x₁ = evalms-wf Δ env⋖Δ e₁⇓[ts₁,x₁]
    Δ'' , Δ'⧺Δ⊢ts₂∈Δ'' , Δ''⧺Δ'⧺Δ⊩x₂ =
      evalms-wf (Δ' ⧺ Δ) (extend-⋖ env⋖Δ (++-⊆ _ _)) e₂⇓[ts₂,x₂]
  in
    Δ'' ⧺ Δ' , block-typ-join Δ⊢ts₁∈Δ' Δ'⧺Δ⊢ts₂∈Δ'' , admit-N _ _
evalms-wf Δ env⋖Δ (evalms-CC e⇓[ts,x]) =
  let Δ' , Δ⊢ts∈Δ' , _ = evalms-wf Δ env⋖Δ e⇓[ts,x]
   in Δ' , Δ⊢ts∈Δ' , admit-Code (anf-c _)
evalms-wf Δ env⋖Δ
  (evalms-λλ
    {env' = env'} {τ = τ} {τ' = τ'} {e' = body}
    refl e⇓[ts,⟨env',e'⟩] e'⇓[tsᵢ,v]) =
  let
    Δ' , Δ⊢ts∈Δ' , Δ'⧺Δ⊩⟨env',e'⟩ = evalms-wf Δ env⋖Δ e⇓[ts,⟨env',e'⟩]
    env'⋖τ∷Δ'⧺Δ = wk-⋖ τ (un⊩-=> Δ'⧺Δ⊩⟨env',e'⟩)
    Δᵢ , τ∷Δ'⧺Δ⊢tsᵢ∈Δᵢ , Δᵢ⧺τ∷Δ'⧺Δ⊩v =
      evalms-wf
        (τ ∷ Δ' ⧺ Δ)
        (cons-valid (admit-Code (anf-v Context.here)) env'⋖τ∷Δ'⧺Δ)
        e'⇓[tsᵢ,v]
  in
    τ => τ' ∷ Δ' ,
    anf-cons refl Δ⊢ts∈Δ' (anf-λ τ refl τ∷Δ'⧺Δ⊢tsᵢ∈Δᵢ (un⊩-Code Δᵢ⧺τ∷Δ'⧺Δ⊩v)) ,
    admit-Code (anf-v Context.here)
evalms-wf Δ env⋖Δ
  (evalms-++
    {m₁ = m₁} {m₂ = m₂} {offs = offs} {a₁ = a₁} {a₂ = a₂}
    refl refl e₁⇓[ts₁,a₁] e₂⇓[ts₂,a₂]) =
  let
    Δ' , Δ⊢ts₁∈Δ' , Δ'⧺Δ⊩a₁ = evalms-wf Δ env⋖Δ e₁⇓[ts₁,a₁]
    Δ'' , Δ'⧺Δ⊢ts₂∈Δ'' , Δ''⧺Δ'⧺Δ⊩a₂ =
      evalms-wf (Δ' ⧺ Δ) (extend-⋖ env⋖Δ (++-⊆ _ _)) e₂⇓[ts₂,a₂]
    Δ⊢ts₂⧺ts₁∈Δ''⧺Δ' = block-typ-join Δ⊢ts₁∈Δ' Δ'⧺Δ⊢ts₂∈Δ''
    Δ''⧺Δ'⧺Δ⊢a₁∈N = vl-typ-extend (++-⊆ _ Δ'') (un⊩-Code Δ'⧺Δ⊩a₁)
    Δ''⧺Δ'⧺Δ⊢a₂∈N = un⊩-Code Δ''⧺Δ'⧺Δ⊩a₂
    Δ''⧺Δ'⧺Δ⊢a₁+a₂∈N = anf-+ Δ''⧺Δ'⧺Δ⊢a₁∈N Δ''⧺Δ'⧺Δ⊢a₂∈N
    [Δ''⧺Δ']⧺Δ⊢a₁+a₂∈N =
      ≅-subst (_⊢t a₁ +ₐ a₂ ∈ N)
        (≅-symmetric (≅-++-assoc Δ'' Δ' Δ)) Δ''⧺Δ'⧺Δ⊢a₁+a₂∈N
    Δ⊢a₁+a₂∷ts₁⧺ts₂⊢N∷Δ''⧺Δ' =
      anf-cons refl Δ⊢ts₂⧺ts₁∈Δ''⧺Δ' [Δ''⧺Δ']⧺Δ⊢a₁+a₂∈N
    N∷Δ''⧺Δ'⧺Δ[i]=N = Context.here {t = N} {Γ = Δ'' ⧺ Δ' ⧺ Δ}
    [N∷Δ''⧺Δ']⧺Δ[i]=N =
      ≅-subst (_[ m₂ + (m₁ + offs) ]= N)
        (≅-symmetric (≅-++-assoc (N ∷ Δ'') Δ' Δ)) N∷Δ''⧺Δ'⧺Δ[i]=N
  in
    N ∷ (Δ'' ⧺ Δ') ,
    Δ⊢a₁+a₂∷ts₁⧺ts₂⊢N∷Δ''⧺Δ' ,
    admit-Code (anf-v [N∷Δ''⧺Δ']⧺Δ[i]=N)
evalms-wf Δ env⋖Δ
  (evalms-$$
    {m₁ = m₁} {m₂ = m₂} {offs = offs} {τ = τ} {τ' = τ'} {a₁ = f} {a₂ = x}
    refl refl e₁⇓[ts₁,f] e₂⇓[ts₂,x]) =
  let
    Δ' , Δ⊢ts₁∈Δ' , Δ'⧺Δ⊩f = evalms-wf Δ env⋖Δ e₁⇓[ts₁,f]
    Δ'' , Δ'⧺Δ⊢ts₂∈Δ'' , Δ''⧺Δ'⧺Δ⊩x =
      evalms-wf (Δ' ⧺ Δ) (extend-⋖ env⋖Δ (++-⊆ _ _)) e₂⇓[ts₂,x]
    Δ⊢ts₂⧺ts₁∈Δ''⧺Δ' = block-typ-join Δ⊢ts₁∈Δ' Δ'⧺Δ⊢ts₂∈Δ''
    Δ''⧺Δ'⧺Δ⊢f∈τ=>τ' = vl-typ-extend (++-⊆ _ Δ'') (un⊩-Code Δ'⧺Δ⊩f)
    Δ''⧺Δ'⧺Δ⊢x∈τ = un⊩-Code Δ''⧺Δ'⧺Δ⊩x
    Δ''⧺Δ'⧺Δ⊢f$x∈τ' = anf-$ Δ''⧺Δ'⧺Δ⊢f∈τ=>τ' Δ''⧺Δ'⧺Δ⊢x∈τ
    [Δ''⧺Δ']⧺Δ⊢f$x∈τ' =
      ≅-subst (_⊢t f $ₐ x ∈ τ')
        (≅-symmetric (≅-++-assoc Δ'' Δ' Δ)) Δ''⧺Δ'⧺Δ⊢f$x∈τ'
    Δ⊢f$x∷ts₁⧺ts₂⊢τ'∷Δ''⧺Δ' =
      anf-cons refl Δ⊢ts₂⧺ts₁∈Δ''⧺Δ' [Δ''⧺Δ']⧺Δ⊢f$x∈τ'
    τ'∷Δ''⧺Δ'⧺Δ[i]=τ' = Context.here {t = τ'} {Γ = Δ'' ⧺ Δ' ⧺ Δ}
    [τ'∷Δ''⧺Δ']⧺Δ[i]=τ' =
      ≅-subst (_[ m₂ + (m₁ + offs) ]=  τ')
        (≅-symmetric (≅-++-assoc (τ' ∷ Δ'') Δ' Δ)) τ'∷Δ''⧺Δ'⧺Δ[i]=τ'
  in
    τ' ∷ (Δ'' ⧺ Δ') ,
    Δ⊢f$x∷ts₁⧺ts₂⊢τ'∷Δ''⧺Δ' ,
    admit-Code (anf-v [τ'∷Δ''⧺Δ']⧺Δ[i]=τ')
