module Lms.STLC.ValueCorrectness where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality using (refl)

open import Data.Product.Extensions
open import Data.Context using (_[_]=_; here; there)
open import Data.Store as Store using (nil; cons; store-lookup-syntax)

open import Lms.STLC.Core
open import Lms.STLC.IR as Anf hiding (Val; Env)
open import Lms.STLC.Evaluation

private variable
  n : ℕ
  offs : ℕ

forgetTyp : Typ Staged → Typ Base
forgetTyp N = N
forgetTyp (τ₁ => τ₂) = forgetTyp τ₁ => forgetTyp τ₂
forgetTyp (Rep τ) = τ

forgetCtx : Ctx Staged n → Ctx Base n
forgetCtx = Vec.map forgetTyp

forget-lookup : ∀{Γ : Ctx Staged n} {i τ} →
  Γ [ i ]= τ → (forgetCtx Γ)[ i ]= (forgetTyp τ)
forget-lookup here = here
forget-lookup (there Γ[i]=τ) = there (forget-lookup Γ[i]=τ)

forget :
  ∀ {Γ : Ctx Staged n} {τ} →
  Tm Staged τ Γ → Tm Base (forgetTyp τ) (forgetCtx Γ)
forget (C x) = C x
forget (V i Γ[i]=τ) = V i (forget-lookup Γ[i]=τ)
forget (λ' τ e) = λ' (forgetTyp τ) (forget e)
forget (e₁ $ e₂) = forget e₁ $ forget e₂
forget (Let e₁ e₂) = Let (forget e₁) (forget e₂)
forget (e₁ +' e₂) = forget e₁ +' forget e₂
forget (CC e) = forget e
forget (λλ τ e) = forget e
forget (e₁ ++ e₂) = forget e₁ +' forget e₂
forget (e₁ $$ e₂) = forget e₁ $ forget e₂

liftCtx : Ctx Base n → Ctx Staged n
liftCtx = Vec.map Rep

lift-lookup : ∀{Γ : Ctx Base n} {i τ} →
  Γ [ i ]= τ → (liftCtx Γ)[ i ]= Rep τ
lift-lookup here = here
lift-lookup (there Γ[i]=τ) = there (lift-lookup Γ[i]=τ)

lift : ∀{Γ : Ctx Base n} {τ} → Tm Base τ Γ → Tm Staged (Rep τ) (liftCtx Γ)
lift (C x) = CC (C x)
lift (V i Γ[i]=τ) = V i (lift-lookup Γ[i]=τ)
lift (λ' τ e) = λλ τ (λ' (Rep τ) (lift e))
lift (e₁ $ e₂) = lift e₁ $$ lift e₂
lift (Let e₁ e₂) = Let (lift e₁) (lift e₂)
lift (e₁ +' e₂) = lift e₁ ++ lift e₂

data _≈_ : ∀{τ} → Val Base τ → Anf.Val → Set where
  ≈-Const : ∀ x → Const x ≈ Constₐ x

data _~[_,_] : ∀{Γ : Ctx Base n} →
    Env Γ →
    Env (liftCtx Γ) → Anf.Env offs → Set
  where
  ~-nil : nil ~[ nil , [] ]
  ~-cons-C : ∀{Γ : Ctx Base n} {env : Env Γ} {envₛ} {envₜ : Anf.Env offs} x →
    env ~[ envₛ , envₜ ] →
    cons (Const x) env ~[ cons (Code N (Cₐ x)) envₛ , envₜ ]
  ~-cons-V :
    ∀ {Γ : Ctx Base n} {env : Env Γ} {envₛ i τ}
      {v : Val Base τ} {envₜ : Anf.Env offs} {v'} →
    envₜ [ i ]↦ v' → v ≈ v' → env ~[ envₛ , envₜ ] →
    cons v env ~[ cons (Code τ (Vₐ i)) envₛ , envₜ ]

module LookupMetaM where
  record T {Γ : Ctx Staged n}
      (envₛ : Env Γ) (envₜ : Anf.Env offs) τ i (v : Val Base τ) : Set
    where
    constructor LM
    field
      leaf : Anf.Atom
      lookup-proof : envₛ [ i ]↦ Code τ leaf ∈ Rep τ
      result : Anf.Val
      leaf-evals : envₜ ⊢v leaf ⇓ result
      v≈result : v ≈ result

  wkₛ :
    ∀ {Γ : Ctx Staged n} {envₛ : Env Γ} {envₜ : Anf.Env offs}
      {τ i} {v : Val Base τ} {τ'} {x : Val Staged τ'} →
    T envₛ envₜ τ i v →
    T (cons x envₛ) envₜ τ i v
  wkₛ (LM a proof b c d) = LM a (Store.there proof) b c d

open LookupMetaM using (LM) renaming (T to LookupMeta) public

~-lookup : ∀{Γ : Ctx Base n} {env : Env Γ} {envₛ} {envₜ : Anf.Env offs} {i τ v} →
  env ~[ envₛ , envₜ ] → env [ i ]↦ v ∈ τ →
  LookupMeta envₛ envₜ τ i v
~-lookup (~-cons-C x _) Store.here =
  LM _ Store.here _ (Anf.eval-c x) (≈-Const x)
~-lookup (~-cons-C _ env~[envₛ,envₜ]) (Store.there env[i]↦p∈τ) =
  LookupMetaM.wkₛ (~-lookup env~[envₛ,envₜ] env[i]↦p∈τ)
~-lookup (~-cons-V {v' = v'} envₜ[i]↦v' v≈v' _) Store.here =
  LM _ Store.here v' (Anf.eval-v envₜ[i]↦v') v≈v'
~-lookup (~-cons-V _ _ env~[envₛ,envₜ]) (Store.there env[i]↦p∈τ) =
  LookupMetaM.wkₛ (~-lookup env~[envₛ,envₜ] env[i]↦p∈τ)

module LiftEquivM where
  record T
      {Γ : Ctx Base n} (envₛ : Env (liftCtx Γ)) (envₜ : Anf.Env offs)
      {τ} (e : Tm Base τ Γ) (v : Val Base τ) : Set
    where
    constructor LE
    field
      anf-e : Anf.Prog
      evalₛ : envₛ , offs ⊢r lift e ⇓ anf-e
      result : Anf.Val
      evalₜ : envₜ ⊢p anf-e ⇓ result
      v≈result : v ≈ result

open LiftEquivM using (LE) renaming (T to LiftEquiv) public

lift-eval :
  ∀ {Γ : Ctx Base n} {env : Env Γ}
    {envₛ : Env (liftCtx Γ)} {envₜ : Anf.Env offs}
    {τ} {e : Tm Base τ Γ} {v} →
  env ~[ envₛ , envₜ ] → env ⊢ e ⇓ v →
  LiftEquiv envₛ envₜ e v
lift-eval env~[envₛ,envₜ] (eval-C x) = LE
  [ [] , Cₐ x ]
  (evalms-CC (evalms-C x))
  (Constₐ x)
  ([] , Anf.eval-nil , Anf.eval-c x)
  (≈-Const x)
lift-eval env~[envₛ,envₜ] (eval-V env[i]↦v∈τ) =
  let
    LM leaf envₛ[i]↦leaf result envₜ⊢leaf⇓result v≈result =
      ~-lookup env~[envₛ,envₜ] env[i]↦v∈τ
  in LE
    [ [] , leaf ]
    (evalms-V envₛ[i]↦leaf)
    result
    ([] , Anf.eval-nil , envₜ⊢leaf⇓result)
    v≈result
lift-eval {offs = offs} env~[envₛ,envₜ] (eval-λ env e) = LE
  [ {!!} ∷ [] , Vₐ offs ]
  {!!}
  {!!}
  {!!}
  {!!}
lift-eval env~[envₛ,envₜ] (eval-$ e⇓ e₁⇓ e₂⇓) = {! !}
lift-eval env~[envₛ,envₜ] (eval-let e₁⇓ e₂⇓) = {! !}
lift-eval env~[envₛ,envₜ] (eval-+ refl e₁⇓ e₂⇓) = {!!}

{-
lift-correct : ∀ {Γ : Ctx Base n} {env : Env Γ} {τ} {e : Tm Base τ Γ} →
  env ⊢ e ⇓ v → {!!}
  -}

{-
valueCorrectness :
  ∀ {τ e ts a va vb} →
  ∅ ⊢⟨ e , zero ⟩⇓⟨[ ts , Code τ a ], fresh ⟩ →
  ∃[ va , vb ](⊢p⟨ ts , a ⟩⇓ va × ∅ ⊢ forget e ⇓ vb × va ≈ vb)
-}
