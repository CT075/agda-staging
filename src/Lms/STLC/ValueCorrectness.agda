module Lms.STLC.ValueCorrectness where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties as Nat
open import Data.Vec as Vec using (Vec; []; _∷_) renaming (_++_ to _⧺_)
open import Data.Product as Prod
open import Data.Unit as Unit using (⊤; tt)
open import Data.Empty as Void
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary.Decidable using (yes; no)

open import Data.Product.Extensions
open import Data.Vec.Extensions
open import Data.Context as Context hiding (Ctx)
open import Data.Store as Store using (nil; cons; store-lookup-syntax)

open import Lms.STLC.Core
open import Lms.STLC.IR as Anf hiding (Val; Env)
open import Lms.STLC.Specialization
open import Lms.STLC.Evaluation

private variable
  w : W
  n n' n₁ n₂ m offs i : ℕ

data _≈_ : ∀{τ} → Val Base τ → Anf.Val → Set where

infix 4 _⊢v_~_ _⊢e⟨_,_⟩~⟨_,_⟩ _⊨_~_
_⊢v_~_ : ∀{τ τ'} →
  Anf.Env offs → Val Staged τ → Val Base τ' → Set
_⊢e⟨_,_⟩~⟨_,_⟩ : ∀{Γ : Ctx Staged n} {τ} {Γ' : Ctx Base n'} {τ'} →
  Anf.Env offs → Env Γ → Tm _ τ Γ → Env Γ' → Tm _ τ' Γ' → Set
_⊨_~_ : ∀{Γ : Ctx Staged n} {Γ' : Ctx Base n} →
  Anf.Env offs → Env Γ → Env Γ' → Set

env ⊢v Const x ~ Const x' = x ≡ x'
env ⊢v Const _ ~ Closure _ _ = ⊥
env ⊢v Closure _ _ ~ Const _ = ⊥
_ ⊢v Closure {n = 0} {τ₁ = τ} envₛ e ~ Closure {n = 0} {τ₁ = τ'} envₛ' e' =
    ∀ {offs} (env : Anf.Env offs) →
    ( ⊤
    × ∀ {x : Val _ τ} {x' : Val _ τ'} →
      env ⊢v x ~ x' → env ⊢e⟨ cons x envₛ , e ⟩~⟨ cons x' envₛ' , e' ⟩)
_ ⊢v Closure {n = suc _} _ _ ~ Closure {n = 0} _ _ = ⊥
_ ⊢v Closure {n = 0} _ _ ~ Closure {n = suc _} _ _ = ⊥
_⊢v_~_ {τ = τ₁ => _} {τ' = τ₁' => _} _
  (Closure {n = suc n₁} envₛ@(cons v tenvₛ) e)
  (Closure {n = suc n₂} envₛ'@(cons v' tenvₛ') e')
  with n₁ ≟ n₂
... | no _ = ⊥
... | yes refl =
    ∀ {offs} (env : Anf.Env offs) →
    ( env ⊢v v ~ v' × env ⊨ tenvₛ ~ tenvₛ'
    × ∀ {x : Val _ τ₁} {x' : Val _ τ₁'} →
      env ⊢v x ~ x' → env ⊢e⟨ cons x envₛ , e ⟩~⟨ cons x' envₛ' , e' ⟩)
env ⊢v Code τ p ~ v' = ∃[ v ] (env ⊢v p ⇓ v × v' ≈ v)

_⊢e⟨_,_⟩~⟨_,_⟩ {offs} envₜ envₛ e envₛ' e' =
  ∃[ v ](∃[ v' ](∃ᵥ[ ts ](
    envₛ , offs ⊢ e ⇓[ ts , v ] ×
    envₛ' ⊢ e' ⇓ v' ×
    Σ[ vs ∈ Anf.Env _ ](envₜ ⊢ts ts ⇓ vs × (vs ⧺ envₜ) ⊢v v ~ v'))))

envₜ ⊨ nil ~ nil = ⊤
envₜ ⊨ cons v envₛ ~ cons v' env =
  envₜ ⊢v v ~ v' × envₜ ⊨ envₛ ~ env

{-
data _⊨_~_ where
  ~-nil : ∀{envₜ : Anf.Env offs} → envₜ ⊨ nil ~ nil
  ~-cons :
    ∀ {Γ : Ctx Staged n} {Γ' : Ctx Base n}
      {envₜ : Anf.Env offs} {envₛ : Env Γ} {env : Env Γ'}
      {τ τ'} {v : Val _ τ} {v' : Val _ τ'} →
    envₜ ⊢v v ~ v' →
    envₜ ⊨ envₛ ~ env →
    envₜ ⊨ cons v envₛ ~ cons v' env

wk-⊨ : ∀{Γ : Ctx Staged n} {Γ' : Ctx Base n}
  {envₜ : Anf.Env offs} {envₛ : Env Γ} {env : Env Γ'} x →
  envₜ ⊨ envₛ ~ env →
  x ∷ envₜ ⊨ envₛ ~ env
wk-⊨ x ~-nil = ~-nil
wk-⊨ x (~-cons v~v' envₛ~env) = ~-cons {! v~v' !} (wk-⊨ x envₛ~env)
    -}

~-lookup :
  ∀ {Γ : Ctx Base n} {Γₛ : Ctx Staged n} {τ τ'}
    {envₜ : Anf.Env offs} {env : Env Γ} {envₛ : Env Γₛ} →
  envₜ ⊨ envₛ ~ env →
  Γₛ [ i ]= τ →
  Γ [ i ]= τ' →
  ∃[ v ](∃[ v' ](envₛ [ i ]↦ v ∈ τ × env [ i ]↦ v' ∈ τ' × envₜ ⊢v v ~ v'))
{-
~-lookup
    {env = cons v' _} {envₛ = cons v _}
    (~-cons v~v' ⊨env) here here =
  v , v' , Store.here , Store.here , v~v'
~-lookup (~-cons x ⊨env) here (there Γₛ[i]=τ') =
  ⊥-elim (<-irrefl refl ([]=→< Γₛ[i]=τ'))
~-lookup (~-cons x ⊨env) (there Γ[i]=τ) here =
  ⊥-elim (<-irrefl refl ([]=→< Γ[i]=τ))
~-lookup (~-cons x ⊨env) (there Γ[i]=τ) (there Γₛ[i]=τ') =
  let v , v' , p , p' , v~v' = ~-lookup ⊨env Γ[i]=τ Γₛ[i]=τ'
   in v , v' , Store.there p , Store.there p' , v~v'
-}

ctx-env-lookup : ∀{Γ : Ctx w n} {τ} →
  (env : Env Γ) → Γ [ i ]= τ → Σ[ v ∈ _ ](env [ i ]↦ v ∈ τ)
ctx-env-lookup (cons x _) here = x , Store.here
ctx-env-lookup (cons _ env) (there Γ[i]=τ) =
  let x , p = ctx-env-lookup env Γ[i]=τ
   in x , Store.there p

valueCorrectness :
  ∀ {Γ : Ctx Staged n} {τ} {e : Tm _ τ Γ} {envₛ : Env Γ}
    {Γ' : Ctx Base n} {τ'} {e' : Tm _ τ' Γ'} {env : Env Γ'}
    {envₜ : Anf.Env offs} →
  envₜ ⊨ envₛ ~ env → e ≤ e' →
  envₜ ⊢e⟨ envₛ , e ⟩~⟨ env , e' ⟩
valueCorrectness ⊨env (≤-C x) = {!!}
{-
  Const x , Const x , [] ,ᵥ evalms-C x , eval-C x , [] , eval-nil , refl
valueCorrectness ⊨env (≤-V i Γₛ[i]=τ Γ[i]=τ' _) =
  let v , v' , envₛ[i]↦v , env[i]↦v' , v~v' =
        ~-lookup ⊨env Γₛ[i]=τ Γ[i]=τ'
   in ( v
      , v'
      , []
      ,ᵥ evalms-V envₛ[i]↦v
      , eval-V env[i]↦v'
      , []
      , eval-nil
      , v~v')
valueCorrectness {envₛ = envₛ} {env = env}
    ⊨env (≤-λ {eₛ = e} {eₜ = e'} _ e≤e') =
  ( Closure envₛ e
  , Closure env e'
  , []
  ,ᵥ  evalms-λ envₛ e
  , eval-λ env e'
  , []
  , eval-nil
  , {! λ x~x' → valueCorrectness (~-cons x~x' {!!}) e≤e'!})
valueCorrectness {offs = offs} {envₛ = envₛ} {env = env} {envₜ = envₜ} ⊨env
  (≤-$ {τ₁ = τ₁} {τ₂ = τ₂} {τ₁' = τ₁'} {τ₂' = τ₂'}
    e₁≤e₁' e₂≤e₂') =
  let
    f , f' , ts₁ ,ᵥ e₁⇓f , e₁'⇓f' , vs₁ , ts₁⇓vs₁ , f~f' =
      valueCorrectness ⊨env e₁≤e₁'
    {-
    x , x' , ts₂ ,ᵥ e₂⇓x , e₂'⇓x' , vs₂ , ts₂⇓vs₂ , x~x' =
      {! valueCorrectness {envₜ = vs₁ ⧺ envₜ} ⊨env e₂≤e₂' !}
      -}
  in
    {! f~f' x~x' !}
    {-
  where
    cont :
      ∀ {f : Val Staged (τ₁ => τ₂)} {f' : Val Base (τ₁' => τ₂')}
        {vs₁ : Anf.Env n} →
      vs₁ ⧺ envₜ ⊢v f ~ f' →
      {!!}
    cont = {!!}
    -}
valueCorrectness ⊨env (≤-let e≤e' e≤e'') = {! !}
valueCorrectness ⊨env (≤-+ e≤e' e≤e'') = {! !}
valueCorrectness ⊨env (≤-CC e≤e') = {! !}
valueCorrectness ⊨env ≤-λλ = {! !}
valueCorrectness ⊨env (≤-++ e≤e' e≤e'') = {! !}
valueCorrectness ⊨env (≤-$$ e≤e' e≤e'') = {! !}
-}
