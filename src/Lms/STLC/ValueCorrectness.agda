module Lms.STLC.ValueCorrectness where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties as Nat
open import Data.Vec as Vec using (Vec; []; _∷_) renaming (_++_ to _⧺_)
open import Data.Product as Prod
open import Data.Unit as Unit using (⊤; tt)
open import Data.Empty as Void
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Data.Product.Extensions
open import Data.Vec.Extensions
open import Data.Context as Context hiding (Ctx)
open import Data.Store as Store using (nil; cons; store-lookup-syntax)

open import Lms.STLC.Core
open import Lms.STLC.IR as Anf hiding (Val; Env)
open import Lms.STLC.Specialization
open import Lms.STLC.Evaluation
open import Lms.STLC.Normalization

private variable
  w : W
  n n' n₁ n₂ m m' offs i : ℕ

infix 4 _≈_
_≈_ : ∀{τ} → Val Base τ → Anf.Val → Set
_≈_ (Const x) (Constₐ x') = x ≡ x'
_≈_ (Const _) (Closureₐ _ _ _) = ⊥
_≈_ (Closure _ _) (Constₐ _) = ⊥
_≈_ {τ = τ => τ'} (Closure env e) (Closureₐ vs ts a) =
  ∀ {x : Val Base τ} {x' : Anf.Val} →
  -- Given related inputs...
  x ≈ x' →
  Σ[ v ∈ Val Base τ' ](Σ[ v' ∈ Anf.Val ](Σ[ vs' ∈ Anf.Env _ ]
    -- Then the upper closure produces v,
    ( cons x env ⊢ e ⇓ v
    -- the IR closure produces v',
    × x' ∷ vs ⊢ts ts ⇓ vs' × vs' ⧺ x' ∷ vs ⊢v a ⇓ v'
    -- and v and v' are related.
    × v ≈ v')))

infix 4 _⊨v_~_ _⊨e⟨_,_⟩~⟨_,_⟩ _⊨ρ_~_
_⊨v_~_ : ∀{τ τ'} →
  Anf.Env offs → Val Staged τ → Val Base τ' → Set
_⊨e⟨_,_⟩~⟨_,_⟩ : ∀{Γ : Ctx Staged n} {τ} {Γ' : Ctx Base n'} {τ'} →
  Anf.Env offs → Env Γ → Tm _ τ Γ → Env Γ' → Tm _ τ' Γ' → Set
data _⊨ρ_~_ : ∀{Γ : Ctx Staged n} {Γ' : Ctx Base n} →
  Anf.Env offs → Env Γ → Env Γ' → Set

envₜ ⊨v Const x ~ Const x' = x ≡ x'
envₜ ⊨v Const _ ~ Closure _ _ = ⊥
envₜ ⊨v Closure _ _ ~ Const _ = ⊥
-- XXX: Do we need envₛ and envₛ' to be related?
envₜ ⊨v eₛ@(Closure {τ₁ = τ} envₛ e) ~ Closure {τ₁ = τ'} envₛ' e' =
  SNᵥ eₛ ×
  ∀ {offs} {env : Anf.Env offs} {x : Val _ τ} {x' : Val _ τ'} →
  envₜ ⊆ env → env ⊨v x ~ x' → env ⊨e⟨ cons x envₛ , e ⟩~⟨ cons x' envₛ' , e' ⟩
envₜ ⊨v Code τ p ~ v' = ∃[ v ] (envₜ ⊢v p ⇓ v × v' ≈ v)

_⊨e⟨_,_⟩~⟨_,_⟩ {offs = offs} envₜ envₛ e envₛ' e' =
  ∃[ v ](∃[ v' ](∃ᵥ[ ts ](
    envₛ , offs ⊢ e ⇓[ ts , v ] ×
    envₛ' ⊢ e' ⇓ v' ×
    Σ[ vs ∈ Anf.Env _ ](envₜ ⊢ts ts ⇓ vs × (vs ⧺ envₜ) ⊨v v ~ v'))))

data _⊨ρ_~_ where
  ~-nil : ∀{envₜ : Anf.Env offs} → envₜ ⊨ρ nil ~ nil
  ~-cons :
    ∀ {Γ : Ctx Staged n} {Γ' : Ctx Base n}
      {envₜ : Anf.Env offs} {envₛ : Env Γ} {env : Env Γ'}
      {τ τ'} {v : Val _ τ} {v' : Val _ τ'} →
    envₜ ⊨v v ~ v' →
    envₜ ⊨ρ envₛ ~ env →
    envₜ ⊨ρ cons v envₛ ~ cons v' env

v~⇒SN : ∀ {envₜ : Anf.Env offs} {τ τ'} {v : Val _ τ} {v' : Val _ τ'} →
  envₜ ⊨v v ~ v' →
  SNᵥ v
v~⇒SN {v = Const x} v~v' = tt
v~⇒SN {v = Closure env x} {v' = Closure _ _} (SN[v] , _) = SN[v]
v~⇒SN {v = Code τ x} v~v' = tt

ρ~⇒⊨ :
  ∀ {envₜ : Anf.Env offs}
    {Γ : Ctx Staged n} {Γ' : Ctx Base n}
    {envₛ : Env Γ} {env : Env Γ'} →
  envₜ ⊨ρ envₛ ~ env →
  Γ ⊨ envₛ
ρ~⇒⊨ ~-nil = models-nil
ρ~⇒⊨ (~-cons v~v' envₛ~env) = models-cons (v~⇒SN v~v') (ρ~⇒⊨ envₛ~env)

wk-v~ :
  ∀ {envₜ : Anf.Env offs} {τ τ'} {v : Val _ τ} {v' : Val _ τ'} x →
  envₜ ⊨v v ~ v' →
  x ∷ envₜ ⊨v v ~ v'
wk-v~ {v = Const x} {Const .x} _ refl = refl
wk-v~ {v = Closure envₛ eₛ} {Closure env e} _ (SN[v] , IH) =
  SN[v] , λ x∷env'⊆env x~x' → IH (⊆-uncons x∷env'⊆env) x~x'
wk-v~ {v = Code τ p} {v'} _ (v , env⊢p⇓v , v'≈v) =
  v , wk-v⇓ _ env⊢p⇓v , v'≈v

wk-ρ~ :
  ∀ {Γ : Ctx Staged n} {Γ' : Ctx Base n}
    {envₜ : Anf.Env offs} {envₛ : Env Γ} {env : Env Γ'} x →
  envₜ ⊨ρ envₛ ~ env →
  x ∷ envₜ ⊨ρ envₛ ~ env
wk-ρ~ _ ~-nil = ~-nil
wk-ρ~ _ (~-cons v~v' envₛ~env) =
  ~-cons (wk-v~ _ v~v') (wk-ρ~ _ envₛ~env)

extend-ρ~ :
  ∀ {Γ : Ctx Staged n} {Γ' : Ctx Base n}
    {envₜ : Anf.Env offs} {envₜ' : Anf.Env m} {envₛ : Env Γ} {env : Env Γ'} →
  envₜ ⊆ envₜ' →
  envₜ ⊨ρ envₛ ~ env →
  envₜ' ⊨ρ envₛ ~ env
extend-ρ~ (⊆-refl Γ) envₛ~env = envₛ~env
extend-ρ~ (⊆-cons t envₜ⊆envₜ') envₛ~env =
  wk-ρ~ t (extend-ρ~ envₜ⊆envₜ' envₛ~env)

~-lookup :
  ∀ {Γ : Ctx Base n} {Γₛ : Ctx Staged n} {τ τ'}
    {envₜ : Anf.Env offs} {env : Env Γ} {envₛ : Env Γₛ} →
  envₜ ⊨ρ envₛ ~ env →
  Γₛ [ i ]= τ →
  Γ [ i ]= τ' →
  ∃[ v ](∃[ v' ](envₛ [ i ]↦ v ∈ τ × env [ i ]↦ v' ∈ τ' × envₜ ⊨v v ~ v'))
~-lookup
    {env = cons v' _} {envₛ = cons v _}
    (~-cons v~v' ρₛ~ρ) here here =
  v , v' , Store.here , Store.here , v~v'
~-lookup (~-cons x ρₛ~ρ) here (there Γₛ[i]=τ') =
  ⊥-elim (<-irrefl refl ([]=→< Γₛ[i]=τ'))
~-lookup (~-cons x ρₛ~ρ) (there Γ[i]=τ) here =
  ⊥-elim (<-irrefl refl ([]=→< Γ[i]=τ))
~-lookup (~-cons x ρₛ~ρ) (there Γ[i]=τ) (there Γₛ[i]=τ') =
  let v , v' , p , p' , v~v' = ~-lookup ρₛ~ρ Γ[i]=τ Γₛ[i]=τ'
   in v , v' , Store.there p , Store.there p' , v~v'

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
  envₜ ⊨ρ envₛ ~ env → e ≤ e' →
  envₜ ⊨e⟨ envₛ , e ⟩~⟨ env , e' ⟩
valueCorrectness ρₛ~ρ (≤-C x) =
  Const x , Const x , [] ,ᵥ evalms-C x , eval-C x , [] , eval-nil , refl
valueCorrectness ρₛ~ρ (≤-V i Γₛ[i]=τ Γ[i]=τ' _) =
  let v , v' , envₛ[i]↦v , env[i]↦v' , v~v' =
        ~-lookup ρₛ~ρ Γₛ[i]=τ Γ[i]=τ'
   in ( v
      , v'
      , []
      ,ᵥ evalms-V envₛ[i]↦v
      , eval-V env[i]↦v'
      , []
      , eval-nil
      , v~v')
valueCorrectness {envₛ = envₛ} {env = env}
    ρₛ~ρ (≤-λ {eₛ = e} {eₜ = e'} _ e≤e') =
  ( Closure envₛ e
  , Closure env e'
  , []
  ,ᵥ evalms-λ envₛ e
  , eval-λ env e'
  , []
  , eval-nil
  , (λ offs SN[x] → strongNormalization (models-cons SN[x] (ρ~⇒⊨ ρₛ~ρ)) offs e)
  , λ ρₜ⊆ρ x~x' → valueCorrectness (~-cons x~x' (extend-ρ~ ρₜ⊆ρ ρₛ~ρ)) e≤e')
valueCorrectness {envₜ = envₜ} ρₛ~ρ (≤-$ e₁≤e₁' e₂≤e₂')
  with f , f' , ts₁ ,ᵥ e₁⇓f , e₁'⇓f' , vs₁ , ts₁⇓vs₁ , f~f' ←
    valueCorrectness ρₛ~ρ e₁≤e₁'
  with x , x' , ts₂ ,ᵥ e₂⇓x , e₂'⇓x' , vs₂ , ts₂⇓vs₂ , x~x' ←
    valueCorrectness (extend-ρ~ (++-⊆ _ vs₁) ρₛ~ρ) e₂≤e₂'
  with f | f' | f~f'
... | Closure _ _ | Closure _ _ | (_ , IH) =
    let v , v' , ts₃ ,ᵥ e⇓v , e'⇓v' , vs₃ , ts₃⇓vs₃ , v~v' =
          IH (++-⊆ _ vs₂) x~x'
     in ( v
        , v'
        , ts₃ ⧺ ts₂ ⧺ ts₁
        ,ᵥ evalms-$ refl refl e₁⇓f e₂⇓x e⇓v
        , eval-$ e₁'⇓f' e₂'⇓x' e'⇓v'
        , vs₃ ⧺ vs₂ ⧺ vs₁
        , ts⇓-join (ts⇓-join ts₁⇓vs₁ ts₂⇓vs₂)
            (≅-subst (_⊢ts ts₃ ⇓ vs₃)
              (≅-symmetric (≅-++-assoc vs₂ vs₁ envₜ)) ts₃⇓vs₃)
        , ≅-subst (_⊨v v ~ v') (reassoc vs₃ vs₂ vs₁ envₜ) v~v')
  where
    reassoc : ∀ {T a b c d}
      (xs : Vec T a) (ys : Vec T b)
      (zs : Vec T c) (ws : Vec T d) →
      xs ⧺ ys ⧺ zs ⧺ ws ≅ (xs ⧺ ys ⧺ zs) ⧺ ws
    reassoc xs ys zs ws = begin
      xs ⧺ ys ⧺ zs ⧺ ws ≅⟨ ≅-cong (xs ⧺_) (≅-symmetric (≅-++-assoc ys zs ws)) ⟩
      xs ⧺ (ys ⧺ zs) ⧺ ws ≅⟨ ≅-symmetric (≅-++-assoc xs (ys ⧺ zs) ws) ⟩
      (xs ⧺ ys ⧺ zs) ⧺ ws ∎
      where
        open ≅-Reasoning
valueCorrectness ρₛ~ρ (≤-let e₁≤e₁' e₂≤e₂') = {! !}
valueCorrectness ρₛ~ρ (≤-+ e≤e' e≤e'') = {! !}
valueCorrectness ρₛ~ρ (≤-CC e≤e') = {! !}
valueCorrectness {offs = offs} {e = λλ τ e} {envₛ} {env = env} {envₜ}
  ρₛ~ρ (≤-λλ {τ = τ} {τ' = τ'} e≤e')
  with f , f' , ts ,ᵥ e⇓f , e'⇓f' , vs , ts⇓vs , f~f' ←
    valueCorrectness ρₛ~ρ e≤e'
  with fSN , (_,ᵥ_ {len = len} tsSN (e⇓SN[ts,f] , SN[f])) ←
    strongNormalization (ρ~⇒⊨ ρₛ~ρ) offs e
  with ts≅tsSN , refl ← evalms-unique e⇓f e⇓SN[ts,f]
  with refl ← ≅-len ts≅tsSN
  with refl ← ≅⇒≡ ts≅tsSN
  with Closure envₛ eₛ ← f
  with Closure envᵢ eᵢ ← f'
  with _ , IH-body ← f~f'
  with Code _ catom , cbody ,ᵥ cbody⇓ , tt ←
    SN[f] (suc (len + offs)) {Code _ (Vₐ (len + offs))} tt
  using envₜ' ← vs ⧺ envₜ
  using clo ← Closureₐ envₜ' cbody catom =
  ( Code (_ => _) (Vₐ (len + offs))
  , Closure envᵢ eᵢ
  , λₐ τ cbody catom ∷ ts
  ,ᵥ evalms-λλ refl e⇓f cbody⇓
  , e'⇓f'
  , clo ∷ vs
  , eval-cons refl ts⇓vs Anf.eval-λ
  , clo
  , Anf.eval-v here
  , inner)
  where
    inner : ∀{x : Val Base τ} {x' : Anf.Val} →
      x ≈ x' →
      Σ[ v ∈ Val Base τ' ](Σ[ v' ∈ Anf.Val ](Σ[ vs' ∈ Anf.Env _ ](
        cons x envᵢ ⊢ eᵢ ⇓ v ×
        x' ∷ envₜ' ⊢ts cbody ⇓ vs' ×
        vs' ⧺ x' ∷ envₜ' ⊢v catom ⇓ v' ×
        v ≈ v')))
    inner {x = x} {x' = x'} x≈x'
      using V[offs']~x ← x' , eval-v here , x≈x'
      with Code τ' p , v' , ts' ,ᵥ eₛ⇓ , eᵢ⇓v' , vs' , ts'⇓vs' , p~v' ←
        IH-body
          {x = Code τ (Vₐ (len + offs))}
          (⊆-cons x' (⊆-refl envₜ')) V[offs']~x
      with v'' , p⇓v'' , v'≈v'' ← p~v'
      with cbody≅ts' , refl ← evalms-unique cbody⇓ eₛ⇓
      with refl ← ≅-len cbody≅ts'
      with refl ← ≅⇒≡ cbody≅ts' =
      v' , v'' ,  vs' , eᵢ⇓v' , ts'⇓vs' , p⇓v'' , v'≈v''
valueCorrectness ρₛ~ρ (≤-++ e≤e' e≤e'') = {! !}
valueCorrectness ρₛ~ρ (≤-$$ e≤e' e≤e'') = {! !}
