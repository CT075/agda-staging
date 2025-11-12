module Lms.STLC.Normalization where

open import Data.Nat as Nat
open import Data.Nat.Properties as Nat
open import Data.Product as Prod
open import Data.Vec as Vec hiding (_[_]=_) renaming (_++_ to _⧺_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (refl)

open import Data.Vec.Extensions as Vec
open import Data.Context hiding (Ctx)
open import Data.Store as Store

open import Lms.STLC.Core
open import Lms.STLC.IR as Anf hiding (Val; Env)
open import Lms.STLC.Evaluation

private variable
  n n₁ n₂ i : ℕ
  τ τ' : Typ Staged
  Γ : Ctx Staged n
  env : Env Γ

SNᵥ : {τ : Typ Staged} → Val _ τ → Set
SN : {τ : Typ Staged} → ℕ → Env Γ → Tm _ τ Γ → Set

SNᵥ (Const x) = ⊤
SNᵥ (Code τ p) = ⊤
SNᵥ (Closure env body) = ∀ offs {x} → SNᵥ x → SN offs (cons x env) body

SN {τ = τ} offs env e =
  Σ[ v ∈ Val _ τ ](∃ᵥ[ ts ](env , offs ⊢ e ⇓[ ts , v ] × SNᵥ v))

infix 4 _⊨_
data _⊨_ : (Γ : Ctx Staged n) → Env Γ → Set where
  models-nil : [] ⊨ nil
  models-cons : ∀{v : Val _ τ} →
    SNᵥ v → Γ ⊨ env → τ ∷ Γ ⊨ cons v env

lookup-⊨ : Γ ⊨ env → Γ [ i ]= τ → Σ[ v ∈ Val _ τ ](env [ i ]↦ v ∈ τ × SNᵥ v)
lookup-⊨ (models-cons v∈⟦τ⟧ _) here = _ , Store.here , v∈⟦τ⟧
lookup-⊨ (models-cons _ Γ⊨env) (there Γ[i]=τ) =
  let v , env[i]↦v , v∈⟦τ⟧ = lookup-⊨ Γ⊨env Γ[i]=τ
   in v , Store.there env[i]↦v , v∈⟦τ⟧

strongNormalization : Γ ⊨ env → (offs : ℕ) → (e : Tm _ τ Γ) → SN offs env e
strongNormalization Γ⊨env offs (C x) = Const x , [] ,ᵥ evalms-C x , tt
strongNormalization Γ⊨env offs (V i Γ[i]=v) =
  let v , env[i]↦v , v∈⟦τ⟧ = lookup-⊨ Γ⊨env Γ[i]=v
   in v , [] ,ᵥ evalms-V env[i]↦v , v∈⟦τ⟧
strongNormalization {env = env} Γ⊨env offs (λ' τ e) =
  Closure env e , [] ,ᵥ evalms-λ _ _ ,
    λ offs' x∈⟦τ⟧ → strongNormalization (models-cons x∈⟦τ⟧ Γ⊨env) offs' e
strongNormalization Γ⊨env offs (e₁ $ e₂) =
  let
    Cf , xs₁@(ts₁ ,ᵥ e₁⇓f , f∈⟦τ=>τ'⟧) = strongNormalization Γ⊨env offs e₁
    offs' = Vec.∃ᵥ-syntax.len xs₁ + offs
    x , ts₂ ,ᵥ e₂⇓x , x∈⟦τ⟧ = strongNormalization Γ⊨env offs' e₂
  in
    cont e₁⇓f e₂⇓x f∈⟦τ=>τ'⟧ x∈⟦τ⟧
  where
    cont : ∀{Cf x} {ts₁ : Vec Anf.Expr n₁} {ts₂ : Vec Anf.Expr n₂} →
      env , offs ⊢ e₁ ⇓[ ts₁ , Cf ] → env , (n₁ + offs) ⊢ e₂ ⇓[ ts₂ , x ] →
      SNᵥ Cf → SNᵥ x →
      SN offs env (e₁ $ e₂)
    cont {n₁ = n₁} {n₂ = n₂} {Cf = Closure env' body} {ts₁ = ts₁} {ts₂ = ts₂}
        e₁⇓f e₂⇓x f∈⟦τ=>τ'⟧ x∈⟦τ⟧ =
      let v , ts₃ ,ᵥ body⇓v , v∈⟦τ'⟧ = f∈⟦τ=>τ'⟧ (n₂ + n₁ + offs) x∈⟦τ⟧
      in ( v
         , ts₃ ⧺ ts₂ ⧺ ts₁
         ,ᵥ evalms-$ refl (+-assoc n₂ n₁ offs) e₁⇓f e₂⇓x body⇓v
         , v∈⟦τ'⟧)
strongNormalization Γ⊨env offs (Let e₁ e₂) =
  let
    x₁ , xs₁@(ts₁ ,ᵥ e₁⇓x₁ , x₁∈⟦τ₁⟧) = strongNormalization Γ⊨env offs e₁
    offs' = Vec.∃ᵥ-syntax.len xs₁ + offs
    x₂ , ts₂ ,ᵥ e₂⇓x₂ , x₂∈⟦τ₂⟧ =
      strongNormalization (models-cons x₁∈⟦τ₁⟧ Γ⊨env) offs' e₂
  in
    x₂ , ts₂ ⧺ ts₁ ,ᵥ evalms-let refl e₁⇓x₁ e₂⇓x₂ , x₂∈⟦τ₂⟧
strongNormalization Γ⊨env offs (e₁ +' e₂) =
  let
    Cx₁ , xs₁@(ts₁ ,ᵥ e₁⇓x₁ , x₁∈⟦N⟧) = strongNormalization Γ⊨env offs e₁
    offs' = Vec.∃ᵥ-syntax.len xs₁ + offs
    Cx₂ , ts₂ ,ᵥ e₂⇓x₂ , x₂∈⟦N⟧ =  strongNormalization Γ⊨env offs' e₂
  in
    cont e₁⇓x₁ e₂⇓x₂
  where
    cont : ∀{Cx₁ Cx₂} {ts₁ : Vec Anf.Expr n₁} {ts₂ : Vec Anf.Expr n₂} →
      env , offs ⊢ e₁ ⇓[ ts₁ , Cx₁ ] → env , (n₁ + offs) ⊢ e₂ ⇓[ ts₂ , Cx₂ ] →
      SN offs env (e₁ +' e₂)
    cont {Cx₁ = Const x₁} {Cx₂ = Const x₂} {ts₁ = ts₁} {ts₂ = ts₂}
        e₁⇓x₁ e₂⇓x₂ =
      Const (x₁ + x₂) , ts₂ ⧺ ts₁ ,ᵥ evalms-+ refl refl e₁⇓x₁ e₂⇓x₂ , tt
strongNormalization Γ⊨env offs (CC e) =
  let Cx , ts ,ᵥ e⇓x , x∈⟦N⟧ = strongNormalization Γ⊨env offs e
   in cont e⇓x
  where
    cont : ∀{Cx} {ts : Vec Anf.Expr n} →
      env , offs ⊢ e ⇓[ ts , Cx ] →
      SN offs env (CC e)
    cont {Cx = Const x} {ts} e⇓x = Code N (Cₐ x) , ts ,ᵥ evalms-CC e⇓x , tt
strongNormalization Γ⊨env offs (λλ τ e) =
  let
    Cf , ts ,ᵥ e⇓f , f∈⟦Rep[τ]=>Rep[τ']⟧ =
      strongNormalization Γ⊨env offs e
  in
    cont e⇓f f∈⟦Rep[τ]=>Rep[τ']⟧
  where
    unwrap : ∀{τ} (Ca : Val _ (Rep τ)) → Anf.Atom
    unwrap (Code τ a) = a

    cont : ∀{Cf} {ts : Vec Anf.Expr n} →
      env , offs ⊢ e ⇓[ ts , Cf ] → SNᵥ Cf →
      SN offs env (λλ τ e)
    cont {n = n} {Cf = Closure env' body} {ts} e⇓f f∈⟦Rep[τ]=>Rep[τ']⟧ with
      f∈⟦Rep[τ]=>Rep[τ']⟧ (suc (n + offs)) {x = Code _ (Vₐ (n + offs))} tt
    ... | Code _ a , tsᵢ ,ᵥ body⇓a , a∈⟦Rep[τ']⟧ =
          ( Code _ (Vₐ (n + offs))
          , λₐ _ tsᵢ a ∷ ts
          ,ᵥ evalms-λλ refl e⇓f body⇓a
          , tt)
strongNormalization Γ⊨env offs (e₁ ++ e₂) =
  let
    Cx₁ , xs₁@(ts₁ ,ᵥ e₁⇓x₁ , x₁∈⟦Rep[N]⟧) = strongNormalization Γ⊨env offs e₁
    offs' = Vec.∃ᵥ-syntax.len xs₁ + offs
    Cx₂ , ts₂ ,ᵥ e₂⇓x₂ , x₂∈⟦Rep[N]⟧ =  strongNormalization Γ⊨env offs' e₂
  in
    cont e₁⇓x₁ e₂⇓x₂
  where
    cont : ∀{Cx₁ Cx₂} {ts₁ : Vec Anf.Expr n₁} {ts₂ : Vec Anf.Expr n₂} →
      env , offs ⊢ e₁ ⇓[ ts₁ , Cx₁ ] → env , (n₁ + offs) ⊢ e₂ ⇓[ ts₂ , Cx₂ ] →
      SN offs env (e₁ ++ e₂)
    cont {n₁ = n₁} {n₂ = n₂} {Cx₁ = Code N a₁} {Cx₂ = Code N a₂}
        {ts₁ = ts₁} {ts₂ = ts₂} e₁⇓x₁ e₂⇓x₂ =
      ( Code N (Vₐ (n₂ + n₁ + offs))
      , a₁ +ₐ a₂ ∷ ts₂ ⧺ ts₁
      ,ᵥ evalms-++ refl (+-assoc n₂ n₁ offs) e₁⇓x₁ e₂⇓x₂
      , tt)
strongNormalization Γ⊨env offs (e₁ $$ e₂) =
  let
    Cx₁ , xs₁@(ts₁ ,ᵥ e₁⇓x₁ , x₁∈⟦Rep[τ=>τ']⟧) =
      strongNormalization Γ⊨env offs e₁
    offs' = Vec.∃ᵥ-syntax.len xs₁ + offs
    Cx₂ , ts₂ ,ᵥ e₂⇓x₂ , x₂∈⟦Rep[τ]⟧ =  strongNormalization Γ⊨env offs' e₂
  in
    cont e₁⇓x₁ e₂⇓x₂
  where
    cont : ∀{Cx₁ Cx₂} {ts₁ : Vec Anf.Expr n₁} {ts₂ : Vec Anf.Expr n₂} →
      env , offs ⊢ e₁ ⇓[ ts₁ , Cx₁ ] → env , (n₁ + offs) ⊢ e₂ ⇓[ ts₂ , Cx₂ ] →
      SN offs env (e₁ $$ e₂)
    cont {n₁ = n₁} {n₂ = n₂}
        {Cx₁ = Code (τ => τ') a₁} {Cx₂ = Code τ a₂} {ts₁ = ts₁} {ts₂ = ts₂}
        e₁⇓x₁ e₂⇓x₂ =
      ( Code τ' (Vₐ (n₂ + n₁ + offs))
      , a₁ $ₐ a₂ ∷ ts₂ ⧺ ts₁
      ,ᵥ evalms-$$ refl (+-assoc n₂ n₁ offs) e₁⇓x₁ e₂⇓x₂
      , tt)
