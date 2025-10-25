module Lms.STLC.Lemmas where

open import Data.Nat as Nat
open import Data.Nat.Properties as Nat
open import Data.Product
open import Data.List as List
  using (List; length)
  renaming (_∷_ to _∷ₗ_; [] to nilₗ; _++_ to _++ₗ_)
open import Data.List.Properties as List
open import Relation.Binary.PropositionalEquality

open import Data.Nat.Extensions
open import Data.Vec.Extensions
open import Lms.STLC

private variable
  T : Set
  n n' : ℕ
  fresh fresh' fresh'' fresh''' : ℕ
  ts ts₁ ts₂ ts₃ : List AnfTm

length-lemma : ∀{xs₁ : List T} {xs₂ x₁ x₂} →
  length xs₁ ≡ x₁ → length xs₂ ≡ x₂ →
  length (xs₁ ++ₗ xs₂) ≡ x₁ + x₂
length-lemma {xs₁ = xs₁} {xs₂} {x₁} {x₂} len₁ len₂ =
  trans (length-++ xs₁ {xs₂}) (cong₂ _+_ len₁ len₂)

evalms-fresh : ∀{Γ : Ctx Staged n} {env : Env Γ} {τ} {e : Tm _ τ _} {v} →
  env ⊢⟨ e , fresh ⟩⇓⟨[ ts , v ], fresh' ⟩ →
  fresh ≤ fresh' × length ts ≡ ∣ fresh' - fresh ∣
evalms-fresh {fresh = fresh} (evalms-C _) = ≤-refl , sym (∣n-n∣≡0 fresh)
evalms-fresh {fresh = fresh} (evalms-V i v x) = ≤-refl , sym (∣n-n∣≡0 fresh)
evalms-fresh {fresh = fresh} evalms-λ = ≤-refl , sym (∣n-n∣≡0 fresh)
evalms-fresh (evalms-$ x x₁ x₂) = {! !}
evalms-fresh (evalms-let
    {ts₁ = ts₁} {ts₂ = ts₂} ⟨e₁,i⟩⇓⟨[ts₁,x],i'⟩ ⟨e₂,i'⟩⇓[ts₂,v],i'') =
  let i≤i' , len[ts₁]≡∣i'-i∣ = evalms-fresh ⟨e₁,i⟩⇓⟨[ts₁,x],i'⟩
      i'≤i'' , len[ts₂]≡∣i''-i'∣ = evalms-fresh ⟨e₂,i'⟩⇓[ts₂,v],i''
      len[ts₂++ts₁]≡∣i''-i'∣+∣i'-i∣ =
        -- I am astonished that Agda can't infer xs₁ and xs₂ from context.
        length-lemma {xs₁ = ts₂} {xs₂ = ts₁} len[ts₂]≡∣i''-i'∣ len[ts₁]≡∣i'-i∣
      ∣i''-i'∣+∣i'-i∣≡∣i''-i∣ = ∣a-b∣+|b-c∣≡∣a-c∣ i'≤i'' i≤i'
   in ≤-trans i≤i' i'≤i'' ,
      trans len[ts₂++ts₁]≡∣i''-i'∣+∣i'-i∣ ∣i''-i'∣+∣i'-i∣≡∣i''-i∣
evalms-fresh (evalms-+ x x₁ x₂) = {! !}
evalms-fresh (evalms-CC x) = {! !}
evalms-fresh (evalms-++ x x₁) = {! !}
