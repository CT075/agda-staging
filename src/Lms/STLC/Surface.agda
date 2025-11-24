module Lms.STLC.Surface where

open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Vec as Vec using (_∷_)
open import Data.Product as Prod
open import Data.Maybe

open import Data.Context as Context using (_[_]=_)

open import Lms.STLC.Core as Core hiding (Tm; Ctx; Typ)

Typ = Core.Typ Staged
Ctx = Core.Ctx Staged

private variable
  n i : ℕ
  τ τ' : Typ
  Γ : Ctx n

data Tm : Set where
  C : ℕ → Tm
  V : ℕ → Tm
  λ' : Typ → Tm → Tm
  _$_ : Tm → Tm → Tm
  _+'_ : Tm → Tm → Tm
  Let : Tm → Tm → Tm
  λλ : Tm → Tm

private variable
  e e₁ e₂ : Tm
