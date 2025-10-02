module Data.Gas.Lemmas where

open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import Data.Gas

private variable
  A B C T : Set

done≢timeout : ∀{v : T} → Done v ≢ Timeout
done≢timeout ()

open OrTimeoutOps

liftA2-sub2 : ∀ (f : A → B → C) {ax ay ax' ay'} →
  ax ≡ ax' → ay ≡ ay' → liftA2 f ax ay ≡ liftA2 f ax' ay'
liftA2-sub2 f {ax = ax} {ay = ay} {ax' = ax'} {ay' = ay'} ax≡ax' ay≡ay' =
  begin
    liftA2 f ax ay ≡⟨ cong (λ t → liftA2 f t ay) ax≡ax' ⟩
    liftA2 f ax' ay ≡⟨ cong (liftA2 f ax') ay≡ay' ⟩
    liftA2 f ax' ay'
  ∎
  where open ≡-Reasoning

record liftA2Intermediates
    (f : A → B → C)
    (afst : OrTimeout A)
    (asnd : OrTimeout B)
    (v : C) : Set where
  constructor la2i
  field
    fst : A
    snd : B
    afst→fst : afst ≡ Done fst
    asnd→snd : asnd ≡ Done snd
    run-f : f fst snd ≡ v

liftA2-done : ∀ {f : A → B → C} ax ay {v} →
  liftA2 f ax ay ≡ Done v → liftA2Intermediates f ax ay v
liftA2-done Timeout _ p = ⊥-elim (done≢timeout (sym p))
liftA2-done (Done x) Timeout p = ⊥-elim (done≢timeout (sym p))
liftA2-done {f = f} (Done x) (Done y) {v} p = la2i x y refl refl (unDone-≡ p)
  where
    unDone-≡ : Done (f x y) ≡ Done v → f x y ≡ v
    unDone-≡ refl = refl

bindM2-sub2 : ∀ (f : A → B → OrTimeout C) {mx my mx' my'} →
  mx ≡ mx' → my ≡ my' → bindM2 f mx my ≡ bindM2 f mx' my'
bindM2-sub2 f {mx = mx} {my = my} {mx' = mx'} {my' = my'} mx≡mx' my≡my' =
  begin
    bindM2 f mx my ≡⟨ cong (λ t → bindM2 f t my) mx≡mx' ⟩
    bindM2 f mx' my ≡⟨ cong (bindM2 f mx') my≡my' ⟩
    bindM2 f mx' my'
  ∎
  where open ≡-Reasoning

record bindM2Intermediates
    (f : A → B → OrTimeout C)
    (mfst : OrTimeout A)
    (msnd : OrTimeout B)
    (v : C) : Set where
  constructor bm2i
  field
    fst : A
    snd : B
    mfst→fst : mfst ≡ Done fst
    msnd→snd : msnd ≡ Done snd
    run-f : f fst snd ≡ Done v

bindM2-done : ∀ {f : A → B → OrTimeout C} mx my {v} →
  bindM2 f mx my ≡ Done v → bindM2Intermediates f mx my v
bindM2-done Timeout _ p = ⊥-elim (done≢timeout (sym p))
bindM2-done (Done x) Timeout p = ⊥-elim (done≢timeout (sym p))
bindM2-done {f = f} (Done x) (Done y) {v = v} p = bm2i x y refl refl p
