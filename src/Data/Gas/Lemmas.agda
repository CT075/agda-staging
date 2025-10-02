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

bindM2-sub₁ : ∀ (f : A → B → OrTimeout C) {mx} my {v} →
  mx ≡ v → bindM2 f mx my ≡ bindM2 f v my
bindM2-sub₁ f my = cong (λ t → bindM2 f t my)

bindM2-sub₂ : ∀ (f : A → B → OrTimeout C) mx {my} {v} →
  my ≡ v → bindM2 f mx my ≡ bindM2 f mx v
bindM2-sub₂ f mx = cong (bindM2 f mx)

bindM2-sub-both : ∀ (f : A → B → OrTimeout C) {mx my mx' my'} →
  mx ≡ mx' → my ≡ my' → bindM2 f mx my ≡ bindM2 f mx' my'
bindM2-sub-both f {mx = mx} {my = my} {mx' = mx'} {my' = my'} mx≡mx' my≡my' =
  begin
    bindM2 f mx my ≡⟨ bindM2-sub₁ f my mx≡mx' ⟩
    bindM2 f mx' my ≡⟨ bindM2-sub₂ f mx' my≡my' ⟩
    bindM2 f mx' my'
  ∎
  where open ≡-Reasoning

bindM2-done₁ : ∀ (f : A → B → OrTimeout C) mx my {v} →
  bindM2 f mx my ≡ Done v → ∃[ x ](mx ≡ Done x)
bindM2-done₁ f Timeout _ p = ⊥-elim (done≢timeout (sym p))
bindM2-done₁ f (Done x) _ p = (x , refl)

bindM2-done₂ : ∀ (f : A → B → OrTimeout C) mx my {v} →
  bindM2 f mx my ≡ Done v → ∃[ v' ](my ≡ Done v')
bindM2-done₂ f Timeout _ p = ⊥-elim (done≢timeout (sym p))
bindM2-done₂ f (Done x) Timeout p = ⊥-elim (done≢timeout (sym p))
bindM2-done₂ f (Done x) (Done y) p = (y , refl)

bindM2-done : ∀ {f : A → B → OrTimeout C} {mx my x y v} →
  mx ≡ Done x → my ≡ Done y → bindM2 f mx my ≡ Done v →
  f x y ≡ Done v
bindM2-done {f = f} {mx = mx} {my = my} {x = x} {y = y} {v = v} px py p = sym (begin
  Done v ≡⟨ sym p ⟩
  bindM2 f mx my ≡⟨ bindM2-sub-both f px py ⟩
  bindM2 f (Done x) (Done y) ≡⟨⟩
  f x y
  ∎)
  where open ≡-Reasoning
