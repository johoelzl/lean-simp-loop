/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Monotone version of 1-point elimination for ∃ (and ∀).

  `∃x, t[x, R x a] ~> t[a, rfl]`

with the (reflexive) relation `R`, and `t` is monotone in `R`:
  `∀x y, R x y → t x → t y`.

Then
  (∃x, R x a ∧ p x) ↔ p a
then
  assume h : p a, ⟨a, h, R.refl a⟩
and
  assume ⟨x, hx, hxa⟩, mono x a hxa hx

Or with the following dependent monotonicity:
  `∀x y (h : R x y), t x h → t y R.refl`.

Then
  (∃x, ∃h:R x a, p x h) ↔ p a R.refl
then
  assume h : p a R.refl, ⟨a, h, R.refl a⟩
and
  assume ⟨x, hx, hxa⟩, mono x a hxa hx

-/

#print is_refl

def monotone {α : Sort*} (r : α → α → Prop) (p : α → Prop) : Prop :=
∀x y, r x y → p x → p y

lemma exists_elim_rel {α : Sort*} {r : α → α → Prop} {p : α → Prop} {a : α} :
  (∃x, r a x ∧ p x) ↔ p a :=
⟨_, _⟩
