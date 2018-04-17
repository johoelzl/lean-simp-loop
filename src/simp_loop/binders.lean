/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Binder elimination

We assume a binder `B : p → Π (α : Sort u), (α → t) → t`, where `t` is a type depending on `p`.
Examples:
  ∃: there is no `p` and `t` is `Prop`.
  ⨅, ⨆: here p is `β` and `[complete_lattice β]`, `p` is `β`

Problem: ∀x, _ should be a binder, but is not a constant! Needs special matcher.

Provide a mechanism to rewrite:

  B (x : α) ..x.. (h : x = t), p x  =  B ..x/t.., p t

Here ..x.. are binders, maybe also some constants which provide commutativity rules with `B`.
-/
import simp_loop.conv

namespace simp_loop
open conv_t tactic expr

meta structure binder_eq_elim :=
(match_binder  : expr → tactic (expr × expr))    -- returns the bound type and body
(adapt_rel     : conv unit → conv unit)          -- optionally adapt `eq` to `iff`
(apply_comm    : conv unit)                      -- apply commutativity rule
(apply_congr   : (expr → conv unit) → conv unit) -- apply congruence rule
(apply_elim_eq : conv unit)                      -- (B (x : β) (h : x = t), s x) = s t

namespace binder_eq_elim

protected meta def check_eq (b : binder_eq_elim) (x : expr) : expr → tactic unit
| `(@eq %%β %%l %%r) := guard ((l = x ∧ ¬ x.occurs r) ∨ (r = x ∧ ¬ x.occurs l))
| _ := fail "no match"

protected meta def push (b : binder_eq_elim) (x : expr) : ℕ → conv unit
| 0       := do trace "finished push", trace_lhs,
  return ()
| (n + 1) :=
  (do trace ("push " ++ to_string n ++ " the current binder to the right"), trace_lhs,
    b.apply_comm,
    b.apply_congr $ λx, push n) <|>
  (do trace ("push " ++ to_string n ++ " there is a dependency: switch to the right binder"), trace_lhs,
    b.apply_congr $ λx, push n)

protected meta def pull (b : binder_eq_elim) : ℕ → conv unit
 | 0       := do trace "finished pull", trace_lhs,
  b.apply_elim_eq
| (n + 1) :=
  (do trace ("pull (" ++ to_string n ++ ") the non-dependent binders to the left"), trace_lhs,
    b.apply_comm,
    b.apply_congr $ λx, pull n) <|>
  (do trace ("pull (" ++ to_string n ++ ") the right (dependent binder) to the right, then try again"), trace_lhs,
    b.apply_congr $ λe, b.push e (n + 1),
    pull n)

protected meta def check (b : binder_eq_elim) (x : expr) : ℕ → expr → tactic ℕ
| i e := do
  (β, f) ← b.match_binder e,
  (b.check_eq x β >> return i)
  <|> (do
    (lam n bi d bd) ← return f,
    x ← mk_local' n bi d,
    check (i + 1) (bd.instantiate_var x))

protected meta def conv (b : binder_eq_elim) : conv unit := do
  (β, f) ← lhs >>= (lift_tactic ∘ b.match_binder),
  (lam n bi d bd) ← return f,
  x ← mk_local' n bi d,
  i ← b.check x 0 (bd.instantiate_var x),
  b.adapt_rel (b.pull i)



end binder_eq_elim

section exists_eq_elim

theorem {u v} exists_comm {α : Sort u} {β : Sort v} (p : α → β → Prop) :
  (∃a b, p a b) ↔ (∃b a, p a b) :=
⟨λ⟨a, ⟨b, h⟩⟩, ⟨b, ⟨a, h⟩⟩, λ⟨a, ⟨b, h⟩⟩, ⟨b, ⟨a, h⟩⟩⟩

theorem {u v} exists_elim_eq_left {α : Sort u} (a : α) (p : Π(a':α), a' = a → Prop) :
  (∃(a':α) (h : a' = a), p a' h) ↔ p a rfl :=
⟨λ⟨a', ⟨h, p_h⟩⟩, match a', h, p_h with ._, rfl, h := h end, λh, ⟨a, rfl, h⟩⟩

theorem {u v} exists_elim_eq_right {α : Sort u} (a : α) (p : Π(a':α), a = a' → Prop) :
  (∃(a':α) (h : a = a'), p a' h) ↔ p a rfl :=
⟨λ⟨a', ⟨h, p_h⟩⟩, match a', h, p_h with ._, rfl, h := h end, λh, ⟨a, rfl, h⟩⟩

meta def exists_eq_elim : binder_eq_elim :=
{ match_binder  := λe, (do `(@Exists %%β %%f) ← return e, return (β, f)),
  adapt_rel     := propext,
  apply_comm    := apply_const ``exists_comm,
  apply_congr   := congr_binder `exists_congr,
  apply_elim_eq := apply_const ``exists_elim_eq_left <|> apply_const ``exists_elim_eq_right }

end exists_eq_elim

section forall_eq_elim

theorem {u v} forall_comm {α : Sort u} {β : Sort v} (p : α → β → Prop) :
  (∀a b, p a b) ↔ (∀b a, p a b) :=
⟨assume h b a, h a b, assume h b a, h a b⟩

theorem {u v} forall_elim_eq_left {α : Sort u} (a : α) (p : Π(a':α), a' = a → Prop) :
  (∀(a':α)(h : a' = a), p a' h) ↔ p a rfl :=
⟨λh, h a rfl, λh a' h_eq, match a', h_eq with ._, rfl := h end⟩

theorem {u v} forall_elim_eq_right {α : Sort u} (a : α) (p : Π(a':α), a = a' → Prop) :
  (∀(a':α)(h : a = a'), p a' h) ↔ p a rfl :=
⟨λh, h a rfl, λh a' h_eq, match a', h_eq with ._, rfl := h end⟩

meta def forall_eq_elim : binder_eq_elim :=
{ match_binder  := λe, (do (expr.pi n bi d bd) ← return e, return (d, expr.lam n bi d bd)),
  adapt_rel     := propext,
  apply_comm    := apply_const ``forall_comm,
  apply_congr   := congr_binder `forall_congr,
  apply_elim_eq := apply_const ``forall_elim_eq_left <|> apply_const ``forall_elim_eq_right }

end forall_eq_elim

section test

universes u v w w₂
variables {α : Type u} {β : Type v} {ι : Sort w} {ι₂ : Sort w₂} {a : α} {γ : β → Type} {δ : α → Type}
  {f : α → β} {p : β → Prop}

example : (∃b, ∃c:γ b, ∃h : f a = b, p b) ↔ (∃c:γ (f a), p (f a)) :=
by conversion exists_eq_elim.conv

example : (∃b, ∃c:γ b, ∃a, ∃h : f a = b, p b) ↔ (∃a, ∃c:γ (f a), p (f a)) :=
by conversion exists_eq_elim.conv

example {f : Πa, δ a → β} :
  (∃b, ∃c:γ b, ∃a, ∃d:δ a, ∃h : f a d = b, p b) ↔ (∃a, ∃d:δ a, ∃c:γ (f a d), p (f a d)) :=
by conversion exists_eq_elim.conv

example {f : Πa, δ a → β} :
  (∃b, ∃a, ∃c:γ b, ∃d:δ a, ∃h : f a d = b, p b) ↔ (∃a, ∃d:δ a, ∃c:γ (f a d), p (f a d)) :=
by conversion exists_eq_elim.conv

example {f : Πa, δ a → β} :
  (∃b, ∃a, ∃d:δ a, ∃c:γ b, ∃h : f a d = b, p b) ↔ (∃a, ∃d:δ a, ∃c:γ (f a d), p (f a d)) :=
by conversion exists_eq_elim.conv

example {f : Πa, δ a → β} :
  (∃b, ∃a, ∃d:δ a, ∃h : f a d = b, ∃c:γ b, p b) ↔ (∃a, ∃d:δ a, ∃c:γ (f a d), p (f a d)) :=
by conversion exists_eq_elim.conv

example {f : Πa, δ a → β} :
  (∃b, ∃a, ∃d:δ a, ∃h' : a = a ∧ b = b, ∃h : f a d = b, ∃c:γ b, p b) ↔ _ :=
by conversion exists_eq_elim.conv

end test

#exit -- lattice theory only in mathlib

meta def supr_eq_elim : binder_eq_elim :=
{ match_binder  := λe, (do `(@lattice.supr %%α %%β %%cl %%f) ← return e, return (β, f)),
  adapt_rel     := λc, (do r ← current_relation, guard (r = `eq), c),
  apply_comm    := applyc ``lattice.supr_comm,
  apply_congr   := congr_arg ∘ funext',
  apply_elim_eq := applyc ``lattice.supr_supr_eq_left <|> applyc ``lattice.supr_supr_eq_right }

meta def infi_eq_elim : binder_eq_elim :=
{ match_binder  := λe, (do `(@lattice.infi %%α %%β %%cl %%f) ← return e, return (β, f)),
  adapt_rel     := λc, (do r ← current_relation, guard (r = `eq), c),
  apply_comm    := applyc ``lattice.infi_comm,
  apply_congr   := congr_arg ∘ funext',
  apply_elim_eq := applyc ``lattice.infi_infi_eq_left <|> applyc ``lattice.infi_infi_eq_right }

section
open lattice
variables [complete_lattice α]

theorem Inf_image {s : set β} {f : β → α} : Inf (set.image f s) = (⨅ a ∈ s, f a) :=
begin
  simp [Inf_eq_infi, infi_and],
  conversion infi_eq_elim.conv,
end

theorem Sup_image {s : set β} {f : β → α} : Sup (set.image f s) = (⨆ a ∈ s, f a) :=
begin
  simp [Sup_eq_supr, supr_and],
  conversion supr_eq_elim.conv,
end

end
