/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Binder elimination, also called 1-point rules.

We assume a binder `B : p → Π (α : Sort u), (α → t) → t`, where `t` is a type depending on `p`.
Examples:
  ∀: there is no `p` and `t` is `Prop`.
  ⨅, ⨆: here p is `β` and `[complete_lattice β]`, `p` is `β`

Problem:
  ∀x, _ should be a binder, but is not a constant! To match we need a parametric match function.

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

protected meta def check_eq (b : binder_eq_elim) (x : expr) : expr → tactic bool
| `(@eq %%β %%l %%r) := return ((l = x ∧ ¬ x.occurs r) ∨ (r = x ∧ ¬ x.occurs l))
| _ := return ff

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

/-- `b.find x n e` looks for a binder in the binder-prefix of `e`, where a equality on `x` is bound.
It returns all occurrences of equalitie under binders, to each occurence `n` is added.

TODO: Maybe the list of occurences is not necessary. We can check at each equality if the
other side depends on `x`. Reason: everything needs to be parameterized in `x`, either it is hidden
using some kind of relation, or it appears explicitly.

Can we already decide by looking at the binder type if we should push or pull?
  yes: look at the dependencies
-/
protected meta def find (b : binder_eq_elim) (x : expr) : ℕ → expr → tactic (list ℕ)
| i e := do
  some (β, f) ← try_core $ b.match_binder e | return [],
  b ← b.check_eq x β,
  is ← (do
    (lam n bi d bd) ← return f | return [],
    x ← mk_local' n bi d,
    find (i + 1) (bd.instantiate_var x)),
  return (if b then i :: is else is)

protected meta def conv (b : binder_eq_elim) : conv unit := do
  (β, f) ← lhs >>= (lift_tactic ∘ b.match_binder),
  (lam n bi d bd) ← return f,
  x ← mk_local' n bi d,
  is ← b.find x 0 (bd.instantiate_var x),
  is.mfirst (b.adapt_rel ∘ b.pull)

end binder_eq_elim

end simp_loop
