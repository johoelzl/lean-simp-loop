/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Binder elimination
Also called 1-point rules.

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

#check add_left_cancel_semigroup

section

set_option pp.all true
example {α β : Type} {f : β → α} {p : α → Prop} :
  ∃a : α, ∃b : (λa:α, β) a, ∃h : a = f b, p a :=
_

end

namespace simp_loop
open conv_t tactic expr

namespace exists_eq_elim

meta inductive info
| binder (v : expr) (dependent : bool) | operator (side : bool)

meta def check_eq (x : expr) (deps : list expr) : expr → bool
| `(%%l = %%r) := (l = x ∧ deps.all (λx, ¬ x.occurs r)) ∨ (r = x ∧ deps.all (λx, ¬ x.occurs l))
| _ := ff

meta structure binder_eq_elim :=
(match_binder       : expr → tactic (expr × expr))    -- returns the bound type and body
(adapt_rel          : conv unit → conv unit)          -- optionally adapt `eq` to `iff`
(apply_comm         : conv unit)                      -- apply commutativity rule
(apply_op_comm      : bool → conv unit)                      -- apply commutativity rule
(apply_congr    {α} : (expr → conv α) → conv α) -- apply congruence rule
(apply_op_congr {α} : bool → conv α → conv α) -- apply congruence rule
(apply_elim_eq      : conv unit)                      -- (B (x : β) (h : x = t), s x) = s t

section
parameter (b : binder_eq_elim)
/-

Expected normal form:

  all conjuncts are inside existentials
    `exists_and_distrib_left`, `exists_and_distrib_right`
  no conjuncts or existentials inside the binder type of a existental:
    `exists_and`, `exists_exists`

  now we have two cases:
    `∃x, ∃ ⋯ ∃ , … ∧ x = t ∧ …`
  or
    `∃x, ∃ ⋯ ∃ h : x = t, …`

-/


meta def push : list info → conv unit := λ_, skip
/-
| 0       := do trace "finished push", trace_lhs,
  return ()
| (n + 1) :=
  (do trace ("push " ++ to_string n ++ " the current binder to the right"), trace_lhs,
    b.apply_comm,
    b.apply_congr $ λx, push n) <|>
  (do trace ("push " ++ to_string n ++ " there is a dependency: switch to the right binder"), trace_lhs,
    b.apply_congr $ λx, push n)
-/

meta def pull : list info → conv unit
| []       := do trace "finished pull", trace_lhs,
  b.apply_elim_eq
| (info.binder false :: ps) := do trace "independent binder", trace_lhs,
  b.apply_comm, b.apply_congr $ λx, pull ps
| (info.binder true :: ps) := do trace "dependent binder", trace_lhs,
  b.apply_congr (λe, push ps),
  pull ps
| (info.operator true :: ps) := do trace "operator left", trace_lhs,
  b.congr_left (push ps),
  pull ps
| (info.operator true :: ps) := do trace "operator right", trace_lhs,
  b.congr_right (push ps),
  pull ps

/-
| [i, _] :=
  (do trace ("pull (" ++ to_string n ++ ") the non-dependent binders to the left"), trace_lhs,
    b.apply_comm,
    b.apply_congr $ λx, pull n) <|>
  (do trace ("pull (" ++ to_string n ++ ") the right (dependent binder) to the right, then try again"), trace_lhs,
    b.apply_congr $ λe, b.push e (n + 1),
    pull n)
-/

meta def analyse (v : expr) (deps : list expr) : expr → tactic (option $ list $ info × expr)
| `(@Exists %%α %%p) := if check_eq v deps α then
    return none
  else do
    (lam pp_n bi domain body) ← return p,
    x ← mk_local' pp_n bi domain,
    return [(info.binder v (deps.any $ λv, v.occurs α), body.instantiate_var x)]
| `(%%p ∧ %%q) := do
  return [(info.operator tt, p), (info.operator tt, q)]
| t := return $ if check_eq v deps t then none else some []

meta def find (v : expr) : list expr → expr → tactic (list info) | deps e := do
some ps ← analyse v deps e | return [],
ps' ← ps.mmap (λd, do
  deps ← return $ match d with (info.binder v tt, _) := v :: deps | _ := deps end,
  ps ← find deps d.2,
  return $ d.1 :: ps),
return ps'.join

meta def reorder_equality : list info → conv bool
| [] := do
  `(_ = _) ← lhs | return tt, -- inner term is binder
  return ff -- inner term is equality
| [info.binder _ _] := _
| [info.operator _] := _
| ((info.binder _ _)::xs) := _
| ((info.operator _)::xs) := _

meta def elim_equality (l : list info) : conv unit := do
b.apply_congr (λe, reorder_equality l),
_


meta def reorder_non_dependent1 : list info → conv (list info)
| [] := failed
| xs@((info.binder _ ff) :: _) := return xs
| ((info.binder _ tt) :: xs) := do
  xs ← b.apply_congr (λe, reorder_non_dependent1 xs),
  b.apply_comm,
  return xs
| ((info.operator s) :: xs) := do
  xs ← b.apply_op_congr s (reorder_non_dependent1 xs),
  b.apply_op_comm s,
  return xs

meta def reorder_non_dependent : list info → conv unit | l := do
l' ← b.apply_congr (λe, reorder_non_dependent1 l) | elim_equality l,
b.apply_comm,
b.apply_congr (λe, reorder_non_dependent l')

meta def run : expr → tactic unit
| `(@Exists %%α %%p) := do
  (lam pp_n bi domain body) ← return p,
  v ← mk_local' pp_n bi domain,
  let t := body.instantiate_var v,
  ps ← find v [v] t,
  _
| _ := skip

end
end exists_eq_elim



#exit

meta structure binder_eq_elim :=
(analyse_head : expr → tactic (expr × expr × expr × expr))
(analyse : expr → tactic (list (expr × list expr × expr × expr)))

/- `(t, v, x, t') ∈ analyse_head e` splits e s.t. e = t[x := λv. t'] -/
/- `(t, vs, x, t') ∈ analyse e` splits e s.t. e = t[x := λvs. t'] -/

namespace binder_eq_elim

protected meta def check_eq (b : binder_eq_elim) (x : expr) : expr → bool
| `(%%l = %%r) := ((l = x ∧ ¬ x.occurs r) ∨ (r = x ∧ ¬ x.occurs l))
| _ := ff

protected meta def eliminate (b : binder_eq_elim) (v : expr) :
  expr → list (expr × list expr × expr × expr) → tactic expr :=
_


protected meta def find (b : binder_eq_elim) (x : expr) :
  expr → tactic (list $ list $ expr × list expr × expr × expr) | e := do
ps ← b.analyse e,
ps' ← ps.mmap (λd, do
  ⟨t, vs, v, t'⟩ ← return d,
  if vs.any (b.check_eq x) ∨ b.check_eq x t' then
    return []
  else do
    ps' ← find t',
    return $ ps'.map (λl, d :: l)),
return ps'.join

protected meta def run (b : binder_eq_elim) (e : expr) : tactic expr := do
(t, v, x, t') ← b.analyse_head e,
ps ← b.find v t',
ps.mfirst (b.eliminate v t')

end binder_eq_elim


#exit


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

section exists_eq_elim

theorem exists_and_distrib_left {α : Sort*} (p : α → Prop) (q : Prop) :
  (∃a, p a ∧ q) ↔ (∃a, p a) ∧ q :=
⟨λ⟨a, hp, hq⟩, ⟨⟨a, hp⟩, hq⟩, λ ⟨⟨a, hp⟩, hq⟩, ⟨a, hp, hq⟩⟩

theorem exists_and_distrib_right {α : Sort*} (p : α → Prop) (q : Prop) :
  (∃a, q ∧ p a) ↔ q ∧ (∃a, p a) :=
⟨λ⟨a, hq, hp⟩, ⟨hq, ⟨a, hp⟩⟩, λ ⟨hq, ⟨a, hp⟩⟩, ⟨a, hq, hp⟩⟩

theorem exists_comm {α : Sort*} {β : Sort*} (p : α → β → Prop) :
  (∃a b, p a b) ↔ (∃b a, p a b) :=
⟨λ⟨a, ⟨b, h⟩⟩, ⟨b, ⟨a, h⟩⟩, λ⟨a, ⟨b, h⟩⟩, ⟨b, ⟨a, h⟩⟩⟩

theorem exists_elim_eq_left {α : Sort*} (a : α) (p : Π(a':α), a' = a → Prop) :
  (∃(a':α) (h : a' = a), p a' h) ↔ p a rfl :=
⟨λ⟨a', ⟨h, p_h⟩⟩, match a', h, p_h with ._, rfl, h := h end, λh, ⟨a, rfl, h⟩⟩

theorem exists_elim_eq_right {α : Sort*} (a : α) (p : Π(a':α), a = a' → Prop) :
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

theorem forall_comm {α : Sort*} {β : Sort*} (p : α → β → Prop) :
  (∀a b, p a b) ↔ (∀b a, p a b) :=
⟨assume h b a, h a b, assume h b a, h a b⟩

theorem forall_elim_eq_left {α : Sort*} (a : α) (p : Π(a':α), a' = a → Prop) :
  (∀(a':α)(h : a' = a), p a' h) ↔ p a rfl :=
⟨λh, h a rfl, λh a' h_eq, match a', h_eq with ._, rfl := h end⟩

theorem forall_elim_eq_right {α : Sort*} (a : α) (p : Π(a':α), a = a' → Prop) :
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

variables {α : Type*} {β : Type*} {ι : Sort*} {ι₂ : Sort*} {a : α} {γ : β → Type*} {δ : α → Type*}
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

example {f : α → β} {q : β → α → Prop} :
  (∃b, ∃a, ∃h:q b a, ∃h' : b = b, ∃h : f a = b, ∃c:γ b, p b) ↔ _ :=
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
