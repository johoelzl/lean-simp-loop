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
import simp_loop.conv

def monotone {α : Sort*} (r : α → α → Prop) (p : α → Prop) : Prop :=
∀x y, r x y → p x → p y

lemma monotone_eq {α : Type*} (p : α → Prop) : monotone (=) p :=
assume x y h, h ▸ id

-- do we/want need a dependent version?
lemma exists_elim_rel {α : Sort*} {r : α → α → Prop} {p : α → Prop} {a : α} [is_refl α r]
  (h : monotone r p) :
  (∃x, r x a ∧ p x) ↔ p a :=
⟨assume ⟨x, hxa, hx⟩, h x a hxa hx, assume ha, ⟨a, is_refl.refl r a, ha⟩⟩

lemma ex_extend {α : Type*} {p : α → Prop} : (∃a, p a) ↔ (∃a, p a ∧ true) :=
⟨assume ⟨a, ha⟩, ⟨a, ha, ⟨⟩⟩, assume ⟨a, ha, ⟨⟩⟩, ⟨a, ha⟩⟩

lemma l_eq {p E : Prop} : (p ∧ E) ↔ (E ∧ p) :=
and_comm _ _
lemma l_ex {p E : Prop} {r : E → Prop} : (p ∧ (∃h:E, r h)) ↔ (∃h:E, p ∧ r h) :=
⟨λ⟨h, e, r⟩, ⟨e, h, r⟩, λ⟨e, h, r⟩, ⟨h, e, r⟩⟩
lemma l_cn {p q E : Prop} : (p ∧ (E ∧ q)) ↔ (E ∧ (p ∧ q)) :=
⟨λ⟨h, e, r⟩, ⟨e, h, r⟩, λ⟨e, h, r⟩, ⟨h, e, r⟩⟩
lemma r_eq {p E : Prop} : (E ∧ p) ↔ (E ∧ p) :=
iff.refl _
lemma r_ex {p E : Prop} {r : E → Prop} : ((∃h:E, r h) ∧ p) ↔ (∃h:E, r h ∧ p) :=
⟨λ⟨⟨e, r⟩, h⟩, ⟨e, r, h⟩, λ⟨e, r, h⟩, ⟨⟨e, r⟩, h⟩⟩
lemma r_cn {p q E : Prop} : ((E ∧ q) ∧ p) ↔ (E ∧ (q ∧ p)) :=
⟨λ⟨⟨e, r⟩, h⟩, ⟨e, r, h⟩, λ⟨e, r, h⟩, ⟨⟨e, r⟩, h⟩⟩
lemma e_eq_Prop {p E : Prop} : (∃a:p, E) ↔ (E ∧ p) :=
⟨λ⟨a, h⟩, ⟨h, a⟩, λ⟨h, a⟩, ⟨a, h⟩⟩
lemma e_eq {α : Sort*} {E : Prop} : (∃a:α, E) ↔ (E ∧ ∃a:α, true) :=
⟨λ⟨a, h⟩, ⟨h, ⟨a, ⟨⟩⟩⟩, λ⟨h, ⟨a, _⟩⟩, ⟨a, h⟩⟩
lemma e_ex {α : Sort*} {E : Prop} {s : E → α → Prop} : (∃a:α, ∃h:E, s h a) ↔ (∃h:E, ∃a:α, s h a) :=
⟨λ⟨a, h, t⟩, ⟨h, a, t⟩, λ⟨a, h, t⟩, ⟨h, a, t⟩⟩
lemma e_cn {α : Sort*} {E : Prop} {t : α → Prop} : (∃a:α, E ∧ t a) ↔ (E ∧ (∃a:α, t a)) :=
⟨λ⟨a, e, t⟩, ⟨e, ⟨a, t⟩⟩, λ⟨e, ⟨a, t⟩⟩, ⟨a, e, t⟩⟩

lemma l_congr {p q r : Prop} (h : q ↔ r) : p ∧ q ↔ p ∧ r :=
and_congr (iff.refl p) h
lemma r_congr {p q r : Prop} (h : q ↔ r) : q ∧ p ↔ r ∧ p :=
and_congr h (iff.refl p)
lemma ex_congr {α : Sort*} {p q : α → Prop} (h : ∀a, p a ↔ q a) : (∃a, p a) ↔ (∃a, q a) :=
exists_congr h

lemma comm_l {α : Sort*} {p : Prop} {q : α → Prop} : p ∧ (∃a, q a) ↔ ∃a, p ∧ q a :=
⟨λ⟨a, hq, hp⟩, ⟨hq, ⟨a, hp⟩⟩, λ ⟨hq, ⟨a, hp⟩⟩, ⟨a, hq, hp⟩⟩
lemma comm_r {α : Sort*} {p : Prop} {q : α → Prop} : (∃a, q a) ∧ p ↔ ∃a, q a ∧ p :=
⟨λ ⟨⟨a, hp⟩, hq⟩, ⟨a, hp, hq⟩, λ⟨a, hp, hq⟩, ⟨⟨a, hp⟩, hq⟩⟩
lemma comm_ex {α : Sort*} {β : Sort*} {p : α → β → Prop} : (∃a b, p a b) ↔ (∃b a, p a b) :=
⟨λ⟨a, ⟨b, h⟩⟩, ⟨b, ⟨a, h⟩⟩, λ⟨a, ⟨b, h⟩⟩, ⟨b, ⟨a, h⟩⟩⟩

namespace simp_loop
open conv_t tactic expr

meta inductive info
| binder (v : expr) (dependent : bool) | operator (side : bool)

namespace info
open format
meta instance : has_to_format info :=
⟨λi, match i with
| info.binder v d := to_fmt "binder " ++ to_fmt v ++ " " ++ to_fmt d
| info.operator s := to_fmt "operator " ++ to_fmt s
end⟩
end info

meta inductive norm_form
| eq | ex | cn

namespace norm_form
open format
meta instance : has_to_format norm_form :=
⟨λi, match i with
| norm_form.eq := to_fmt "eq"
| norm_form.ex := to_fmt "ex"
| norm_form.cn := to_fmt "cn"
end⟩
end norm_form

meta def congr_ex {α} (c : conv α) : conv α := congr_binder ``ex_congr (λ_, c)

meta def congr {α} (c : conv α) : info → conv α
| (info.binder _ _) := congr_ex c
| (info.operator tt) := congr_simple ``r_congr c
| (info.operator ff) := congr_simple ``l_congr c

meta def apply_norm (n_eq n_ex n_cn : list name) : norm_form → conv norm_form
| norm_form.eq := do n_eq.mfirst apply_const, return norm_form.cn
| norm_form.ex := do n_ex.mfirst apply_const, return norm_form.ex
| norm_form.cn := do n_cn.mfirst apply_const, return norm_form.cn

meta def analyse (chk : expr → list expr → expr → bool)
  (v : expr) (deps : list expr) : expr → tactic (option $ list $ info × expr)
| `(@Exists %%α %%p) := if chk v deps α then
    return none
  else do
    (lam pp_n bi domain body) ← return p | return (some []),
    x ← mk_local' pp_n bi domain,
    return [(info.binder x (deps.any $ λv, v.occurs α), body.instantiate_var x)]
| `(%%p ∧ %%q) := return [(info.operator tt, p), (info.operator ff, q)]
| t := return $ if chk v deps t then none else some []

meta def find (chk : expr → list expr → expr → bool)
  (v : expr) : list expr → expr → tactic (list $ list info) | deps e := do
some is ← analyse chk v deps e | return [[]],
iss ← is.mmap (λ⟨i, t⟩, do
  deps ← return $ match i with (info.binder v tt) := v :: deps | _ := deps end,
  iss ← find deps t,
  return $ iss.map $ λis, i :: is),
return iss.join

section reorder

private meta def reorder_dependent : list info → conv norm_form
| [] := (do -- trace "reorder_equality []", trace_lhs,
  `(_ = _) ← lhs, return norm_form.eq) <|> return norm_form.ex
| (i::xs)  := do
  n ← congr (reorder_dependent xs) i,
  match i with
  | info.binder _ _  := apply_norm [``e_eq_Prop, ``e_eq] [``e_ex] [``e_cn] n
  | info.operator tt := apply_norm [``r_eq] [``r_ex] [``r_cn] n
  | info.operator ff := apply_norm [``l_eq] [``l_ex] [``l_cn] n
  end

private meta def reorder_non_dependent : list info → conv (option (list info))
| []      := return none
| (i::is) := (do info.binder _ ff ← return i, return is) <|> (do
  some is' ← congr (reorder_non_dependent is) i | return none,
  r ← return $ match i with
  | info.binder _ _  := ``comm_ex
  | info.operator tt := ``comm_r
  | info.operator ff := ``comm_l
  end,
  apply_const r,
  return (i :: is'))

meta def reorder {α} (elim : norm_form → conv α) : list info → conv α | l := do
-- trace (to_fmt "reorder_and_elim " ++ to_fmt l),
some l' ← congr_ex (reorder_non_dependent l) |
  (congr_ex (reorder_dependent l) >>= elim),
apply_const ``comm_ex,
congr_ex (reorder l')

end reorder

section equality_elim

meta def check_eq (x : expr) (deps : list expr) : expr → bool
| `(%%l = %%r) := (l = x ∧ deps.all (λx, ¬ x.occurs r)) ∨ (r = x ∧ deps.all (λx, ¬ x.occurs l))
| _ := ff

meta def elim_equality (n : norm_form) : conv unit := do
-- trace (to_fmt "elim_equality [reordered] " ++ to_fmt n), trace_lhs,
apply_norm [``elim_eq_left, ``elim_eq_right] [``elim_ex_left, ``elim_ex_right] [``elim_cn_left, ``elim_cn_right] n,
skip

meta def run : conv unit := do
pss ← congr_binder ``ex_congr (λv, do t ← lhs, find check_eq v [v] t),
pss.mfirst (reorder elim_equality)

end equality_elim

end simp_loop