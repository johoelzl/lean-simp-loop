/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

1-point elimination for ∃.

This implements a conversion transforming
  `∃x, t[x, x = a] ~> t[a, rfl]`
where `t` is an expression consiting of existentials and conjunctions, and the equality is either
the type of one of the existentials or in one of the conjunctions.

Concrete examples:
  `∃a, a = t ∧ p a                     ~>   p t`
  `∃a, p a ∧ ∃b, ∃h : a = f b, q a h   ~>   ∃b, p (f b) ∧ q (f b) rfl`

This is implemented by
* `find`: find all possible equalities, and keep track of dependencies on `x`
* `reorder_non_dependent`: move all existentials which are not dependent on `x` before the first one
* `elim_equality`: walk to the equality and bring it in the normal form
    eq : E
    ex : ∃h:E, q
    cn : E ∧ q
  end finally eliminated it.

To bring it into normal form we need to keep care of the following cases:
  l : p ∧ X
  r : X ∧ p
  e : ∃a, X
applying these rules:
  l_eq : p ∧ E            ~>  E ∧ p
  l_ex : p ∧ (∃h:E, q h)  ~>  ∃h:E, p ∧ q h
  l_cn : p ∧ (E ∧ q)      ~>  E ∧ (p ∧ q)
  r_eq : E ∧ p            ~>  E ∧ p
  r_ex : (∃h:E, q h) ∧ p  ~>  ∃h:E, q h ∧ p
  r_cn : (E ∧ q) ∧ p      ~>  E ∧ (q ∧ p)
  e_eq_Prop : ∃a, E       ~>  E ∧ a
  e_eq : ∃a, E            ~>  E ∧ nonempty a
  e_ex : ∃a, ∃h:E, q h a  ~>  ∃h:E, ∃a, q h a
  e_cn : ∃a, E ∧ p a      ~>  E ∧ (∃a, p a)

And finally for elimination:
  elim_eq : ∃x, x = t           ~>  true
  elim_ex : ∃x, ∃h:x = t, p x h ~>  p t rfl
  elim_cn : ∃x, (x = t) ∧ p x   ~>  p t

This tactic is inspired by the one-point elimination in Isabelle's simplifier.
-/
import simp_loop.conv

namespace simp_loop
open conv_t tactic expr

namespace exists_eq_elim

section

section
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
lemma e_eq {α : Sort*} {E : Prop} : (∃a:α, E) ↔ (E ∧ nonempty α) :=
⟨λ⟨a, h⟩, ⟨h, ⟨a⟩⟩, λ⟨h, ⟨a⟩⟩, ⟨a, h⟩⟩
lemma e_ex {α : Sort*} {E : Prop} {s : E → α → Prop} : (∃a:α, ∃h:E, s h a) ↔ (∃h:E, ∃a:α, s h a) :=
⟨λ⟨a, h, t⟩, ⟨h, a, t⟩, λ⟨a, h, t⟩, ⟨h, a, t⟩⟩
lemma e_cn {α : Sort*} {E : Prop} {t : α → Prop} : (∃a:α, E ∧ t a) ↔ (E ∧ (∃a:α, t a)) :=
⟨λ⟨a, e, t⟩, ⟨e, ⟨a, t⟩⟩, λ⟨e, ⟨a, t⟩⟩, ⟨a, e, t⟩⟩

lemma elim_eq_left {α : Sort*} {a : α} : (∃x, x = a) ↔ true :=
⟨λ_, ⟨⟩, λ_, ⟨a, rfl⟩⟩
lemma elim_eq_right {α : Sort*} {a : α} : (∃x, a = x) ↔ true :=
⟨λ_, ⟨⟩, λ_, ⟨a, rfl⟩⟩
lemma elim_ex_left {α : Sort*} {a : α} {q : Πx, x = a → Prop} : (∃x, ∃h:x = a, q x h) ↔ q a rfl :=
⟨λ⟨x, rfl, q⟩, q, λh, ⟨a, rfl, h⟩⟩
lemma elim_ex_right {α : Sort*} {a : α} {q : Πx, a = x → Prop} : (∃x, ∃h:a = x, q x h) ↔ q a rfl :=
⟨λ⟨x, rfl, q⟩, q, λh, ⟨a, rfl, h⟩⟩
lemma elim_cn_left {α : Sort*} {a : α} {p : α → Prop} : (∃x, (x = a) ∧ p x) ↔ p a :=
⟨λ⟨x, rfl, p⟩, p, λh, ⟨a, rfl, h⟩⟩
lemma elim_cn_right {α : Sort*} {a : α} {p : α → Prop} : (∃x, (a = x) ∧ p x) ↔ p a :=
⟨λ⟨x, rfl, p⟩, p, λh, ⟨a, rfl, h⟩⟩

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

end

end

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

meta def check_eq (x : expr) (deps : list expr) : expr → bool
| `(%%l = %%r) := (l = x ∧ deps.all (λx, ¬ x.occurs r)) ∨ (r = x ∧ deps.all (λx, ¬ x.occurs l))
| _ := ff

meta def congr_ex {α} (c : conv α) : conv α := congr_binder ``ex_congr (λ_, c)

meta def congr {α} (c : conv α) : info → conv α
| (info.binder _ _) := congr_ex c
| (info.operator tt) := congr_simple ``r_congr c
| (info.operator ff) := congr_simple ``l_congr c

meta def apply_norm (n_eq n_ex n_cn : list name) : norm_form → conv norm_form
| norm_form.eq := do n_eq.mfirst apply_const, return norm_form.cn
| norm_form.ex := do n_ex.mfirst apply_const, return norm_form.ex
| norm_form.cn := do n_cn.mfirst apply_const, return norm_form.cn

meta def analyse (v : expr) (deps : list expr) : expr → tactic (option $ list $ info × expr)
| `(@Exists %%α %%p) := if check_eq v deps α then
    return none
  else do
    (lam pp_n bi domain body) ← return p | return (some []),
    x ← mk_local' pp_n bi domain,
    return [(info.binder x (deps.any $ λv, v.occurs α), body.instantiate_var x)]
| `(%%p ∧ %%q) := return [(info.operator tt, p), (info.operator ff, q)]
| t := return $ if check_eq v deps t then none else some []

meta def find (v : expr) : list expr → expr → tactic (list $ list info) | deps e := do
some is ← analyse v deps e | return [[]],
iss ← is.mmap (λ⟨i, t⟩, do
  deps ← return $ match i with (info.binder v tt) := v :: deps | _ := deps end,
  iss ← find deps t,
  return $ iss.map $ λis, i :: is),
return iss.join

meta def reorder_equality : list info → conv norm_form
| [] := (do -- trace "reorder_equality []", trace_lhs,
  `(_ = _) ← lhs, return norm_form.eq) <|> return norm_form.ex
| (i@(info.binder _ _)::xs)  := congr (reorder_equality xs) i >>= apply_norm [``e_eq_Prop, ``e_eq] [``e_ex] [``e_cn]
| (i@(info.operator tt)::xs) := congr (reorder_equality xs) i >>= apply_norm [``r_eq] [``r_ex] [``r_cn]
| (i@(info.operator ff)::xs) := congr (reorder_equality xs) i >>= apply_norm [``l_eq] [``l_ex] [``l_cn]

meta def elim_equality (l : list info) : conv unit := do
-- trace (to_fmt "elim_equality " ++ to_fmt l),
n ← congr_ex (reorder_equality l),
-- trace (to_fmt "elim_equality [reordered] " ++ to_fmt n), trace_lhs,
apply_norm [``elim_eq_left, ``elim_eq_right] [``elim_ex_left, ``elim_ex_right] [``elim_cn_left, ``elim_cn_right] n,
skip

meta def reorder_non_dependent : list info → conv (option (list info))
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

meta def reorder_and_elim : list info → conv unit | l := do
-- trace (to_fmt "reorder_and_elim " ++ to_fmt l),
some l' ← congr_ex (reorder_non_dependent l) | elim_equality l,
apply_const ``comm_ex,
congr_ex (reorder_and_elim l')

meta def run : conv unit := do
pss ← congr_binder ``ex_congr (λv, do t ← lhs, find v [v] t),
pss.mfirst reorder_and_elim

section test

variables {α : Sort*} {β : Sort*} {γ : β → Sort*} {δ : α → Sort*}

example {f : α → β} {a : α} {p : β → Prop} :
  (∃b, ∃c:γ b, ∃h : f a = b, p b) ↔ (∃c:γ (f a), p (f a)) :=
by conversion exists_eq_elim.run

example {f : α → β} {p : β → Prop} :
  (∃b, ∃c:γ b, ∃a, ∃h : f a = b, p b) ↔ (∃a, ∃c:γ (f a), p (f a)) :=
by conversion exists_eq_elim.run

example {f : Πa, δ a → β} {p : β → Prop} :
  (∃b, ∃c:γ b, ∃a, ∃d:δ a, ∃h : f a d = b, p b) ↔ (∃a, ∃d:δ a, ∃c:γ (f a d), p (f a d)) :=
by conversion exists_eq_elim.run

example {f : Πa, δ a → β} {p : β → Prop} :
  (∃b, ∃a, ∃c:γ b, ∃d:δ a, ∃h : f a d = b, p b) ↔ (∃a, ∃d:δ a, ∃c:γ (f a d), p (f a d)) :=
by conversion exists_eq_elim.run

example {f : Πa, δ a → β} {p : β → Prop} :
  (∃b, ∃a, ∃d:δ a, ∃c:γ b, ∃h : f a d = b, p b) ↔ (∃a, ∃d:δ a, ∃c:γ (f a d), p (f a d)) :=
by conversion exists_eq_elim.run

example {f : Πa, δ a → β} {p : β → Prop} :
  (∃b, ∃a, ∃d:δ a, ∃h : f a d = b, ∃c:γ b, p b) ↔ (∃a, ∃d:δ a, ∃c:γ (f a d), p (f a d)) :=
by conversion exists_eq_elim.run

example {f : Πa, δ a → β} {p : β → Prop} :
  (∃b, ∃a, ∃d:δ a, ∃h' : a = a ∧ b = b, ∃h : f a d = b, ∃c:γ b, p b) ↔
    (∃a (d : δ a) (h' : a = a ∧ f a d = f a d) (c : γ (f a d)), p (f a d)) :=
by conversion exists_eq_elim.run

example {f : α → β} {q : β → α → Prop} {p : β → Prop} :
  (∃b a, ∃h:q b a, ∃h' : b = b, ∃h : f a = b, ∃c:γ b, p b) ↔
    (∃a (h : q (f a) a) (h : f a = f a) (c : γ (f a)), p (f a)) :=
by conversion exists_eq_elim.run

example {f : α → β} {p : β → Prop} :
  (∃a, (∃c, ∃h: a = a , ∃b : β, a = f c) ∧ (∃c:α, p a)) ↔
    (∃a (b:β), f a = f a ∧ ∃ (c : α), p (f a))  :=
by conversion exists_eq_elim.run

example {f : α → β} {p : β → Prop} :
  (∃a, (∃c, ∃h: a = a , ∃b : β, a = f c) ∧ (∃c:α, p a)) ↔
    (∃a (b:β), f a = f a ∧ ∃ (c : α), p (f a))  :=
by conversion exists_eq_elim.run

example {f g : α → β} {p : α → Prop} :
  (∃b, ∃a:(λb:β, α) b, ∃a₂, ∃h:f a = b, b = g a₂ ∧ p a₂) ↔
    (∃a₂ (a : (λ (b : β), α) (g a₂)) (h : f a = g a₂), p a₂)  :=
by conversion exists_eq_elim.run

example {p q r : α → Prop} {a : α}:
  (∃a', (p a' ∧ r a') ∧ (a = a' ∧ q a)) ↔ (p a ∧ r a) ∧ q a :=
by conversion exists_eq_elim.run

example {p q r : α → Prop} {a : α} :
  (∃a', (p a' ∧ r a') ∧ (a' = a ∧ q a)) ↔ (p a ∧ r a) ∧ q a :=
by conversion exists_eq_elim.run

example {p : α → Prop} {q : Prop} :
  (∃a, p a ∧ ∃a', a = a' ∧ q) ↔ (∃a, p a ∧ q) :=
by conversion exists_eq_elim.run

end test

end exists_eq_elim
end simp_loop
