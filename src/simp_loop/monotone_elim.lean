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

inductive bintree (α : Type*)
| leaf (a : α) : bintree
| node (l r : bintree) : bintree

def list.dedup {α : Type*} [decidable_eq α] : list α → list α
| []        := []
| (x :: xs) := (if x ∈ xs then xs.dedup else x :: xs.dedup)

namespace bintree
variables {α : Type*} {β : Type*}

def pos := list bool

def left : bintree α → bintree α
| (leaf a)   := leaf a
| (node l r) := l

def right : bintree α → bintree α
| (leaf a)   := leaf a
| (node l r) := r

def at_pos : pos → bintree α → bintree α
| []        t := t
| (ff :: p) t := at_pos p (left t)
| (tt :: p) t := at_pos p (right t)

def map (f : α → β) : bintree α → bintree β
| (leaf a) := leaf (f a)
| (node l r) := node (map l) (map r)

def mmap {m : Type* → Type*} [monad m] (f : α → m β) : bintree α → m (bintree β)
| (leaf a)   := leaf <$> f a
| (node l r) := node <$> mmap l <*> mmap r

end bintree


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

section term_focus

/-

Move a term on one side of a relation using Galois connections:

Symmetric rules:
  f x R y ↔ x Q g z

    ⟹ f x R t ↔ x Q t'
    ⟹ t Q g x ↔ t' R x

Injectivity rules:
  f x R g y ↔ x Q y

    ⟹ f x R t ↔ x Q t'
    ⟹ t R g x ↔ t' Q x

Splitting rules:
  f x R t ↔ (C₁ ∧ x Q₁ t₁) ∨ (C₂ ∧ x Q₂ t₂)

Setup:

* allow symmetric relations
* apply the rules symmetrically
* should we add dischargers for conditional rules, ala:
    0 < R → x / R ≤ S ↔ x ≤ S * R
  or:
    x / R ≤ S ↔ (0 < R ∧ x ≤ S * R) ∨ (R < 0 ∧ S * R ≤ x) ∨ (R = 0 ∧ 0 ≤ S)
    This one doesn't work for monotone elimination as we have x ≤ S * R and S * R ≤ x case.
* conditionals:
    ∀x n i : ℕ, x + n = i ↔ (n ≤ i ∧ x = i - n)
    ∀x n i : ℕ, x - n = i ↔ ((i = 0 ∧ x ≤ n) ∨ x = i + n)
    ∀x n i : ℕ, n - x = i ↔ ((i = 0 ∧ n ≤ x) ∨ (i ≤ n ∧ x = i - n))

-/


meta def connection_iff : user_attribute :=
{ name := `connection_iff,
  descr := "Connection rules of the form f x R y ↔ x Q g z, used for term focusing" }

section analyse

meta def conjs : expr → tactic (list expr)
| `(%%a ∧ %%b) := do
  as ← conjs a,
  bs ← conjs b,
  return (as ++ bs)
| e := return [e]

meta def disjs_of_conjs : expr → tactic (list $ list expr)
| `(%%a ∨ %%b) := do
  as ← disjs_of_conjs a,
  bs ← disjs_of_conjs b,
  return (as ++ bs)
| e := do
  d ← conjs e,
  return [d]

-- better `parse_rel`: this doesn't work with heq!
-- idea: use relation manager
meta def parse_rel : expr → tactic (expr × expr × expr)
| (expr.app (expr.app f a) b) := return (f, a, b)
| _ := fail "term is not a relation application"

def peep {α} : list α → list (list α × α × list α)
| []        := []
| (a :: xs) := ([], a, xs) :: (peep xs).map (λ⟨p, a', s⟩, (a::p, a', s))

private meta def analyse_connection_aux (ls : list level) (vs : list expr) (lhs rhs : expr) :
  tactic $ list pattern := do
disjs ← disjs_of_conjs rhs,
candidates ← disjs.mmap (λconjs, do
  candidates ← (peep conjs).mmap (λxs, (do
    (ps, e, ss) ← return xs,
    (rel, l, r) ← parse_rel e,
    return $
      (if l ∈ vs ∧ (r :: rel :: ps ++ ss).all (λe, ¬ l.occurs e) then [l] else []) ++
      (if r ∈ vs ∧ (l :: rel :: ps ++ ss).all (λe, ¬ r.occurs e) then [r] else []))
      <|> return []),
  return candidates.join),
let candidates := vs.filter $ λv, candidates.all $ λcs, v ∈ cs,

(rel, l, r) ← parse_rel lhs,
let candidates := candidates.filter $ λc,
  ¬ c.occurs rel ∧ ((c.occurs l ∧ ¬ c.occurs r) ∨ c.occurs r ∧ ¬ c.occurs l),
let candidates := candidates.dedup,
let vs' := vs.filter (λv, v.occurs lhs),
candidates.mmap (λc, mk_pattern ls vs' lhs [] [c])

/-- `analyse_connection ls r` a list of symm-flag and pattern. The pattern matches if the rule is
applicable. In this case `tactic.match_pattern` returns one expression where the focused variable
should occur. The symm-flag indicates if the iff-rule should be applied in its symmetric variant. -/
meta def analyse_connection (n : name) : tactic $ list $ bool × pattern := do
e ← get_env,
d ← e.get n,
let ls := d.univ_params.map level.param,
(vs, `(%%lhs ↔ %%rhs)) ← mk_local_pis d.type,
l ← analyse_connection_aux ls vs lhs rhs,
r ← analyse_connection_aux ls vs rhs lhs,
return (l.map (λp, (ff, p)) ++ r.map (λp, (tt, p)))

meta def ors (c : conv unit) : conv unit := do
`(_ ∨ _) ← lhs | c,
congr_core (congr_core skip ors) ors,
skip

meta def ands (c : conv unit) : conv unit := do
`(_ ∧ _) ← lhs | c,
congr_core (congr_core skip ands) ands,
skip

meta def local_eq (v₀ v₁ : expr) : bool :=
v₀.is_local_constant ∧ v₁.is_local_constant ∧ v₀.local_uniq_name = v₁.local_uniq_name

meta def term_focus (l : list (name × bool × pattern)) (v : expr) : conv unit :=
l.mfirst $ assume ⟨n, symm, pat⟩, do
  ([], [t]) ← match_pattern pat,
  guard $ v.occurs t,
  (if symm then apply_const n else fail "symmetric apply not supported yet"),
  ors (ands $ (do
    l ← lhs,
    (_, l, r) ← lift_tactic $ parse_rel l,
    guard ((v.occurs l ∧ ¬ local_eq l v) ∨ (v.occurs r ∧ ¬ local_eq r v)),
    term_focus) <|> skip)

end analyse

/-

Lattices

  x ≤ y ⊓ z ↔ x ≤ y ∧ x ≤ z

  y ⊓ z ≤ x ↔ y \ z ≤ x (Heyting algebra)

  a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c

Case: Focus on a
  (∃ x, x ⊔ b ≤ c ∧ p x) ↔ (∃x, x ≤ c ∧ b ≤ c ∧ p x)

-/


end term_focus

#exit

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