/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.
-/

namespace tactic

meta class monad_tactic (m : Type → Type) :=
(lift_tactic {} {α : Type} : tactic α → m α)

export monad_tactic (lift_tactic)

meta instance : monad_tactic tactic := ⟨λα, id⟩

meta instance monad_tactic_trans {m : Type → Type} {n : Type → Type}
  [has_monad_lift m n] [monad_tactic m] : monad_tactic n :=
⟨λα t, monad_lift (lift_tactic t : m α)⟩

end tactic

open tactic

namespace simp_loop

meta structure conv_result (α : Type) :=
(val : α) (rhs : expr) (proof : option expr)

meta structure conv_t (m : Type → Type) (α : Type) : Type :=
(run : name → expr → m (conv_result α))

attribute [pp_using_anonymous_constructor] conv_t

@[reducible] meta def conv (α : Type) : Type := conv_t tactic α

namespace conv_t

section
parameters {m : Type → Type} [monad m] [monad_tactic m]

meta def lhs : conv_t m expr :=
⟨λ r e, return ⟨e, e, none⟩⟩

meta def rel : conv_t m name :=
⟨λ r e, return ⟨r, e, none⟩⟩

meta def change (new_p : pexpr) : conv_t m unit :=
⟨λ r e, do
  new_e ← lift_tactic (do
    e_type ← infer_type e,
    new_e ← to_expr ``(%%new_p : %%e_type),
    unify e new_e,
    return new_e),
  return ⟨(), new_e, none⟩⟩

protected meta def pure {α : Type} : α → conv_t m α :=
λ a, ⟨λr e, return ⟨a, e, none⟩⟩

private meta def join_proofs (r : name) (o₁ o₂ : option expr) : tactic (option expr) :=
match o₁, o₂ with
| none,    _       := return o₂
| _,       none    := return o₁
| some p₁, some p₂ := do
  env ← get_env,
  match env.trans_for r with
  | some trans := do pr ← mk_app trans [p₁, p₂], return $ some pr
  | none       := fail format!"converter failed, relation '{r}' is not transitive"
  end
end

protected meta def seq {α β : Type} (c₁ : conv_t m (α → β)) (c₂ : conv_t m α) : conv_t m β :=
⟨λ r e, do
  ⟨fn, e₁, pr₁⟩ ← c₁.run r e,
  ⟨a,  e₂, pr₂⟩ ← c₂.run r e₁,
  pr            ← lift_tactic $ join_proofs r pr₁ pr₂,
  return ⟨fn a, e₂, pr⟩⟩

protected meta def map {α β : Type} (f : α → β) (c : conv_t m α) : conv_t m β :=
⟨λ r e, do
  ⟨a, e₁, pr⟩ ← c.run r e,
  return ⟨f a, e₁, pr⟩⟩

protected meta def bind {α β : Type} (c₁ : conv_t m α) (c₂ : α → conv_t m β) : conv_t m β :=
⟨λ r e,
  has_bind.bind (c₁.run r e) (λ⟨a, e₁, pr₁⟩,
  has_bind.bind ((c₂ a).run r e₁) (λ⟨b, e₂, pr₂⟩,
  has_bind.bind (lift_tactic $ join_proofs r pr₁ pr₂) (λpr, return ⟨b, e₂, pr⟩)))⟩
/- do -- fails as it chooses the `conv.bind` as `bind`...
  ⟨a, e₁, pr₁⟩ ← c₁.run r e,
  ⟨b, e₂, pr₂⟩ ← (c₂ a).run r e₁,
  pr           ← lift_tactic $ join_proofs r pr₁ pr₂,
  return ⟨b, e₂, pr⟩
  -/

meta instance : monad_tactic (conv_t m) :=
⟨λα t, ⟨λ r e, do a ← (lift_tactic t : m α), return ⟨a, e, none⟩⟩⟩

meta instance : monad (conv_t m) :=
{ map  := @conv_t.map m _ _,
  pure := @conv_t.pure m _ _,
  bind := @conv_t.bind m _ _ }

/-
protected meta def fail {α β : Type} [has_to_format β] (msg : β) : conv α :=
⟨λ r e, tactic.fail msg⟩

protected meta def failed {α : Type} : conv α :=
⟨λ r e, tactic.failed⟩
protected meta def orelse {α : Type} (c₁ : conv α) (c₂ : conv α) : conv α :=
λ r e, c₁ r e <|> c₂ r e

meta instance : alternative conv :=
{ failure := @conv.failed,
  orelse  := @conv.orelse,
  ..conv.monad }
-/

meta def whnf (md : transparency := reducible) : conv_t m unit :=
⟨λ r e, do n ← (lift_tactic (tactic.whnf e md) : m expr), return ⟨(), n, none⟩⟩

meta def dsimp : conv unit :=
λ r e, do s ← simp_lemmas.mk_default, n ← s.dsimplify [] e, return ⟨(), n, none⟩

meta def try {α} (c : conv α) : conv (option α) :=
(c >>= (return ∘ some)) <|> return none

meta def tryb (c : conv unit) : conv bool :=
(c >> return tt) <|> return ff

meta def trace {α : Type} [has_to_tactic_format α] (a : α) : conv unit :=
λ r e, tactic.trace a >> return ⟨(), e, none⟩

meta def trace_lhs : conv unit :=
lhs >>= trace

meta def apply_lemmas_core (s : simp_lemmas) (prove : tactic unit) : conv unit :=
λ r e, do
  (new_e, pr) ← s.rewrite e prove r,
  return ⟨(), new_e, some pr⟩

meta def apply_lemmas (s : simp_lemmas) : conv unit :=
apply_lemmas_core s failed

/- adapter for using iff-lemmas as eq-lemmas -/
meta def apply_propext_lemmas_core (s : simp_lemmas) (prove : tactic unit) : conv unit :=
λ r e, do
  guard (r = `eq),
  (new_e, pr) ← s.rewrite e prove `iff,
  new_pr ← mk_app `propext [pr],
  return ⟨(), new_e, some new_pr⟩

meta def apply_propext_lemmas (s : simp_lemmas) : conv unit :=
apply_propext_lemmas_core s failed

private meta def mk_refl_proof (r : name) (e : expr) : tactic expr :=
do env ← get_env,
   match (environment.refl_for env r) with
   | (some refl) := do pr ← mk_app refl [e], return pr
   | none        := fail format!"converter failed, relation '{r}' is not reflexive"
   end

meta def to_tactic (c : conv unit) : name → expr → tactic (expr × expr) :=
λ r e, do
  ⟨u, e₁, o⟩ ← c r e,
  match o with
  | none   := do p ← mk_refl_proof r e, return (e₁, p)
  | some p := return (e₁, p)
  end

meta def lift_tactic {α : Type} (t : tactic α) : conv α :=
λ r e, do a ← t, return ⟨a, e, none⟩

meta def apply_simp_set (attr_name : name) : conv unit :=
lift_tactic (get_user_simp_lemmas attr_name) >>= apply_lemmas

meta def apply_propext_simp_set (attr_name : name) : conv unit :=
lift_tactic (get_user_simp_lemmas attr_name) >>= apply_propext_lemmas

meta def skip : conv unit :=
return ()

meta def repeat : conv unit → conv unit
| c r lhs :=
  (do
     ⟨_, rhs₁, pr₁⟩ ← c r lhs,
     guard (¬ lhs =ₐ rhs₁),
     ⟨_, rhs₂, pr₂⟩ ← repeat c r rhs₁,
     pr ← join_proofs r pr₁ pr₂,
     return ⟨(), rhs₂, pr⟩)
  <|> return ⟨(), lhs, none⟩

meta def first {α : Type} : list (conv α) → conv α
| []      := conv.failed
| (c::cs) := c <|> first cs

meta def match_pattern (p : pattern) : conv (list level × list expr) :=
do l ← lhs, lift_tactic $ tactic.match_pattern p l

meta def mk_match_expr (p : pexpr) : tactic (conv unit) :=
do new_p ← pexpr_to_pattern p,
   return (λ r e, tactic.match_pattern new_p e >> return ⟨(), e, none⟩)

meta def match_expr (p : pexpr) : conv unit :=
λ r e, do
  new_p ← pexpr_to_pattern p,
  tactic.match_pattern new_p e >> return ⟨(), e, none⟩

meta def funext {α} (c : expr → conv α) : conv α :=
λ r lhs, do
  guard (r = `eq),
  (expr.lam n bi d b) ← return lhs,
  let aux_type := expr.pi n bi d (expr.const `true []),
  (result, _) ← solve_aux aux_type $ do {
    x ← intro1,
    c_result ← c x r (b.instantiate_var x),
    let rhs  := expr.lam n bi d (c_result.rhs.abstract x),
    match c_result.proof : _ → tactic (conv_result α) with
    | some pr := do
      let aux_pr := expr.lam n bi d (pr.abstract x),
      new_pr ← mk_app `funext [lhs, rhs, aux_pr],
      return ⟨c_result.val, rhs, some new_pr⟩
    | none    := return ⟨c_result.val, rhs, none⟩
    end },
  return result

meta def congr_core {α β} (c_f : conv α) (c_a : conv β) : conv (option α × option β) :=
λ r lhs, do
  guard (r = `eq),
  (expr.app f a) ← return lhs,
  f_type ← infer_type f >>= tactic.whnf,
  guard (f_type.is_arrow),
  ⟨val_f, new_f, of⟩ ← try c_f r f,
  ⟨val_a, new_a, oa⟩ ← try c_a r a,
  rhs ← return $ new_f new_a,
  match of, oa with
  | none, none      :=
      return ⟨(val_f, val_a), rhs, none⟩
  | none, some pr_a := do
      pr ← mk_app `congr_arg [a, new_a, f, pr_a],
      return ⟨(val_f, val_a), new_f new_a, some pr⟩
  | some pr_f, none := do
      pr ← mk_app `congr_fun [f, new_f, pr_f, a],
      return ⟨(val_f, val_a), rhs, some pr⟩
  | some pr_f, some pr_a := do
      pr ← mk_app `congr [f, new_f, a, new_a, pr_f, pr_a],
      return ⟨(val_f, val_a), rhs, some pr⟩
  end

meta def congr {α} (c : conv α) : conv (option α × option α) :=
congr_core c c

meta def bottom_up (c : conv unit) : conv unit :=
λ r e, do
  s ← simp_lemmas.mk_default,
  (a, new_e, pr) ←
     ext_simplify_core () {} s
       (λ u, return u)
       (λ a s r p e, failed)
       (λ a s r p e, do ⟨u, new_e, pr⟩ ← c r e, return ((), new_e, pr, tt))
       r e,
  return ⟨(), new_e, some pr⟩

meta def top_down (c : conv unit) : conv unit :=
λ r e, do
  s ← simp_lemmas.mk_default,
  (a, new_e, pr) ←
     ext_simplify_core () {} s
       (λ u, return u)
       (λ a s r p e, do ⟨u, new_e, pr⟩ ← c r e, return ((), new_e, pr, tt))
       (λ a s r p e, failed)
       r e,
  return ⟨(), new_e, some pr⟩

meta def find (c : conv unit) : conv unit :=
λ r e, do
  s ← simp_lemmas.mk_default,
  (a, new_e, pr) ←
     ext_simplify_core () {} s
       (λ u, return u)
       (λ a s r p e,
         (do ⟨u, new_e, pr⟩ ← c r e, return ((), new_e, pr, ff))
         <|>
         return ((), e, none, tt))
       (λ a s r p e, failed)
       r e,
  return ⟨(), new_e, some pr⟩

meta def find_pattern (pat : pattern) (c : conv unit) : conv unit :=
λ r e, do
  s ← simp_lemmas.mk_default,
  (a, new_e, pr) ←
     ext_simplify_core () {} s
       (λ u, return u)
       (λ a s r p e, do
         matched ← (tactic.match_pattern pat e >> return tt) <|> return ff,
         if matched
         then do ⟨u, new_e, pr⟩ ← c r e, return ((), new_e, pr, ff)
         else return ((), e, none, tt))
       (λ a s r p e, failed)
       r e,
  return ⟨(), new_e, some pr⟩

meta def findp : pexpr → conv unit → conv unit :=
λ p c r e, do
  pat ← pexpr_to_pattern p,
  find_pattern pat c r e

meta def conversion (c : conv unit) : tactic unit :=
do (r, lhs, rhs) ← (target_lhs_rhs <|> fail "conversion failed, target is not of the form 'lhs R rhs'"),
   (new_lhs, pr) ← to_tactic c r lhs,
   (unify new_lhs rhs <|>
     do new_lhs_fmt ← pp new_lhs,
        rhs_fmt     ← pp rhs,
        fail (to_fmt "conversion failed, expected" ++
                     rhs_fmt.indent 4 ++ format.line ++ "provided" ++
                     new_lhs_fmt.indent 4)),
   exact pr

end conv

end simp_loop
