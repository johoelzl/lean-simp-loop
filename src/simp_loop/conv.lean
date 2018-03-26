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

meta def conv_result.mmap_pr {α} (f_r : expr → tactic expr) (f_pr : expr → expr → tactic expr) :
  conv_result α → tactic (conv_result α)
| ⟨a, r, pr⟩ := do
  r' ← f_r r,
  match pr with
  | some pr := do
    pr' ← f_pr r pr,
    return ⟨a, r', pr'⟩
  | none := return ⟨a, r', none⟩
  end

meta structure conv_t (m : Type → Type) (α : Type) : Type :=
(run : name → expr → m (conv_result α))

attribute [pp_using_anonymous_constructor] conv_t

@[reducible] meta def conv (α : Type) : Type := conv_t tactic α

namespace conv_t

section
parameters {m : Type → Type} [monad m] [alternative m] [monad_tactic m]

meta instance : monad_tactic (conv_t m) :=
⟨λα t, ⟨λ r e, do a ← lift_tactic t, return ⟨a, e, none⟩⟩⟩

meta instance {α} : has_coe (tactic α) (conv_t m α) :=
⟨lift_tactic⟩

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

-- do syntax doesn't work if we call it bind
protected meta def bind' {α β : Type} (c₁ : conv_t m α) (c₂ : α → conv_t m β) : conv_t m β :=
⟨λ r e, do
  ⟨a, e₁, pr₁⟩ ← c₁.run r e,
  ⟨b, e₂, pr₂⟩ ← (c₂ a).run r e₁,
  pr           ← lift_tactic $ join_proofs r pr₁ pr₂,
  return ⟨b, e₂, pr⟩⟩

meta instance : monad (conv_t m) :=
{ map  := @conv_t.map m _ _ _,
  pure := @conv_t.pure m _ _ _,
  bind := @conv_t.bind' m _ _ _ }

protected meta def fail {α β : Type} [has_to_format β] (msg : β) : conv_t m α :=
tactic.fail msg

protected meta def failed {α : Type} : conv_t m α :=
tactic.failed

protected meta def orelse {α : Type} (c₁ : conv_t m α) (c₂ : conv_t m α) : conv_t m α :=
⟨λ r e, c₁.run r e <|> c₂.run r e⟩

meta instance : alternative (conv_t m) :=
{ failure := @conv_t.failed _ _ _ _,
  orelse  := @conv_t.orelse _ _ _ _ }

meta def try {α} (c : conv_t m α) : conv_t m (option α) :=
(c >>= (return ∘ some)) <|> return none

meta def tryb (c : conv_t m unit) : conv_t m bool :=
(c >> return tt) <|> return ff

meta def lhs : conv_t m expr :=
⟨λ r e, return ⟨e, e, none⟩⟩

meta def rel : conv_t m name :=
⟨λ r e, return ⟨r, e, none⟩⟩

meta def guard_rel (r : name) : conv_t m unit :=
do r' ← rel, guard $ r = r'

meta def run' {α} (r : name) (e : expr) (c : conv_t m α) : conv_t m (conv_result α) :=
⟨λr' e', do r ← c.run r e, return ⟨r, e', none⟩⟩

meta def change_with (f : expr → tactic expr) : conv_t m unit :=
⟨λ r e, do n ← lift_tactic $ f e, return ⟨(), n, none⟩⟩

meta def change (new_p : pexpr) : conv_t m unit :=
change_with $ λe, do
  e_type ← infer_type e,
  new_e ← to_expr ``(%%new_p : %%e_type),
  unify e new_e,
  return new_e

meta def whnf (md : transparency := reducible) : conv_t m unit :=
change_with $ λe, tactic.whnf e md

meta def dsimp : conv_t m unit :=
change_with $ λe, do s ← simp_lemmas.mk_default, s.dsimplify [] e

meta def trace {α : Type} [has_to_tactic_format α] (a : α) : conv_t m unit :=
tactic.trace a

meta def trace_lhs : conv_t m unit :=
lhs >>= trace

meta def apply_lemmas_core (s : simp_lemmas) (prove : tactic unit) : conv_t m unit :=
⟨λ r e, do
  (new_e, pr) ← lift_tactic $ s.rewrite e prove r,
  return ⟨(), new_e, some pr⟩⟩

meta def apply_lemmas (s : simp_lemmas) : conv_t m unit :=
apply_lemmas_core s tactic.failed

meta def propext {α} (c : conv_t m α) : conv_t m α :=
⟨λr lhs, do
  guard (r = `eq),
  r ← c.run `iff lhs,
  lift_tactic $ r.mmap_pr return $ λrhs pr, mk_app `propext [pr]⟩

/- adapter for using iff-lemmas as eq-lemmas -/
meta def apply_propext_lemmas_core (s : simp_lemmas) (prove : tactic unit) : conv_t m unit :=
propext (apply_lemmas_core s prove)

meta def apply_propext_lemmas (s : simp_lemmas) : conv_t m unit :=
apply_propext_lemmas_core s tactic.failed

private meta def mk_refl_proof (r : name) (e : expr) : tactic expr :=
do env ← get_env,
   match (environment.refl_for env r) with
   | (some refl) := do pr ← mk_app refl [e], return pr
   | none        := tactic.fail format!"converter failed, relation '{r}' is not reflexive"
   end

meta def to_tactic (c : conv unit) : name → expr → tactic (expr × expr) :=
λ r e, do
  ⟨u, e₁, o⟩ ← c.run r e,
  match o with
  | none   := do p ← mk_refl_proof r e, return (e₁, p)
  | some p := return (e₁, p)
  end

meta def apply_simp_set (attr_name : name) : conv_t m unit :=
get_user_simp_lemmas attr_name >>= apply_lemmas

meta def apply_propext_simp_set (attr_name : name) : conv_t m unit :=
get_user_simp_lemmas attr_name >>= apply_propext_lemmas

meta def skip : conv_t m unit :=
return ()

meta def repeat (c : conv_t m unit) : conv_t m unit := do
  old ← lhs,
  c,
  new ← lhs,
  (if old =ₐ new then skip else repeat)

meta def first {α : Type} : list (conv_t m α) → conv_t m α
| []      := failed
| (c::cs) := c <|> first cs

meta def match_pattern (p : pattern) : conv_t m (list level × list expr) :=
do l ← lhs, tactic.match_pattern p l

meta def mk_match_expr (p : pexpr) : tactic (conv_t m unit) :=
(λe, match_pattern e >> skip) <$> pexpr_to_pattern p

meta def match_expr (p : pexpr) : conv_t m unit := do
  new_p ← pexpr_to_pattern p,
  match_pattern new_p,
  skip

meta def funext {α} (c : expr → conv_t m α) : conv_t m α :=
⟨λr lhs, do
  guard (r = `eq),
  (expr.lam n bi d b) ← lift_tactic $ tactic.whnf lhs | lift_tactic $ failure,
  n' ← lift_tactic $ mk_fresh_name,
  let v := expr.local_const n' n bi d,
  r ← (c v).run r lhs,
  lift_tactic $ r.mmap_pr
    (λr, return $ expr.lam n bi d (r.abstract v))
    (λr pr, lift_tactic $ mk_app
      `funext [lhs, expr.lam n bi d (r.abstract v), expr.lam n bi d (pr.abstract v)])⟩

meta def congr_core {α β} (c_f : conv_t m α) (c_a : conv_t m β) : conv_t m (α × β) := do
  guard_rel `eq,
  (expr.app f a) ← lhs | failure,
  f_type ← lift_tactic (infer_type f >>= tactic.whnf),
  guard (f_type.is_arrow),
  ⟨λ r lhs, do
    ⟨val_f, new_f, of⟩ ← c_f.run r f,
    ⟨val_a, new_a, oa⟩ ← c_a.run r a,
    let rhs := new_f new_a,
    match of, oa with
    | none, none      :=
        return ⟨(val_f, val_a), rhs, none⟩
    | none, some pr_a := do
        pr ← lift_tactic $ mk_app `congr_arg [a, new_a, f, pr_a],
        return ⟨(val_f, val_a), rhs, some pr⟩
    | some pr_f, none := do
        pr ← lift_tactic $ mk_app `congr_fun [f, new_f, pr_f, a],
        return ⟨(val_f, val_a), rhs, some pr⟩
    | some pr_f, some pr_a := do
        pr ← lift_tactic $ mk_app `congr [f, new_f, a, new_a, pr_f, pr_a],
        return ⟨(val_f, val_a), rhs, some pr⟩
    end⟩

meta def congr (c : conv_t m unit) : conv_t m unit :=
congr_core c c >> skip

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

end

end conv_t

meta def conversion (c : conv unit) : tactic unit :=
do (r, lhs, rhs) ← (target_lhs_rhs <|> fail "conversion failed, target is not of the form 'lhs R rhs'"),
   (new_lhs, pr) ← conv_t.to_tactic c r lhs,
   (unify new_lhs rhs <|>
     do new_lhs_fmt ← pp new_lhs,
        rhs_fmt     ← pp rhs,
        fail (to_fmt "conversion failed, expected" ++
                     rhs_fmt.indent 4 ++ format.line ++ "provided" ++
                     new_lhs_fmt.indent 4)),
   exact pr

end simp_loop
