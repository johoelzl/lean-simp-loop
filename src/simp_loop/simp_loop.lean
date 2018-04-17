/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Simplifier loop with additional simplification procedures (i.e. Isabelle's simpprocs).
-/

open tactic

/- Ideas to implement:

* binder elimination: (∃x, t = x ∧ p x) ↔ p t
  - support ⨆, ⨅, ∑, …
  - add focus variable: (∃x, t = x + 1 ∧ p x) ↔ (∃x, t - 1 = x ∧ p x)
  - add monotonicity: mono p → (∃x, x ≤ t ∧ p x) ↔ p t
  - use Galois connection for focusing: f x ≤ t ↔ t ≤ g x

* if / match distributivity: C (if p then a else b) = if p then C a else C b
  - how to handle the dependent case?
  - the context C should not contain binder appearing in p, a, and b.
  - take care of iterated ifs: if p then (if q then a else b) else c

The following may be interesting until there is a algebraic normalizer in Lean
* cancellation:
  - in an expression: + x - y - x = - y
  - in an (in)equality: a + b = b + c → a = c

* basic linear arithmetic?

-/

namespace simp_loop

meta def proc_attr : user_attribute :=
{ name := `simp_loop.proc,
  descr := "Simplification procedures for the simp loop." }

protected meta def loop (p : list $ tactic unit) (s : simp_lemmas) (to_unfold : list name)
  (cfg : simp_config) (dcfg : dsimp_config) : tactic unit := do
t₀ ← target,
simp_target s to_unfold cfg,
dsimp_target s to_unfold dcfg,
p.mmap' id,
t₁ ← target,
if t₀ =ₐ t₁ then skip else loop

meta def main : tactic unit := do
_ -- prepare simp lemmas, to_unfold data, configuration, discharger

end simp_loop