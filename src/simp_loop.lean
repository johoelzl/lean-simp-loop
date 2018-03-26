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

* cancellation:
  - in an expression: + x - y - x = - y
  - in an (in)equality: a + b = b + c → a = c

* if / match distributivity: C (if p then a else b) = if p then C a else C b
  - how to handle the dependent case?
  - the context C should not contain binder appearing in p, a, and b.
  - take care of iterated ifs: if p then (if q then a else b) else c

* basic linear arithmetic?

-/

