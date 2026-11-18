/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathias Stout
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Algebraic.Integral
/-! # Polynomials vanishing at elements of field extensions

Generic lemmas about the polynomials over a base field `F` that vanish at an element of an
`F`-algebra; nothing in this file mentions model theory. The model-theoretic content, used for
quantifier elimination in algebraically closed fields (`Algebra/ACF/QE.lean`), is that an element
`b : K` and an element `c : L` satisfy the same `F`-polynomial equations exactly when they are
"of the same kind" over `F`.

* `Polynomial.mem_support_map_of_injective` : an injective ring homomorphism does not change the
  support of a polynomial.
* `IsAlgebraic.exists_aeval_eq_zero_iff` : the **algebraic case** — if `b` is algebraic over
  `F` and `L` is algebraically closed, some `c : L` satisfies exactly the same polynomials
  over `F` as `b`, namely any root of the minimal polynomial of `b`.
* `exists_forall_aeval_ne_zero` : the **finite satisfiability** input for the transcendental
  case — over an infinite field, finitely many nonzero polynomials have a common non-root.
-/

public section

open Polynomial

/-- The membership form of `Polynomial.support_map_of_injective`: an injective ring homomorphism
does not change the support of a polynomial. -/
theorem Polynomial.mem_support_map_of_injective {R S : Type*} [Semiring R] [Semiring S]
    {f : R →+* S} (hf : Function.Injective f) {p : R[X]} {i : ℕ} :
    i ∈ (p.map f).support ↔ i ∈ p.support := by
  rw [support_map_of_injective p hf]

variable {F K L : Type*} [Field F]

/-- **The algebraic case**: if `b` is algebraic over `F` and `L` is an algebraically closed
field extension of `F`, then some `c : L` is annihilated by exactly the same polynomials over
`F` as `b` — any root of the minimal polynomial of `b` will do. -/
theorem IsAlgebraic.exists_aeval_eq_zero_iff [Field K] [Field L] [Algebra F K] [Algebra F L]
    [IsAlgClosed L] {b : K} (hb : IsAlgebraic F b) :
    ∃ c : L, ∀ q : F[X], aeval b q = 0 ↔ aeval c q = 0 := by
  have hint : IsIntegral F b := hb.isIntegral
  have hmonic : (minpoly F b).Monic := minpoly.monic hint
  have hirr : Irreducible (minpoly F b) := minpoly.irreducible hint
  obtain ⟨c, hcaeval⟩ := IsAlgClosed.exists_aeval_eq_zero L (minpoly F b)
    (minpoly.degree_pos hint).ne'
  have hmc : minpoly F b = minpoly F c :=
    minpoly.eq_of_irreducible_of_monic hirr hcaeval hmonic
  refine ⟨c, fun q => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨r, rfl⟩ := minpoly.dvd F b h
    rw [map_mul, hcaeval, zero_mul]
  · obtain ⟨r, rfl⟩ := hmc ▸ minpoly.dvd F c h
    rw [map_mul, minpoly.aeval, zero_mul]

/-- **Finite satisfiability of transcendence**: over an infinite field extension, finitely many
nonzero polynomials have a common non-root. This is what makes the type asserting
transcendence over `F` finitely satisfiable. -/
theorem exists_forall_aeval_ne_zero [Field L] [Algebra F L] [Infinite L]
    (s : Finset F[X]) (hs : ∀ q ∈ s, q ≠ 0) :
    ∃ c : L, ∀ q ∈ s, aeval c q ≠ 0 := by
  classical
  have hPne : (∏ q ∈ s, q.map (algebraMap F L)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun q hq => ?_)
    simpa only [ne_eq, Polynomial.map_eq_zero_iff (algebraMap F L).injective] using hs q hq
  obtain ⟨c, hc⟩ := (finite_setOfPred_isRoot hPne).infinite_compl.nonempty
  refine ⟨c, fun q hq hq0 => hc ?_⟩
  change (∏ q ∈ s, q.map (algebraMap F L)).IsRoot c
  rw [IsRoot, eval_prod]
  refine Finset.prod_eq_zero hq ?_
  rw [eval_map, ← aeval_def]
  exact hq0
