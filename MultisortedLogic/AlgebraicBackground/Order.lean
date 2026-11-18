/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathias Stout
-/

module

public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.GroupTheory.Divisible

/-! # Order-theoretic facts about ordered abelian groups

Generic lemmas about ordered abelian groups, used for the theory of divisible ordered abelian
groups (`Algebra/DOAG/`). Nothing in this file mentions model theory.

## Main results

* `nsmulRec_eq_nsmul` : in any `AddMonoid`, the generic recursion `nsmulRec` agrees with `•`.
* `DivisibleBy.denselyOrdered` : a `ℤ`-divisible linearly ordered abelian group is densely
  ordered.
-/

public section

/-- The generic recursion `nsmulRec` (which only needs `Zero` and `Add`) agrees with the
`nsmul` of any `AddMonoid`. -/
theorem nsmulRec_eq_nsmul {G : Type*} [AddMonoid G] (n : ℕ) (a : G) :
    nsmulRec n a = n • a := by
  induction n with
  | zero => rw [nsmulRec, zero_nsmul]
  | succ n ih => rw [nsmulRec, ih, succ_nsmul]

/-- A `ℤ`-divisible linearly ordered abelian group is densely ordered: between `a < b` lies
the half of `a + b`. -/
theorem DivisibleBy.denselyOrdered {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [DivisibleBy G ℤ] : DenselyOrdered G := by
  constructor
  intro a b hab
  set c := DivisibleBy.div (a + b) (2 : ℤ) with hcdef
  have h2 : (2 : ℤ) • c = a + b :=
    DivisibleBy.div_cancel (n := (2 : ℤ)) (a + b) two_ne_zero
  refine ⟨c, ?_, ?_⟩
  · by_contra h
    rw [not_lt] at h
    have hle : (2 : ℤ) • c ≤ (2 : ℤ) • a := (zsmul_le_zsmul_iff_right two_pos).mpr h
    rw [h2, two_zsmul] at hle
    exact ((add_lt_add_right hab a).trans_le hle).false
  · by_contra h
    rw [not_lt] at h
    have hle : (2 : ℤ) • b ≤ (2 : ℤ) • c := (zsmul_le_zsmul_iff_right two_pos).mpr h
    rw [h2, two_zsmul] at hle
    exact ((add_lt_add_left hab b).trans_le hle).false
