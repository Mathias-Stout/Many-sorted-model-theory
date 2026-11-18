/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Polynomial.Splits

/-!
# The leading term structure `RV`

For a valued field `K` with valuation subring `A`, the *leading term structure* is
`RV = Kˣ / (1 + 𝔪) ∪ {0}`, together with the multiplicative map `rv : K → RV` extending the
quotient map by `rv 0 = 0`. It is the sort that makes quantifier elimination for algebraically
closed valued fields work in a three-sorted language.

Mathlib already provides the subgroup `1 + 𝔪` of `Kˣ` as
`ValuationSubring.principalUnitGroup`, so `RV` is the quotient by it with a zero adjoined.

## Main definitions

* `ValuationSubring.RVUnits` : the group `Kˣ / (1 + 𝔪)`.
* `ValuationSubring.RV` : the monoid `Kˣ / (1 + 𝔪) ∪ {0}`.
* `ValuationSubring.rv` : the map `K → RV`.

## Main statements

* `ValuationSubring.rv_eq_zero_iff` : `rv x = 0 ↔ x = 0`.
* `ValuationSubring.rv_eq_iff_valuation_sub_lt` : `rv x = rv y ↔ v (x - y) < v y`, for `y ≠ 0`.
  This is the statement that the fibers of `rv` are the open balls `{x : v (x - y) < v y}`, and
  it is what makes `rv`-distances the right thing to quantify over.
-/

@[expose] public section

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- The units of the leading term structure: `Kˣ / (1 + 𝔪)`. -/
abbrev RVUnits := Kˣ ⧸ A.principalUnitGroup

/-- The leading term structure `RV = Kˣ / (1 + 𝔪) ∪ {0}`. -/
abbrev RV := WithZero A.RVUnits

variable {A}

open scoped Classical in
/-- The leading term map `rv : K → RV`, sending `0` to `0` and `x ≠ 0` to its class. -/
noncomputable def rv : K →*₀ A.RV where
  toFun x := if h : x = 0 then 0 else ((QuotientGroup.mk (Units.mk0 x h) : A.RVUnits) : A.RV)
  map_zero' := dite_eq_left rfl
  map_one' := by
    rw [dite_eq_right (one_ne_zero (α := K))]
    simp
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    rw [dite_eq_right hx, dite_eq_right hy, dite_eq_right (mul_ne_zero hx hy), ← WithZero.coe_mul,
      ← QuotientGroup.mk_mul, Units.mk0_mul]

@[simp]
theorem rv_zero : rv (A := A) 0 = 0 := rv.map_zero

theorem rv_apply_of_ne_zero {x : K} (hx : x ≠ 0) :
    rv (A := A) x = ((QuotientGroup.mk (Units.mk0 x hx) : A.RVUnits) : A.RV) :=
  dite_eq_right hx

@[simp]
theorem rv_eq_zero_iff {x : K} : rv (A := A) x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [rv_apply_of_ne_zero hx, hx]

/-- The fibers of `rv` are the open balls: two nonzero elements have the same leading term
exactly when their difference is smaller than either of them. -/
theorem rv_eq_iff_valuation_sub_lt {x y : K} (hx : x ≠ 0) :
    rv (A := A) x = rv (A := A) y ↔ A.valuation (y - x) < A.valuation x := by
  by_cases hy : y = 0
  · subst hy
    simp only [rv_zero, rv_eq_zero_iff, hx, zero_sub, Valuation.map_neg, lt_self_iff_false]
  rw [rv_apply_of_ne_zero hx, rv_apply_of_ne_zero hy, WithZero.coe_inj,
    QuotientGroup.eq, mem_principalUnitGroup_iff]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [show x⁻¹ * y - 1 = (y - x) * x⁻¹ by field_simp]
  rw [map_mul, map_inv₀, ← div_eq_mul_inv,
    div_lt_one₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hx))]

/-- The valuation of a unit, as a group homomorphism `Kˣ →* Γ`. -/
noncomputable def valUnits : Kˣ →* A.ValueGroup :=
  (A.valuation : K →*₀ A.ValueGroup).toMonoidHom.comp (Units.coeHom K)

@[simp]
theorem valUnits_apply (u : Kˣ) : valUnits (A := A) u = A.valuation (u : K) := rfl

/-- The valuation on the leading term structure, `val : RV → Γ`. It satisfies
`val ∘ rv = valuation` (`ValuationSubring.rvVal_rv`). -/
noncomputable def rvVal : A.RV →*₀ A.ValueGroup :=
  WithZero.lift' (QuotientGroup.lift _ valUnits A.principal_units_le_units)

@[simp]
theorem rvVal_rv (x : K) : rvVal (A := A) (rv x) = A.valuation x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [rv_apply_of_ne_zero hx]
    rfl

theorem rv_surjective : Function.Surjective (rv (A := A)) := by
  intro r
  induction r using WithZero.recZeroCoe with
  | zero => exact ⟨0, rv_zero⟩
  | coe q =>
    induction q using QuotientGroup.induction_on with
    | _ u => exact ⟨(u : K), by simp [rv_apply_of_ne_zero (Units.ne_zero u)]⟩

/-- `rvVal` detects the zero of `A.RV`: since `rv` is onto and `A.valuation x = 0 ↔ x = 0`,
the only leading term of value `0` is `0` itself. -/
theorem rvVal_eq_zero_iff {ξ : A.RV} : rvVal (A := A) ξ = 0 ↔ ξ = 0 := by
  obtain ⟨x, rfl⟩ := rv_surjective ξ
  rw [rvVal_rv, Valuation.zero_iff, rv_eq_zero_iff]

/-- **A non-canceling sum depends only on the leading terms.** If `u` and `u'` have the same
leading term and `u + w` does not cancel, then `u + w` and `u' + w` have the same leading term
too — which is what lets a distance computed at one point of a subfield be moved to another. -/
theorem rv_add_congr {u u' w : K} (h : rv (A := A) u = rv (A := A) u')
    (hnc : A.valuation (u + w) = max (A.valuation u) (A.valuation w)) :
    rv (A := A) (u + w) = rv (A := A) (u' + w) := by
  by_cases hu : u = 0
  · subst hu
    rw [rv_zero, eq_comm, rv_eq_zero_iff] at h
    rw [h]
  have hsub : A.valuation (u' - u) < A.valuation u := (rv_eq_iff_valuation_sub_lt hu).mp h
  have hle : A.valuation u ≤ A.valuation (u + w) := by rw [hnc]; exact le_max_left _ _
  have huw : u + w ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hle
    exact hu ((Valuation.zero_iff _).mp (le_antisymm hle zero_le))
  rw [rv_eq_iff_valuation_sub_lt huw, show u' + w - (u + w) = u' - u by ring]
  exact lt_of_lt_of_le hsub hle

/-- **Non-cancellation may be read at either of two elements with the same leading term**, and
then the two translates have the same value. -/
theorem valuation_add_max_congr {u u' w : K} (h : rv (A := A) u = rv (A := A) u')
    (hnc : A.valuation (u + w) = max (A.valuation u) (A.valuation w)) :
    A.valuation (u' + w) = max (A.valuation u') (A.valuation w) := by
  by_cases hu : u = 0
  · subst hu
    rw [rv_zero, eq_comm, rv_eq_zero_iff] at h
    rw [h]
    exact hnc
  have hvu : A.valuation u' = A.valuation u := by rw [← rvVal_rv (A := A) u', ← h, rvVal_rv]
  have hsub : A.valuation (u' - u) < A.valuation u := (rv_eq_iff_valuation_sub_lt hu).mp h
  have hle : A.valuation u ≤ A.valuation (u + w) := by rw [hnc]; exact le_max_left _ _
  have hlt : A.valuation (u' - u) < A.valuation (u + w) := lt_of_lt_of_le hsub hle
  rw [hvu, ← hnc, show u' + w = u + w + (u' - u) by ring,
    A.valuation.map_add_of_distinct_val (ne_of_lt hlt).symm, max_eq_left (le_of_lt hlt)]

/-- The same as `rv_add_congr`, with the non-cancellation hypothesis read at `u'`. This is the
form the transfer uses, because `u'` and `w` are then values of the coefficient field, where
non-cancellation is a comparison the embedding reflects. -/
theorem rv_add_congr' {u u' w : K} (h : rv (A := A) u = rv (A := A) u')
    (hnc : A.valuation (u' + w) = max (A.valuation u') (A.valuation w)) :
    rv (A := A) (u + w) = rv (A := A) (u' + w) :=
  rv_add_congr h (valuation_add_max_congr h.symm hnc)

open Polynomial in
/-- If `p` splits, its leading term at `a` is determined by the leading terms of the distances
from `a` to the roots of `p`. This is what makes the `rv`-distances of `a` to the elements of a
subfield determine `rv (p a)` for every polynomial `p` over that subfield, when the subfield is
algebraically closed. -/
theorem rv_eval_eq_leadingCoeff_mul_prod {p : K[X]} (hp : p.Splits) (a : K) :
    rv (A := A) (p.eval a) =
      rv (A := A) p.leadingCoeff * (p.roots.map fun r => rv (A := A) (a - r)).prod := by
  conv_lhs => rw [hp.eq_prod_roots]
  rw [eval_mul, eval_C, map_mul, eval_multiset_prod, Multiset.map_map]
  congr 1
  rw [map_multiset_prod]
  simp

end ValuationSubring
