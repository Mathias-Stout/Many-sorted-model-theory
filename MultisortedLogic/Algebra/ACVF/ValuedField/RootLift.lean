/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.ValuedField.BallFilter
public import MultisortedLogic.Algebra.ACVF.ValuedField.Lift

/-!
# Lifting a root of the reduction, without monicity

`ValuationSubring.exists_root_residue_eq` lifts a root of the reduction of a **monic** polynomial
over the valuation ring to a root of the polynomial itself. The scaling step of Rideau-Kikuchi's
immediate case produces a polynomial that is only *integral with a unit coefficient*, and there the
roots lying outside the valuation ring have to be accounted for.

They are, and without Gauss's lemma. Evaluate at a point `z'` whose residue is **not** a root of
the reduction: then `val (P z') = 1`, which pins down the product of the outside factors, because
those factors take the same value at every point of the valuation ring. Comparing with a point `z`
of residue `γ`, where `val (P z) < 1`, one factor must have strictly dropped, and it can only be
an inside one — its root is the required lift. The residue field is infinite (it is algebraically
closed whenever the field is), so a `z'` exists.

## Main statements

* `ValuationSubring.residue_eq_zero_iff` : the residue vanishes exactly below value `1`.
* `ValuationSubring.exists_root_residue_eq_of_map_ne_zero` : **the lifting**.
-/

@[expose] public section

namespace ValuationSubring

open Polynomial IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K}

/-- The residue of an element of the valuation ring vanishes exactly when its value drops
below `1`. -/
theorem residue_eq_zero_iff (x : A) : residue A x = 0 ↔ A.valuation ((x : A) : K) < 1 :=
  (IsLocalRing.residue_eq_zero_iff x).trans (A.valuation_lt_one_iff x)

/-- The value of `P` at a point of the valuation ring, read in the field. -/
theorem coe_eval_eq (P : A[X]) (w : A) :
    ((P.eval w : A) : K) = (P.map A.subtype).eval ((w : A) : K) :=
  (eval_map_apply A.subtype w).symm

/-- **Roots of the reduction lift, without monicity.** If `P` has coefficients in the valuation
ring, a nonzero reduction, and splits over the field, then every root of its reduction is the
residue of a root of `P` lying in the valuation ring. -/
theorem exists_root_residue_eq_of_map_ne_zero [Infinite (ResidueField A)]
    {P : A[X]} (hsplit : (P.map A.subtype).Splits)
    (hP : P.map (residue A) ≠ 0) {γ : ResidueField A}
    (hγ : (P.map (residue A)).eval γ = 0) :
    ∃ x : A, (P.map A.subtype).eval ((x : A) : K) = 0 ∧ residue A x = γ := by
  classical
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero] at hP
    exact hP rfl
  have hPK : P.map A.subtype ≠ 0 :=
    Polynomial.map_ne_zero_iff Subtype.val_injective |>.mpr hP0
  -- a point of residue `γ`, and one whose residue is not a root of the reduction
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective γ
  obtain ⟨ρ, hρ⟩ := Infinite.exists_notMem_finset (P.map (residue A)).roots.toFinset
  obtain ⟨z', hz'⟩ := Ideal.Quotient.mk_surjective ρ
  have hzres : residue A z = γ := hz
  have hz'res : residue A z' = ρ := hz'
  have hPz : A.valuation ((P.map A.subtype).eval ((z : A) : K)) < 1 := by
    rw [← coe_eval_eq]
    refine (residue_eq_zero_iff _).mp ?_
    rw [← eval_map_apply, hzres, hγ]
  have hPz' : ¬ A.valuation ((P.map A.subtype).eval ((z' : A) : K)) < 1 := by
    rw [← coe_eval_eq]
    intro hlt
    refine hρ (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr ?_))
    rw [Polynomial.IsRoot, ← hz'res, eval_map_apply]
    exact (residue_eq_zero_iff _).mpr hlt
  have hlt := lt_of_lt_of_le hPz (not_lt.mp hPz')
  rw [valuation_eval_eq_prod hsplit, valuation_eval_eq_prod hsplit] at hlt
  have hlead : A.valuation (P.map A.subtype).leadingCoeff ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff, Polynomial.leadingCoeff_eq_zero]
    exact hPK
  have hprod := (mul_lt_mul_iff_right₀ (pos_iff_ne_zero.mpr hlead)).mp hlt
  -- some factor strictly drops, and it cannot be one whose root is outside the valuation ring
  have hex : ∃ r ∈ (P.map A.subtype).roots,
      A.valuation (((z : A) : K) - r) < A.valuation (((z' : A) : K) - r) := by
    by_contra hcon
    push Not at hcon
    exact absurd (Multiset.prod_map_le_prod_map _ _ hcon) (not_le.mpr hprod)
  obtain ⟨r, hr, hrlt⟩ := hex
  have hrA : r ∈ A := by
    by_contra hrA
    have hvr : 1 < A.valuation r := by
      rw [← not_le]
      exact fun h => hrA (A.mem_of_valuation_le_one r h)
    have hsub : ∀ w : A, A.valuation (((w : A) : K) - r) = A.valuation r := by
      intro w
      rw [sub_eq_add_neg, A.valuation.map_add_of_distinct_val (by
        rw [Valuation.map_neg]
        exact ne_of_lt (lt_of_le_of_lt (A.valuation_le_one w) hvr)),
        Valuation.map_neg, max_eq_right (le_of_lt (lt_of_le_of_lt (A.valuation_le_one w) hvr))]
    rw [hsub z, hsub z'] at hrlt
    exact absurd hrlt (lt_irrefl _)
  refine ⟨⟨r, hrA⟩, (Polynomial.mem_roots hPK).mp hr, ?_⟩
  have hdrop : A.valuation ((((z - ⟨r, hrA⟩ : A) : A) : K)) < 1 := by
    have hcoe : (((z - ⟨r, hrA⟩ : A) : A) : K) = ((z : A) : K) - r := rfl
    rw [hcoe]
    exact lt_of_lt_of_le hrlt (A.valuation_le_one (z' - ⟨r, hrA⟩))
  have := (residue_eq_zero_iff (z - ⟨r, hrA⟩)).mpr hdrop
  rw [map_sub, sub_eq_zero] at this
  rw [← this, hzres]

end ValuationSubring
