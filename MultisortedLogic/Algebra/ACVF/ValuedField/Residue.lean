/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.AlgebraicBackground.RV

/-!
# Leading terms of units, and the purely residual computation

This is the computational core of Rideau-Kikuchi's Proposition 2.1.5 (purely residual 1-types). The
point of that lemma is that for `a` with a prescribed residue, and `Q` of degree below the minimal
polynomial of that residue, the valuation of `Q a` is just the largest valuation among the
coefficients of `Q` — nothing cancels, because the reduction of `Q` does not vanish at the residue.

Two ingredients:

* among elements of valuation `1`, the leading term is exactly the residue
  (`rv_eq_iff_residue_eq`), so on the unit part the `RV` sort *is* the residue field;
* a polynomial over the valuation ring whose reduction does not vanish at `res a` takes a unit
  value at `a` (`valuation_eval_eq_one`), which is the non-cancellation that makes the
  valuation of `Q a` computable.

## Main statements

* `ValuationSubring.rv_eq_iff_valuation_sub_lt_one`
* `ValuationSubring.rv_eq_iff_residue_eq`
* `ValuationSubring.valuation_eval_eq_one`
* `ValuationSubring.exists_toSubring_of_max`, `exists_coeff_max_toSubring` : the scaling step.
* `ValuationSubring.exists_rv_eval_eq_of_residual` : Proposition 2.1.5 itself, over a subfield.
-/

@[expose] public section

namespace ValuationSubring

open Polynomial IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K}

/-- Against a reference point of valuation `1`, having the same leading term means being at
distance less than `1`. -/
theorem rv_eq_iff_valuation_sub_lt_one {x y : K} (hy : A.valuation y = 1) :
    rv (A := A) x = rv (A := A) y ↔ A.valuation (x - y) < 1 := by
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact zero_ne_one hy
  rw [eq_comm, rv_eq_iff_valuation_sub_lt hy0, hy]

/-- **On the unit part, the leading term is the residue.** Two units of the valuation ring have
the same leading term exactly when they have the same residue, so the `RV` sort restricted to
valuation `1` is a copy of the residue field. -/
theorem rv_eq_iff_residue_eq {x y : A} (hy : IsUnit y) :
    rv (A := A) (x : K) = rv (A := A) (y : K) ↔ residue A x = residue A y := by
  have hy1 : A.valuation (y : K) = 1 := (A.valuation_eq_one_iff y).mp hy
  rw [rv_eq_iff_valuation_sub_lt_one hy1]
  rw [show ((x : K) - (y : K)) = ((x - y : A) : K) by push_cast; ring]
  rw [← A.valuation_lt_one_iff (x - y)]
  rw [← sub_eq_zero (a := residue A x), ← map_sub, residue_eq_zero_iff]

/-- **Non-cancellation in the residual case.** A polynomial over the valuation ring whose
reduction does not vanish at the residue of `a` takes a unit value at `a`. This is the step
"by minimality of `res⋆P`, `res (Q₀ a) = res⋆Q₀ (α) ≠ 0`, hence `v (Q₀ a) = 0`" in the
proof of Rideau-Kikuchi's Proposition 2.1.5(1). -/
theorem valuation_eval_eq_one {Q : A[X]} {a : A}
    (h : (Q.map (residue A)).eval (residue A a) ≠ 0) :
    A.valuation ((Q.eval a : A) : K) = 1 := by
  rw [← A.valuation_eq_one_iff, ← residue_ne_zero_iff_isUnit]
  rwa [eval_map, eval₂_at_apply] at h

/-!
### The scaling step

Rideau-Kikuchi's Proposition 2.1.5 is stated for `Q` over a subfield, and its proof begins by
dividing `Q` by its coefficient of largest valuation. The result is a polynomial over the valuation
ring whose reduction is nonzero — one of its coefficients is `1` — and which therefore does not
vanish at `res a` as long as its degree stays below the degree of `res a` over the residue subfield.
-/

/-- **The scaling step**, with the index supplied. Dividing a polynomial by a coefficient of
largest valuation gives a polynomial `R` over the valuation ring whose `i₀`-th coefficient is
`1`, of the same degree, with `Q a = q_{i₀} · R a`.

The index is an argument rather than a choice because a transfer argument has to scale by the
*same* index on both sides of an embedding. -/
theorem exists_toSubring_of_max {Q : K[X]} {i₀ : ℕ} (hi₀ : i₀ ∈ Q.support)
    (hmax : ∀ i ∈ Q.support, A.valuation (Q.coeff i) ≤ A.valuation (Q.coeff i₀)) :
    ∃ R : A[X],
      (∀ i, ((R.coeff i : A) : K) = (Q.coeff i₀)⁻¹ * Q.coeff i) ∧
      R.natDegree = Q.natDegree ∧ R.coeff i₀ = 1 ∧
      ∀ a : A, Q.eval (a : K) = Q.coeff i₀ * ((R.eval a : A) : K) := by
  classical
  have hq : Q.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  have hvq : A.valuation (Q.coeff i₀) ≠ 0 := (Valuation.ne_zero_iff _).mpr hq
  -- every coefficient of `Q / q_{i₀}` lies in the valuation ring
  have hle : ∀ i, A.valuation ((Q.coeff i₀)⁻¹ * Q.coeff i) ≤ 1 := by
    intro i
    by_cases h : Q.coeff i = 0
    · simp [h]
    · rw [map_mul, map_inv₀, inv_mul_le_one₀ (pos_iff_ne_zero.mpr hvq)]
      exact hmax i (Polynomial.mem_support_iff.mpr h)
  have hsub : ↑(C (Q.coeff i₀)⁻¹ * Q).coeffs ⊆ (A.toSubring : Set K) := by
    intro x hx
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [Polynomial.coeff_C_mul]
    exact A.mem_of_valuation_le_one _ (hle i)
  set R : A[X] := (C (Q.coeff i₀)⁻¹ * Q).toSubring A.toSubring hsub with hR
  have hmap : R.map A.toSubring.subtype = C (Q.coeff i₀)⁻¹ * Q := Polynomial.map_toSubring _ _ _
  have hc : ∀ i, ((R.coeff i : A) : K) = (Q.coeff i₀)⁻¹ * Q.coeff i := by
    intro i
    have := congrArg (AddMonoidAlgebra.coeff · i) hmap
    simpa [Polynomial.coeff_map, Polynomial.coeff_C_mul] using this
  refine ⟨R, hc, ?_, ?_, ?_⟩
  · rw [hR, Polynomial.natDegree_toSubring, Polynomial.natDegree_C_mul (inv_ne_zero hq)]
  · have := hc i₀
    rw [inv_mul_cancel₀ hq] at this
    exact Subtype.ext (by rw [this]; rfl)
  · intro a
    have heval : ((R.eval a : A) : K) = (R.map A.toSubring.subtype).eval ((a : A) : K) := by
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply (p := R) A.subtype a).symm
    rw [heval, hmap, Polynomial.eval_mul, Polynomial.eval_C, ← mul_assoc,
      mul_inv_cancel₀ hq, one_mul]

/-- **The scaling step.** The same, choosing the index of largest coefficient valuation. -/
theorem exists_coeff_max_toSubring {Q : K[X]} (hQ : Q ≠ 0) :
    ∃ (i₀ : ℕ) (R : A[X]), i₀ ∈ Q.support ∧
      (∀ i ∈ Q.support, A.valuation (Q.coeff i) ≤ A.valuation (Q.coeff i₀)) ∧
      (∀ i, ((R.coeff i : A) : K) = (Q.coeff i₀)⁻¹ * Q.coeff i) ∧
      R.natDegree = Q.natDegree ∧ R.coeff i₀ = 1 ∧
      ∀ a : A, Q.eval (a : K) = Q.coeff i₀ * ((R.eval a : A) : K) := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image Q.support
    (fun i => A.valuation (Q.coeff i)) (Polynomial.support_nonempty.mpr hQ)
  obtain ⟨R, hc, hdeg, hone, heval⟩ := exists_toSubring_of_max hi₀ hmax
  exact ⟨i₀, R, hi₀, hmax, hc, hdeg, hone, heval⟩

/-- **Proposition 2.1.5, the purely residual computation.** Let `a` be an element of the valuation
ring whose residue has degree at least `n` over the residues of a subfield `F` — that is, no nonzero
reduction of an `F`-polynomial of degree `< n` vanishes at `res a`. Then for `Q` over `F` of degree
`< n` the valuation of `Q a` is the largest valuation among the coefficients of `Q`, and its leading
term is that coefficient's times a unit whose residue is computed in the residue field. Nothing
cancels, so `rv (Q a)` is determined by the `rv` of the coefficients together with the residue of
`a`. -/
theorem exists_rv_eval_eq_of_residual_on {C : Set K} {n : ℕ} {a : A} {Q : K[X]}
    (hQ : Q ≠ 0) (hQC : ∀ i j : ℕ, (Q.coeff j)⁻¹ * Q.coeff i ∈ C) (hQn : Q.natDegree < n)
    (hdeg : ∀ R : A[X], (∀ i, ((R.coeff i : A) : K) ∈ C) → R.natDegree < n →
      R.map (residue A) ≠ 0 → (R.map (residue A)).eval (residue A a) ≠ 0) :
    ∃ (i₀ : ℕ) (R : A[X]), i₀ ∈ Q.support ∧
      (∀ i ∈ Q.support, A.valuation (Q.coeff i) ≤ A.valuation (Q.coeff i₀)) ∧
      (∀ i, ((R.coeff i : A) : K) = (Q.coeff i₀)⁻¹ * Q.coeff i) ∧
      IsUnit (R.eval a) ∧
      A.valuation (Q.eval (a : K)) = A.valuation (Q.coeff i₀) ∧
      rv (A := A) (Q.eval (a : K))
        = rv (A := A) (Q.coeff i₀) * rv (A := A) ((R.eval a : A) : K) := by
  obtain ⟨i₀, R, hi₀, hmax, hc, hdegR, hone, heval⟩ := exists_coeff_max_toSubring (A := A) hQ
  have hq : Q.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  -- the reduction of `R` is nonzero: its `i₀`-th coefficient is `1`
  have hRne : R.map (residue A) ≠ 0 := by
    intro h0
    have : (R.map (residue A)).coeff i₀ = 0 := by rw [h0, Polynomial.coeff_zero]
    rw [Polynomial.coeff_map, hone, map_one] at this
    exact one_ne_zero this
  have hRF : ∀ i, ((R.coeff i : A) : K) ∈ C := by
    intro i
    rw [hc i]
    exact hQC i i₀
  have hnv := hdeg R hRF (hdegR ▸ hQn) hRne
  have hunit : A.valuation ((R.eval a : A) : K) = 1 := valuation_eval_eq_one hnv
  refine ⟨i₀, R, hi₀, hmax, hc, (A.valuation_eq_one_iff _).mpr hunit, ?_, ?_⟩
  · rw [heval a, map_mul, hunit, mul_one]
  · rw [heval a, map_mul]

/-- **Proposition 2.1.5**, in the form the unbounded residual case uses: the coefficients are taken
from a subfield, which is closed under the ratios `exists_rv_eval_eq_of_residual_on` needs. -/
theorem exists_rv_eval_eq_of_residual {F : Subfield K} {n : ℕ} {a : A} {Q : K[X]}
    (hQ : Q ≠ 0) (hQF : ∀ i, Q.coeff i ∈ F) (hQn : Q.natDegree < n)
    (hdeg : ∀ R : A[X], (∀ i, ((R.coeff i : A) : K) ∈ F) → R.natDegree < n →
      R.map (residue A) ≠ 0 → (R.map (residue A)).eval (residue A a) ≠ 0) :
    ∃ (i₀ : ℕ) (R : A[X]), i₀ ∈ Q.support ∧
      (∀ i ∈ Q.support, A.valuation (Q.coeff i) ≤ A.valuation (Q.coeff i₀)) ∧
      (∀ i, ((R.coeff i : A) : K) = (Q.coeff i₀)⁻¹ * Q.coeff i) ∧
      IsUnit (R.eval a) ∧
      A.valuation (Q.eval (a : K)) = A.valuation (Q.coeff i₀) ∧
      rv (A := A) (Q.eval (a : K))
        = rv (A := A) (Q.coeff i₀) * rv (A := A) ((R.eval a : A) : K) :=
  exists_rv_eval_eq_of_residual_on hQ
    (fun i j => F.mul_mem (F.inv_mem (hQF j)) (hQF i)) hQn hdeg

end ValuationSubring
