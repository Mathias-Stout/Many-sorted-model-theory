/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.ValuedField.Extend
public import MultisortedLogic.Algebra.ACVF.ValuedField.Residue

/-!
# The residual case, as a reflection

`Algebra/ACVF/ValuedField/Extend.lean` reduces everything the extension of an embedding needs to a
single property of `a` and `b`: `ReflectData`, that the order of the values of polynomials is the
same on the two sides. This file establishes it in Rideau-Kikuchi's **residual** case, where what is
new about `a` is its residue.

The point is how little is needed. Proposition 2.1.5 (`exists_rv_eval_eq_of_residual`) says that
when no nonzero reduction of an integral polynomial of degree below `n` vanishes at `res a`, the
value of `Q a` is simply the **largest value among the coefficients of `Q`**. So the order of the
values of polynomials is determined by the order of the values of the coefficients — and that order
is the same on the two sides by hypothesis, which also makes the *same* index dominant on both. No
map of residue fields appears: leading terms do not have to be compared, because `ReflectData.rvEq`
derives them from values.

What the far side must satisfy is the same non-degeneracy, `ResidualDeg ψ AL b n`. That is a real
condition on `b` — it is where the residue field re-enters, when the caller chooses `b` — but it
is a hypothesis here and not a construction.

## Main definitions

* `ValuationSubring.ResidualDeg` : the non-degeneracy hypothesis of Proposition 2.1.5.
* `ValuationSubring.ResidualDegOn` : the same, for coefficients in a prescribed set.

## Main statements

* `ValuationSubring.valuation_le_iff_of_residual_on` : the reflection, below the degree bound and
  for coefficients in a prescribed set. This is the finite fragment the transcendental case needs;
  the whole pattern then comes by compactness, in `Algebra/ACVF/FieldStep/Routing.lean`.
* `ValuationSubring.reflectData_of_residual_modByMonic` : the algebraic case, for all polynomials.
* `exists_forall_eval_ne_zero_of_coeffs_mem` : over an infinite field, the nonzero polynomials of
  bounded degree with coefficients in a finite set have a common non-root. This is how the
  caller finds a `b` with `ResidualDeg ψ AL b n`.
-/

@[expose] public section

namespace ValuationSubring

open Polynomial IsLocalRing

variable {K L : Type*} [Field K] [Field L] {AK : ValuationSubring K} {AL : ValuationSubring L}
variable {R : Type*} [Field R] {φ : R →+* K} {ψ : R →+* L}

/-- **The non-degeneracy hypothesis of Proposition 2.1.5**: no nonzero reduction of an integral
polynomial over the coefficient field, of degree below `n`, vanishes at the residue of `a`. For `n`
the degree of `res a` over the residue field of the coefficients this says exactly that the degree
is not smaller. -/
def ResidualDeg (φ : R →+* K) (AK : ValuationSubring K) (a : AK) (n : ℕ) : Prop :=
  ∀ RQ : AK[X], (∀ i, ((RQ.coeff i : AK) : K) ∈ (φ.fieldRange : Subfield K)) →
    RQ.natDegree < n → RQ.map (residue AK) ≠ 0 →
    (RQ.map (residue AK)).eval (residue AK a) ≠ 0

/-- **The non-degeneracy hypothesis of Proposition 2.1.5, with the coefficients bounded.** Only the
polynomials whose coefficients lie in a prescribed set `C` have to be avoided.

`ResidualDeg φ AK a n` is the case `C = φ.fieldRange`. The bounded form is what the *finite*
fragment of the residual case needs: the residue of the far-side element only has to avoid the
finitely many polynomials that a given finite set of polynomials produces, which an infinite
residue field always allows, whereas full transcendence over the residues of the coefficient
field may be unattainable in the target. -/
def ResidualDegOn (C : Set K) (AK : ValuationSubring K) (a : AK) (n : ℕ) : Prop :=
  ∀ RQ : AK[X], (∀ i, ((RQ.coeff i : AK) : K) ∈ C) → RQ.natDegree < n →
    RQ.map (residue AK) ≠ 0 → (RQ.map (residue AK)).eval (residue AK a) ≠ 0

/-- **The dominant coefficient is the same on both sides, with the coefficients bounded.** The
set `D` lives in the coefficient field and has to contain the ratios of the coefficients of `S`,
which is what the scaling step of Proposition 2.1.5 forms. -/
theorem exists_dominant_coeff_of_residual_on {D : Set R} {a : AK} {b : AL} {n : ℕ}
    (hcoeff : CoeffReflect φ ψ AK AL)
    (hdegK : ResidualDegOn (φ '' D) AK a n) (hdegL : ResidualDegOn (ψ '' D) AL b n)
    {S : R[X]} (hS0 : S ≠ 0) (hSn : S.natDegree < n)
    (hSD : ∀ i j : ℕ, (S.coeff j)⁻¹ * S.coeff i ∈ D) :
    ∃ i ∈ S.support,
      AK.valuation (evalOn φ (a : K) S) = AK.valuation (φ (S.coeff i)) ∧
        AL.valuation (evalOn' ψ (b : L) S) = AL.valuation (ψ (S.coeff i)) := by
  have hevK : evalOn φ (a : K) S = (S.map φ).eval (a : K) := (Polynomial.eval_map _ _).symm
  have hevL : evalOn' ψ (b : L) S = (S.map ψ).eval (b : L) := (Polynomial.eval_map _ _).symm
  obtain ⟨i₀, -, hi₀, hmaxK, -, -, hvalK, -⟩ :=
    exists_rv_eval_eq_of_residual_on (A := AK) (C := φ '' D) (Polynomial.map_ne_zero hS0)
      (fun i j => by
        rw [Polynomial.coeff_map, Polynomial.coeff_map, ← map_inv₀, ← map_mul]
        exact ⟨_, hSD i j, rfl⟩)
      (by rwa [Polynomial.natDegree_map]) hdegK
  obtain ⟨i₁, -, hi₁, hmaxL, -, -, hvalL, -⟩ :=
    exists_rv_eval_eq_of_residual_on (A := AL) (C := ψ '' D) (Polynomial.map_ne_zero hS0)
      (fun i j => by
        rw [Polynomial.coeff_map, Polynomial.coeff_map, ← map_inv₀, ← map_mul]
        exact ⟨_, hSD i j, rfl⟩)
      (by rwa [Polynomial.natDegree_map]) hdegL
  refine ⟨i₀, (mem_support_map_of_injective φ.injective).mp hi₀,
    by rw [hevK, hvalK, Polynomial.coeff_map], ?_⟩
  rw [hevL, hvalL, Polynomial.coeff_map]
  refine le_antisymm ?_ ?_
  · have hK : AK.valuation (φ (S.coeff i₁)) ≤ AK.valuation (φ (S.coeff i₀)) := by
      simpa only [Polynomial.coeff_map] using
        hmaxK i₁ ((mem_support_map_of_injective φ.injective).mpr
          ((mem_support_map_of_injective ψ.injective).mp hi₁))
    exact (hcoeff _ _).mp hK
  · simpa only [Polynomial.coeff_map] using
      hmaxL i₀ ((mem_support_map_of_injective ψ.injective).mpr
        ((mem_support_map_of_injective φ.injective).mp hi₀))

/-- **The reflection of the order of values, with degrees and coefficients bounded.** This is the
form the finite fragment `ValuePatternAt` uses. -/
theorem valuation_le_iff_of_residual_on {D : Set R} {a : AK} {b : AL} {n : ℕ}
    (hcoeff : CoeffReflect φ ψ AK AL)
    (hdegK : ResidualDegOn (φ '' D) AK a n) (hdegL : ResidualDegOn (ψ '' D) AL b n)
    {P Q : R[X]} (hPn : P.natDegree < n) (hQn : Q.natDegree < n)
    (hPD : ∀ i j : ℕ, (P.coeff j)⁻¹ * P.coeff i ∈ D)
    (hQD : ∀ i j : ℕ, (Q.coeff j)⁻¹ * Q.coeff i ∈ D) :
    AK.valuation (evalOn φ (a : K) P) ≤ AK.valuation (evalOn φ (a : K) Q)
      ↔ AL.valuation (evalOn' ψ (b : L) P) ≤ AL.valuation (evalOn' ψ (b : L) Q) := by
  by_cases hP0 : P = 0
  · subst hP0
    simp only [map_zero]
    exact ⟨fun _ => zero_le, fun _ => zero_le⟩
  by_cases hQ0 : Q = 0
  · subst hQ0
    obtain ⟨i, hi, hvK, hvL⟩ :=
      exists_dominant_coeff_of_residual_on hcoeff hdegK hdegL hP0 hPn hPD
    have hc : P.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hK0 : AK.valuation (evalOn φ (a : K) P) ≠ 0 := by
      rw [hvK]
      exact (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff φ φ.injective).mpr hc)
    have hL0 : AL.valuation (evalOn' ψ (b : L) P) ≠ 0 := by
      rw [hvL]
      exact (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff ψ ψ.injective).mpr hc)
    simp only [map_zero]
    exact ⟨fun hle => absurd (le_antisymm hle zero_le) hK0,
      fun hle => absurd (le_antisymm hle zero_le) hL0⟩
  obtain ⟨i, -, hvKP, hvLP⟩ :=
    exists_dominant_coeff_of_residual_on hcoeff hdegK hdegL hP0 hPn hPD
  obtain ⟨j, -, hvKQ, hvLQ⟩ :=
    exists_dominant_coeff_of_residual_on hcoeff hdegK hdegL hQ0 hQn hQD
  rw [hvKP, hvKQ, hvLP, hvLQ]
  exact hcoeff (P.coeff i) (Q.coeff j)

/-! ### The unbounded case

`ResidualDeg` is `ResidualDegOn` at the whole coefficient field, so the unbounded statements are
the bounded ones at `D = univ`; there is nothing to prove twice. -/

theorem ResidualDeg.residualDegOn_univ {φ : R →+* K} {AK : ValuationSubring K} {a : AK} {n : ℕ}
    (h : ResidualDeg φ AK a n) : ResidualDegOn (φ '' Set.univ) AK a n := by
  rw [Set.image_univ]
  exact fun RQ hRQ => h RQ hRQ

/-- **The reflection of the order of values, below the degree bound.** -/
theorem valuation_le_iff_of_residual {a : AK} {b : AL} {n : ℕ}
    (hcoeff : CoeffReflect φ ψ AK AL)
    (hdegK : ResidualDeg φ AK a n) (hdegL : ResidualDeg ψ AL b n)
    {P Q : R[X]} (hPn : P.natDegree < n) (hQn : Q.natDegree < n) :
    AK.valuation (evalOn φ (a : K) P) ≤ AK.valuation (evalOn φ (a : K) Q)
      ↔ AL.valuation (evalOn' ψ (b : L) P) ≤ AL.valuation (evalOn' ψ (b : L) Q) :=
  valuation_le_iff_of_residual_on (D := Set.univ) hcoeff hdegK.residualDegOn_univ
    hdegL.residualDegOn_univ hPn hQn (fun _ _ => Set.mem_univ _) fun _ _ => Set.mem_univ _

/-- **The residual case, `res a` algebraic of degree `n`**: every polynomial is first reduced
modulo the monic `P₀` that both `a` and `b` satisfy — an exact lifting of the minimal polynomial
of `res a`. -/
theorem reflectData_of_residual_modByMonic {a : AK} {b : AL} {n : ℕ} (hn : 0 < n)
    (hcoeff : CoeffReflect φ ψ AK AL)
    (hdegK : ResidualDeg φ AK a n) (hdegL : ResidualDeg ψ AL b n)
    {P₀ : R[X]} (hP₀ : P₀.Monic) (hP₀n : P₀.natDegree ≤ n)
    (hPa : evalOn φ (a : K) P₀ = 0) (hPb : evalOn' ψ (b : L) P₀ = 0) :
    ReflectData φ ψ AK AL (a : K) (b : L) := by
  refine ⟨fun P Q => ?_⟩
  obtain ⟨P', hP'n, hP'K, hP'L⟩ := exists_reduced_of_monic hP₀ hn hP₀n hPa hPb P
  obtain ⟨Q', hQ'n, hQ'K, hQ'L⟩ := exists_reduced_of_monic hP₀ hn hP₀n hPa hPb Q
  rw [hP'K, hQ'K, hP'L, hQ'L]
  exact valuation_le_iff_of_residual hcoeff hdegK hdegL hP'n hQ'n

end ValuationSubring

/-! ### A common non-root, for the far-side residue -/

open Polynomial in
/-- **A common non-root of every polynomial of bounded degree with coefficients in a finite set.**
There are only finitely many such polynomials, hence finitely many roots between them, so an
infinite field has an element that is a root of none.

This is the finite fragment of transcendence: in Rideau-Kikuchi's residual case the far-side element
is a unit whose residue is not a root of any of the finitely many polynomials that the given finite
set of polynomials produces. -/
theorem exists_forall_eval_ne_zero_of_coeffs_mem {k : Type*} [Field k] [Infinite k]
    (E : Finset k) (n : ℕ) :
    ∃ x : k, ∀ q : k[X], q ≠ 0 → q.natDegree < n → (∀ i, q.coeff i ∈ E) → q.eval x ≠ 0 := by
  classical
  set S : Finset k[X] := (Finset.univ : Finset (Fin n → E)).image
    fun f => ∑ i : Fin n, Polynomial.monomial (i : ℕ) ((f i : k)) with hS
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (S.biUnion fun q => q.roots.toFinset)
  refine ⟨x, fun q hq0 hqn hqE hroot => hx (Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩)⟩
  · refine Finset.mem_image.mpr ⟨fun i => ⟨q.coeff i, hqE i⟩, Finset.mem_univ _, ?_⟩
    conv_rhs => rw [q.as_sum_range' n hqn, Finset.sum_range]
  · rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
    exact hroot
