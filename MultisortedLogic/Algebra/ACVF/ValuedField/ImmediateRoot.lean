/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.ValuedField.ResidueTransfer
public import MultisortedLogic.Algebra.ACVF.ValuedField.RootLift

/-!
# The far-side root at a prescribed distance

Rideau-Kikuchi's immediate case, in its algebraic sub-case, needs an element of the *target* that is
a root of the image of the minimal polynomial `P` **and** at a prescribed distance from a point of
the coefficient field. This file produces it, and the point is that the whole question is a question
about the residue field of the coefficient field — which is literally the same object on the two
sides (`Algebra/ACVF/ValuedField/ResidueTransfer.lean`).

Substituting `X = c + s T` turns "a root at distance `val (φ s)` from `φ c` with leading term
`rv (φ s)`" into "a root of residue `1`". Normalizing the shifted polynomial by its coefficient of
largest value makes it integral with a unit coefficient, and its reduction lives over the residue
field of the coefficient field's valuation ring. So the reduction is *the same polynomial* on both
sides, and `1` is a root of it on the far side because it is one on the near side.
`exists_root_residue_eq_of_map_ne_zero` then lifts that root, without monicity.

## Main statements

* `ValuationSubring.exists_root_rv_sub_eq` : **the far-side root**.
-/

@[expose] public section

namespace ValuationSubring

open Polynomial IsLocalRing

variable {K L R : Type*} [Field K] [Field L] [Field R]
variable {A : ValuationSubring K} {AL : ValuationSubring L} {φ : R →+* K} {ψ : R →+* L}

/-- **Gauss normalization over a valued coefficient field.** Dividing a nonzero polynomial by
its coefficient of largest value makes every coefficient integral, and leaves that one a unit. -/
theorem exists_normalize_coeff {G : R[X]} (hG0 : G ≠ 0) :
    ∃ (e : R) (i₀ : ℕ), e ≠ 0 ∧ (∀ i, A.valuation (φ (e⁻¹ * G.coeff i)) ≤ 1) ∧
      A.valuation (φ (e⁻¹ * G.coeff i₀)) = 1 := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image G.support
    (fun i => A.valuation (φ (G.coeff i))) (Polynomial.support_nonempty.mpr hG0)
  have he0 : G.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  have he0K : φ (G.coeff i₀) ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr he0
  refine ⟨G.coeff i₀, i₀, he0, fun i => ?_, ?_⟩
  · rw [map_mul, map_inv₀, map_mul, map_inv₀, inv_mul_le_one₀
      (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr he0K))]
    by_cases h : G.coeff i = 0
    · rw [h, map_zero, map_zero]
      exact zero_le
    · exact hmax i (Polynomial.mem_support_iff.mpr h)
  · rw [map_mul, map_inv₀, map_mul, map_inv₀,
      inv_mul_cancel₀ ((Valuation.ne_zero_iff _).mpr he0K)]

/-- **The far-side root at a prescribed distance.** If `a` is a root of `P` over the near side at
distance `val (φ s)` and leading term `rv (φ s)` from `φ c`, then the far side has a root of the
image of `P` at leading-term distance `rv (ψ s)` from `ψ c`. -/
theorem exists_root_rv_sub_eq [IsAlgClosed L] [Infinite (ResidueField AL)]
    (hcoeff : CoeffReflect φ ψ A AL)
    {a : K} {P : R[X]} (hP0 : P ≠ 0) (hPa : (P.map φ).eval a = 0)
    {c s : R} (hs0 : s ≠ 0) (hrv : rv (A := A) (a - φ c) = rv (A := A) (φ s)) :
    ∃ b : L, (P.map ψ).eval b = 0 ∧ rv (A := AL) (b - ψ c) = rv (A := AL) (ψ s) := by
  classical
  have hs0K : φ s ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr hs0
  have hs0L : ψ s ≠ 0 := (map_ne_zero_iff ψ ψ.injective).mpr hs0
  -- the shift `X = c + s T`
  set q : R[X] := C c + C s * X with hqdef
  have hq1 : q.coeff 1 = s := by simp [hqdef]
  set G : R[X] := P.comp q with hGdef
  have hG0 : G ≠ 0 := by
    rw [hGdef]
    intro h0
    rcases Polynomial.comp_eq_zero_iff.mp h0 with h | ⟨-, h⟩
    · exact hP0 h
    · have := congrArg (AddMonoidAlgebra.coeff · 1) h
      simp only [hq1, Polynomial.coeff_C, ite_eq_right one_ne_zero] at this
      exact hs0 this
  have hGevalK : ∀ t : K, (G.map φ).eval t = (P.map φ).eval (φ c + φ s * t) := by
    intro t
    rw [hGdef, Polynomial.map_comp, Polynomial.eval_comp]
    congr 1
    simp [hqdef]
  have hGevalL : ∀ t : L, (G.map ψ).eval t = (P.map ψ).eval (ψ c + ψ s * t) := by
    intro t
    rw [hGdef, Polynomial.map_comp, Polynomial.eval_comp]
    congr 1
    simp [hqdef]
  -- the near-side root of residue `1`
  set u : K := (a - φ c) / φ s with hudef
  have hru : rv (A := A) u = 1 := by
    rw [hudef, map_div₀, hrv, div_self ((rv_eq_zero_iff (A := A)).not.mpr hs0K)]
  have hGu : (G.map φ).eval u = 0 := by
    rw [hGevalK, hudef, mul_div_cancel₀ _ hs0K, add_sub_cancel]
    exact hPa
  have hvu : A.valuation u = 1 := by rw [← rvVal_rv (A := A) u, hru, map_one]
  have huA : u ∈ A := A.mem_of_valuation_le_one u (le_of_eq hvu)
  have hresu : residue A ⟨u, huA⟩ = 1 := by
    have h1 : residue A (1 : A) = 1 := map_one _
    rw [← h1]
    refine (rv_eq_iff_residue_eq (A := A) isUnit_one).mp ?_
    rw [OneMemClass.coe_one]
    change rv (A := A) u = rv (A := A) (1 : K)
    rw [hru, map_one]
  -- normalize by the coefficient of largest value
  obtain ⟨e, i₀, he0, hint, hone⟩ := exists_normalize_coeff (A := A) (φ := φ) hG0
  have he0L : ψ e ≠ 0 := (map_ne_zero_iff ψ ψ.injective).mpr he0
  set G₂ : R[X] := C e⁻¹ * G with hG2def
  have hG2coeff : ∀ i, G₂.coeff i = e⁻¹ * G.coeff i := fun i => by
    rw [hG2def, Polynomial.coeff_C_mul]
  have hG2int : ∀ i, A.valuation (φ (G₂.coeff i)) ≤ 1 := fun i => by
    rw [hG2coeff]; exact hint i
  have hG2one : A.valuation (φ (G₂.coeff i₀)) = 1 := by rw [hG2coeff]; exact hone
  -- read `G₂` over the valuation ring of the coefficient field
  have hlifts : G₂ ∈ Polynomial.lifts (coeffValRing A φ).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun i => ⟨⟨G₂.coeff i, A.mem_of_valuation_le_one _ (hG2int i)⟩, rfl⟩
  obtain ⟨Gh, hGhmap, -⟩ := Polynomial.exists_degree_eq_of_mem_lifts hlifts
  have := isLocalHom_coeffValRingHomL hcoeff
  have hcompK : A.subtype.comp (coeffValRingHomK A φ)
      = φ.comp (coeffValRing A φ).subtype := RingHom.ext fun _ => rfl
  have hcompL : AL.subtype.comp (coeffValRingHomL hcoeff)
      = ψ.comp (coeffValRing A φ).subtype := RingHom.ext fun _ => rfl
  have hmapK : (Gh.map (coeffValRingHomK A φ)).map A.subtype = G₂.map φ := by
    rw [Polynomial.map_map, hcompK, ← Polynomial.map_map, hGhmap]
  have hmapL : (Gh.map (coeffValRingHomL hcoeff)).map AL.subtype = G₂.map ψ := by
    rw [Polynomial.map_map, hcompL, ← Polynomial.map_map, hGhmap]
  -- the reduction over the residue field of the coefficient field
  set r₀ : (ResidueField (coeffValRing A φ))[X] :=
    Gh.map (residue (coeffValRing A φ)) with hr₀def
  have hr₀K : r₀.map (coeffResidueHomK A φ)
      = (Gh.map (coeffValRingHomK A φ)).map (residue A) := map_coeffResidueHomK Gh
  have hr₀L : r₀.map (coeffResidueHomL hcoeff)
      = (Gh.map (coeffValRingHomL hcoeff)).map (residue AL) := map_coeffResidueHomL hcoeff Gh
  -- it is nonzero, since one coefficient of `G₂` is a unit
  have hGhcoeff : ∀ i, ((Gh.coeff i : coeffValRing A φ) : R) = G₂.coeff i := by
    intro i
    rw [← hGhmap, Polynomial.coeff_map]
    rfl
  have hunit : IsUnit ((Gh.map (coeffValRingHomK A φ)).coeff i₀) := by
    rw [Polynomial.coeff_map]
    refine (A.valuation_eq_one_iff _).mpr ?_
    rw [coe_coeffValRingHomK, hGhcoeff]
    exact hG2one
  have hmapK0 : (Gh.map (coeffValRingHomK A φ)).map (residue A) ≠ 0 := by
    intro h0
    have h1 : ((Gh.map (coeffValRingHomK A φ)).map (residue A)).coeff i₀ = 0 := by
      rw [h0, Polynomial.coeff_zero]
    rw [Polynomial.coeff_map] at h1
    exact (residue_ne_zero_iff_isUnit _).mpr hunit h1
  have hr₀0 : r₀ ≠ 0 := by
    intro h0
    rw [← hr₀K, h0, Polynomial.map_zero] at hmapK0
    exact hmapK0 rfl
  -- and `1` is a root of it, because it is on the near side
  have hinjK : Function.Injective (coeffResidueHomK A φ) := (coeffResidueHomK A φ).injective
  have hinjL : Function.Injective (coeffResidueHomL hcoeff) := (coeffResidueHomL hcoeff).injective
  have hevalK : ((Gh.map (coeffValRingHomK A φ)).map (residue A)).eval
      (residue A ⟨u, huA⟩) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    refine (residue_eq_zero_iff _).mpr ?_
    rw [coe_eval_eq, hmapK, hG2def, Polynomial.map_mul, Polynomial.eval_mul, hGu, mul_zero,
      map_zero]
    exact zero_lt_one
  have hroot₀ : r₀.eval 1 = 0 := by
    refine hinjK ?_
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hr₀K, map_one, ← hresu]
    exact hevalK
  have hrootL : ((Gh.map (coeffValRingHomL hcoeff)).map (residue AL)).eval 1 = 0 := by
    rw [← hr₀L, ← map_one (coeffResidueHomL hcoeff), Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hroot₀, map_zero]
  have hmapL0 : (Gh.map (coeffValRingHomL hcoeff)).map (residue AL) ≠ 0 := by
    rw [← hr₀L]
    exact Polynomial.map_ne_zero_iff hinjL |>.mpr hr₀0
  -- lift the root
  obtain ⟨x, hxroot, hxres⟩ := exists_root_residue_eq_of_map_ne_zero (A := AL)
    (by rw [hmapL]; exact IsAlgClosed.splits _) hmapL0 hrootL
  rw [hmapL] at hxroot
  have hGx : (G.map ψ).eval ((x : AL) : L) = 0 := by
    rw [hG2def, Polynomial.map_mul, Polynomial.eval_mul, Polynomial.map_C,
      Polynomial.eval_C] at hxroot
    exact (mul_eq_zero.mp hxroot).resolve_left (by
      rw [map_inv₀]
      exact inv_ne_zero he0L)
  have hrx : rv (A := AL) ((x : AL) : L) = 1 := by
    have h1 : rv (A := AL) ((x : AL) : L) = rv (A := AL) (((1 : AL) : L)) := by
      refine (rv_eq_iff_residue_eq (A := AL) isUnit_one).mpr ?_
      rw [hxres, map_one]
    rw [h1, OneMemClass.coe_one, map_one]
  refine ⟨ψ c + ψ s * ((x : AL) : L), by rw [← hGevalL]; exact hGx, ?_⟩
  rw [add_sub_cancel_left, map_mul, hrx, mul_one]

end ValuationSubring
