/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.ValuedField.Comap
public import MultisortedLogic.Algebra.ACVF.ValuedField.ResidualReflect

/-!
# The residual algebraic case: transferring the degree of a residue

Rideau-Kikuchi's residual case at an algebraic residue asks that the far-side element be as
non-degenerate as the near-side one: `ResidualDeg ψ AL b n`, that no nonzero reduction of a
polynomial over the coefficient field of degree `< n` vanishes at `res b`. Unlike the
transcendental case this cannot be arranged by choosing `b` freely — `b` must be a root of the
image of the monic polynomial `a` satisfies — so it has to be *proved*.

It is true because a `CoeffReflect` makes the coefficient field's own valuation ring the same on
the two sides. Write `AR := AK.comap φ` for the valuation ring of the coefficient field. Both
`φ` and `ψ` restrict to **local** homomorphisms out of `AR`, so both induce maps of residue
fields

```
θK : ResidueField AR →+* ResidueField AK,   θL : ResidueField AR →+* ResidueField AL
```

and the reduction `p̄` of the monic polynomial lives over `ResidueField AR` itself. Viewing the
two residue fields as `ResidueField AR`-algebras along `θK` and `θL`, the near-side hypothesis
says exactly that `p̄` is the minimal polynomial of `res a`, hence irreducible; and an
irreducible monic polynomial vanishing at `res b` is the minimal polynomial there too. Its
degree is `n` on both sides, which is `ResidualDeg ψ AL b n`.

## Main definitions

* `ValuationSubring.coeffValRingHomK`, `ValuationSubring.coeffValRingHomL` : the two local
  homomorphisms out of the coefficient field's valuation ring.

## Main statements

* `ValuationSubring.residualDeg_transfer` : **the transfer**.
-/

@[expose] public section

namespace ValuationSubring

open Polynomial IsLocalRing

variable {K L R : Type*} [Field K] [Field L] [Field R]
variable {AK : ValuationSubring K} {AL : ValuationSubring L} {φ : R →+* K} {ψ : R →+* L}

/-! ### The coefficient field's valuation ring, read on both sides -/

/-- The valuation ring of the coefficient field, as the comap of the near-side one. -/
abbrev coeffValRing (AK : ValuationSubring K) (φ : R →+* K) : ValuationSubring R := AK.comap φ

/-- A `CoeffReflect` makes membership of the valuation ring the same on the two sides. -/
theorem mem_iff_of_coeffReflect (hcoeff : CoeffReflect φ ψ AK AL) (r : R) :
    φ r ∈ AK ↔ ψ r ∈ AL := by
  have h := hcoeff r 1
  rw [map_one, map_one, map_one, map_one] at h
  rw [← valuation_le_one_iff, ← valuation_le_one_iff]
  exact h

/-- The inclusion of the coefficient field's valuation ring into the near-side one. -/
def coeffValRingHomK (AK : ValuationSubring K) (φ : R →+* K) :
    coeffValRing AK φ →+* AK :=
  ((φ.comp (coeffValRing AK φ).subtype).codRestrict AK.toSubring fun x => x.2)

@[simp]
theorem coe_coeffValRingHomK (x : coeffValRing AK φ) :
    ((coeffValRingHomK AK φ x : AK) : K) = φ (x : R) := rfl

/-- The map of the coefficient field's valuation ring into the far-side one, which a
`CoeffReflect` makes land there. -/
def coeffValRingHomL (hcoeff : CoeffReflect φ ψ AK AL) : coeffValRing AK φ →+* AL :=
  ((ψ.comp (coeffValRing AK φ).subtype).codRestrict AL.toSubring
    fun x => (mem_iff_of_coeffReflect hcoeff _).mp x.2)

@[simp]
theorem coe_coeffValRingHomL (hcoeff : CoeffReflect φ ψ AK AL) (x : coeffValRing AK φ) :
    ((coeffValRingHomL hcoeff x : AL) : L) = ψ (x : R) := rfl

instance isLocalHom_coeffValRingHomK : IsLocalHom (coeffValRingHomK AK φ) where
  map_nonunit x hx := by
    rw [valuation_eq_one_iff, valuation_comap_eq_one_iff]
    rw [valuation_eq_one_iff] at hx
    exact hx

theorem isLocalHom_coeffValRingHomL (hcoeff : CoeffReflect φ ψ AK AL) :
    IsLocalHom (coeffValRingHomL hcoeff) where
  map_nonunit x hx := by
    rw [valuation_eq_one_iff] at hx
    rw [valuation_eq_one_iff, valuation_comap_eq_one_iff]
    have h1 := hcoeff (x : R) 1
    have h2 := hcoeff 1 (x : R)
    rw [map_one, map_one, map_one, map_one] at h1 h2
    have hL1 : AL.valuation (ψ (x : R)) ≤ 1 := by
      rw [coe_coeffValRingHomL hcoeff x] at hx
      exact le_of_eq hx
    have hL2 : (1 : AL.ValueGroup) ≤ AL.valuation (ψ (x : R)) := by
      rw [coe_coeffValRingHomL hcoeff x] at hx
      exact le_of_eq hx.symm
    exact le_antisymm (h1.mpr hL1) (h2.mpr hL2)

/-! ### The induced maps of residue fields -/

/-- The map of residue fields induced by the inclusion of the coefficient field's valuation ring
into the near-side one. -/
noncomputable def coeffResidueHomK (AK : ValuationSubring K) (φ : R →+* K) :
    ResidueField (coeffValRing AK φ) →+* ResidueField AK :=
  ResidueField.map (coeffValRingHomK AK φ)

/-- The map of residue fields induced by the far-side one. -/
noncomputable def coeffResidueHomL (hcoeff : CoeffReflect φ ψ AK AL) :
    ResidueField (coeffValRing AK φ) →+* ResidueField AL :=
  letI := isLocalHom_coeffValRingHomL hcoeff
  ResidueField.map (coeffValRingHomL hcoeff)

theorem map_coeffResidueHomK (S : (coeffValRing AK φ)[X]) :
    (S.map (residue (coeffValRing AK φ))).map (coeffResidueHomK AK φ)
      = (S.map (coeffValRingHomK AK φ)).map (residue AK) := by
  rw [Polynomial.map_map, Polynomial.map_map, coeffResidueHomK,
    ResidueField.map_comp_residue]

theorem map_coeffResidueHomL (hcoeff : CoeffReflect φ ψ AK AL) (S : (coeffValRing AK φ)[X]) :
    (S.map (residue (coeffValRing AK φ))).map (coeffResidueHomL hcoeff)
      = (S.map (coeffValRingHomL hcoeff)).map (residue AL) := by
  have := isLocalHom_coeffValRingHomL hcoeff
  rw [Polynomial.map_map, Polynomial.map_map, coeffResidueHomL,
    ResidueField.map_comp_residue]

/-! ### The transfer -/

/-- **The degree of the residue transfers.** If `a` and `b` are roots of the two readings of the
same monic polynomial `P₀` of degree `n` over the valuation ring of the coefficient field, and no
nonzero reduction of a polynomial of degree `< n` over the coefficient field vanishes at `res a`,
then none vanishes at `res b` either.

The reduction of `P₀` is the minimal polynomial of `res a` over the residue field of the
coefficient field's valuation ring — that is exactly what the hypothesis says — hence
irreducible; and a monic irreducible polynomial vanishing at `res b` is the minimal polynomial
there too, so its degree `n` bounds every other relation below. -/
theorem residualDeg_transfer (hcoeff : CoeffReflect φ ψ AK AL) {a : AK} {b : AL} {n : ℕ}
    {P₀ : (coeffValRing AK φ)[X]} (hP₀ : P₀.Monic) (hP₀n : P₀.natDegree = n)
    (hPa : (P₀.map (coeffValRingHomK AK φ)).eval a = 0)
    (hPb : (P₀.map (coeffValRingHomL hcoeff)).eval b = 0)
    (hdegK : ResidualDeg φ AK a n) :
    ResidualDeg ψ AL b n := by
  classical
  have := isLocalHom_coeffValRingHomL hcoeff
  let : Algebra (ResidueField (coeffValRing AK φ)) (ResidueField AK) :=
    (coeffResidueHomK AK φ).toAlgebra
  let : Algebra (ResidueField (coeffValRing AK φ)) (ResidueField AL) :=
    (coeffResidueHomL hcoeff).toAlgebra
  set p : (ResidueField (coeffValRing AK φ))[X] := P₀.map (residue (coeffValRing AK φ)) with hpdef
  have hpm : p.Monic := hP₀.map _
  have hpn : p.natDegree = n := by rw [hpdef, hP₀.natDegree_map, hP₀n]
  have haevalK : ∀ (q : (ResidueField (coeffValRing AK φ))[X]) (x : ResidueField AK),
      aeval x q = (q.map (coeffResidueHomK AK φ)).eval x := fun q x => by
    rw [aeval_def, eval₂_eq_eval_map]; rfl
  have haevalL : ∀ (q : (ResidueField (coeffValRing AK φ))[X]) (x : ResidueField AL),
      aeval x q = (q.map (coeffResidueHomL hcoeff)).eval x := fun q x => by
    rw [aeval_def, eval₂_eq_eval_map]; rfl
  have hrootK : aeval (residue AK a) p = 0 := by
    rw [haevalK, hpdef, map_coeffResidueHomK, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hPa, map_zero]
  have hrootL : aeval (residue AL b) p = 0 := by
    rw [haevalL, hpdef, map_coeffResidueHomL, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hPb, map_zero]
  -- the near-side hypothesis, read as minimality over the residue field of the coefficients
  have hminK : ∀ q : (ResidueField (coeffValRing AK φ))[X], q ≠ 0 → q.natDegree < n →
      aeval (residue AK a) q ≠ 0 := by
    intro q hq0 hqn hcon
    obtain ⟨S, hSmap, hSdeg⟩ := Polynomial.exists_degree_eq_of_mem_lifts
      ((Polynomial.lifts_iff_coeff_lifts _).mpr fun i =>
        Ideal.Quotient.mk_surjective (q.coeff i))
    have hSmap' : S.map (residue (coeffValRing AK φ)) = q := hSmap
    have hSn : S.natDegree = q.natDegree := Polynomial.natDegree_eq_of_degree_eq hSdeg
    refine hdegK (S.map (coeffValRingHomK AK φ)) (fun i => ?_) ?_ ?_ ?_
    · rw [Polynomial.coeff_map, coe_coeffValRingHomK]
      exact ⟨_, rfl⟩
    · exact lt_of_le_of_lt (le_trans Polynomial.natDegree_map_le (le_of_eq hSn)) hqn
    · rw [← map_coeffResidueHomK, hSmap']
      exact Polynomial.map_ne_zero hq0
    · rw [← map_coeffResidueHomK, hSmap', ← haevalK]
      exact hcon
  have hintK : IsIntegral (ResidueField (coeffValRing AK φ)) (residue AK a) := ⟨p, hpm, hrootK⟩
  have hpmin : p = minpoly (ResidueField (coeffValRing AK φ)) (residue AK a) := by
    refine minpoly.unique _ _ hpm hrootK fun q hqm hq0 => ?_
    by_contra hlt
    push Not at hlt
    exact hminK q hqm.ne_zero
      (by rw [← hpn]; exact Polynomial.natDegree_lt_natDegree hqm.ne_zero hlt) hq0
  have hirr : Irreducible p := hpmin ▸ minpoly.irreducible hintK
  have hpminL : p = minpoly (ResidueField (coeffValRing AK φ)) (residue AL b) :=
    minpoly.eq_of_irreducible_of_monic hirr hrootL hpm
  -- the far side
  intro RQ hRQ hRQn hRQne hcon
  have hlifts : RQ ∈ Polynomial.lifts (coeffValRingHomL hcoeff) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    obtain ⟨r, hr⟩ := hRQ i
    have hrK : φ r ∈ AK := (mem_iff_of_coeffReflect hcoeff r).mpr (by rw [hr]; exact (RQ.coeff i).2)
    exact ⟨⟨r, hrK⟩, Subtype.ext hr⟩
  obtain ⟨S, hSmap, hSdeg⟩ := Polynomial.exists_degree_eq_of_mem_lifts hlifts
  have hSn : S.natDegree = RQ.natDegree := Polynomial.natDegree_eq_of_degree_eq hSdeg
  set q : (ResidueField (coeffValRing AK φ))[X] := S.map (residue (coeffValRing AK φ)) with hqdef
  have hqmap : q.map (coeffResidueHomL hcoeff) = RQ.map (residue AL) := by
    rw [hqdef, map_coeffResidueHomL, hSmap]
  have hq0 : q ≠ 0 := fun h0 => hRQne (by rw [← hqmap, h0, Polynomial.map_zero])
  have hqn : q.natDegree < n :=
    lt_of_le_of_lt (le_trans Polynomial.natDegree_map_le (le_of_eq hSn)) hRQn
  have hqroot : aeval (residue AL b) q = 0 := by
    rw [haevalL, hqmap]
    exact hcon
  have hdvd : p ∣ q := hpminL ▸ minpoly.dvd _ _ hqroot
  exact absurd (le_trans (le_of_eq hpn.symm) (Polynomial.natDegree_le_of_dvd hdvd hq0))
    (not_le.mpr hqn)

end ValuationSubring
