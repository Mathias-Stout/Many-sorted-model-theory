/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.AlgebraicBackground.RV

/-!
# Leading terms of a subfield

An embedding of fields `f : K →+* L` and a valuation subring `A` of `L` give a valuation subring
`A.comap f` of `K`, and the leading-term structures are compatible: `rv (f x)` depends only on
`rv x`, and the induced map `(A.comap f).RV → A.RV` is injective with image the leading terms of
the image of `f`.

This is what lets the extension lemmas of `Algebra/ACVF/ValuedField/Extend.lean` be applied *at a
subfield* rather than at a whole model. Their hypothesis is a map `fRV : AK.RV →*₀ AL.RV` defined on
the whole leading-term structure of the source, which a partial embedding cannot supply — but if the
source is taken to be the subfield being extended, its leading-term structure is exactly the part
where the map is known.

## Main definitions

* `ValuationSubring.rvComap` : the induced map of leading-term structures.
-/

@[expose] public section

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] (A : ValuationSubring L) {f : K →+* L}

/-- Comparison of valuations is the same computed in a subfield or in the ambient field. -/
theorem valuation_comap_le_iff (x y : K) :
    (A.comap f).valuation x ≤ (A.comap f).valuation y
      ↔ A.valuation (f x) ≤ A.valuation (f y) := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero, map_zero, nonpos_iff_eq_zero, nonpos_iff_eq_zero, Valuation.zero_iff,
      Valuation.zero_iff, map_eq_zero_iff f f.injective]
  · have hfy : f y ≠ 0 := fun h => hy ((map_eq_zero_iff f f.injective).mp h)
    have h1 : (A.comap f).valuation x ≤ (A.comap f).valuation y
        ↔ (A.comap f).valuation (x / y) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hy))]
    have h2 : A.valuation (f x) ≤ A.valuation (f y) ↔ A.valuation (f x / f y) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hfy))]
    rw [h1, h2, valuation_le_one_iff, valuation_le_one_iff, mem_comap, map_div₀]

theorem valuation_comap_lt_iff (x y : K) :
    (A.comap f).valuation x < (A.comap f).valuation y
      ↔ A.valuation (f x) < A.valuation (f y) := by
  rw [← not_le, ← not_le, valuation_comap_le_iff]

theorem valuation_comap_eq_iff (x y : K) :
    (A.comap f).valuation x = (A.comap f).valuation y
      ↔ A.valuation (f x) = A.valuation (f y) := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_comap_le_iff, valuation_comap_le_iff]

/-- Being a unit of the valuation ring is the same computed in a subfield or in the ambient
field. -/
theorem valuation_comap_eq_one_iff (x : K) :
    (A.comap f).valuation x = 1 ↔ A.valuation (f x) = 1 := by
  have h := valuation_comap_eq_iff A (f := f) x 1
  simpa using h

/-- **The fibers of `rv` are the same in a subfield and in the ambient field.** -/
theorem rv_comap_eq_iff (x y : K) :
    rv (A := A.comap f) x = rv (A := A.comap f) y ↔ rv (A := A) (f x) = rv (A := A) (f y) := by
  by_cases hx : x = 0
  · subst hx
    rw [rv_zero, map_zero, rv_zero, eq_comm, eq_comm (a := (0 : A.RV)), rv_eq_zero_iff,
      rv_eq_zero_iff, map_eq_zero_iff f f.injective]
  · have hfx : f x ≠ 0 := fun h => hx ((map_eq_zero_iff f f.injective).mp h)
    rw [rv_eq_iff_valuation_sub_lt (A := A.comap f) hx,
      rv_eq_iff_valuation_sub_lt (A := A) hfx, ← map_sub f,
      valuation_comap_lt_iff (A := A) (y - x) x]

/-- The leading-term map of a subfield, into that of the ambient field. -/
noncomputable def rvComap : (A.comap f).RV →*₀ A.RV where
  toFun ζ := rv (A := A) (f (Classical.choose (rv_surjective ζ)))
  map_zero' := by
    have h : rv (A := A.comap f) (Classical.choose (rv_surjective (A := A.comap f) 0))
        = rv (A := A.comap f) 0 := by
      rw [Classical.choose_spec (rv_surjective (A := A.comap f) 0), rv_zero]
    rw [(rv_comap_eq_iff A _ 0).mp h, map_zero, rv_zero]
  map_one' := by
    have h := Classical.choose_spec (rv_surjective (A := A.comap f) 1)
    have h1 : rv (A := A.comap f) (Classical.choose (rv_surjective (A := A.comap f) 1))
        = rv (A := A.comap f) 1 := by rw [h, map_one]
    rw [(rv_comap_eq_iff A _ 1).mp h1, map_one, map_one]
  map_mul' ζ η := by
    have hζ := Classical.choose_spec (rv_surjective (A := A.comap f) ζ)
    have hη := Classical.choose_spec (rv_surjective (A := A.comap f) η)
    have hζη := Classical.choose_spec (rv_surjective (A := A.comap f) (ζ * η))
    have h : rv (A := A.comap f) (Classical.choose (rv_surjective (A := A.comap f) (ζ * η)))
        = rv (A := A.comap f) (Classical.choose (rv_surjective (A := A.comap f) ζ)
            * Classical.choose (rv_surjective (A := A.comap f) η)) := by
      rw [hζη, map_mul, hζ, hη]
    rw [(rv_comap_eq_iff A _ _).mp h, map_mul, map_mul]

@[simp]
theorem rvComap_rv (x : K) : rvComap A (f := f) (rv (A := A.comap f) x) = rv (A := A) (f x) := by
  have h := Classical.choose_spec (rv_surjective (A := A.comap f) (rv (A := A.comap f) x))
  exact (rv_comap_eq_iff A _ x).mp h

theorem rvComap_injective : Function.Injective (rvComap A (f := f)) := by
  intro ζ η h
  obtain ⟨x, rfl⟩ := rv_surjective (A := A.comap f) ζ
  obtain ⟨y, rfl⟩ := rv_surjective (A := A.comap f) η
  rw [rvComap_rv, rvComap_rv] at h
  exact (rv_comap_eq_iff A x y).mpr h

/-! ### The residue field of a subfield

The valuation ring of a subfield maps into the ambient valuation ring, and the map detects units.
That is enough to carry the non-vanishing hypothesis of Rideau-Kikuchi's Proposition 2.1.5 between
the two — the hypothesis is about reductions of polynomials, and a reduction is nonzero exactly when
one of the coefficients is a unit, while a value at `a` is nonzero exactly when it is a unit. So the
two residue fields never have to be compared directly. -/

section Residue

open IsLocalRing Polynomial

/-- The valuation ring of a subfield, mapped into the ambient valuation ring. -/
def comapHom : (A.comap f) →+* A where
  toFun u := ⟨f (u : K), mem_comap.mp u.2⟩
  map_one' := Subtype.ext (map_one f)
  map_zero' := Subtype.ext (map_zero f)
  map_add' _ _ := Subtype.ext (map_add f _ _)
  map_mul' _ _ := Subtype.ext (map_mul f _ _)

@[simp]
theorem coe_comapHom (u : (A.comap f)) : ((comapHom A (f := f) u : A) : L) = f (u : K) := rfl

theorem comapHom_injective : Function.Injective (comapHom A (f := f)) := fun _ _ h =>
  Subtype.ext (f.injective (congrArg Subtype.val h))

/-- The map detects units, because comparison with `1` is the same on both sides. -/
theorem isUnit_comapHom_iff (u : (A.comap f)) : IsUnit (comapHom A (f := f) u) ↔ IsUnit u := by
  rw [A.valuation_eq_one_iff, (A.comap f).valuation_eq_one_iff, coe_comapHom,
    valuation_comap_eq_one_iff]

/-- A reduction is nonzero exactly when one of the coefficients is a unit. -/
theorem map_residue_ne_zero_iff (R : A[X]) :
    R.map (residue A) ≠ 0 ↔ ∃ i, IsUnit (R.coeff i) := by
  simp only [ne_eq, AddMonoidAlgebra.ext_iff, DFunLike.ext_iff, Polynomial.coeff_map,
    Polynomial.coeff_zero, not_forall, ← residue_ne_zero_iff_isUnit]

/-- A reduction is nonzero at the residue of `a` exactly when its value at `a` is a unit. -/
theorem eval_map_residue_ne_zero_iff (R : A[X]) (a : A) :
    (R.map (residue A)).eval (residue A a) ≠ 0 ↔ IsUnit (R.eval a) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, residue_ne_zero_iff_isUnit]

/-- **The non-vanishing hypothesis of Rideau-Kikuchi's Proposition 2.1.5 passes to a subfield.** If
no reduction of a polynomial over the ambient valuation ring with coefficients in `T` vanishes at
the residue of `f a`, then the same holds for polynomials over the valuation ring of the subfield.
The two residue fields are never compared: a reduction is nonzero exactly when a coefficient is a
unit, and its value at `a` is nonzero exactly when that value is a unit, and `comapHom` detects
units. -/
theorem eval_map_residue_ne_zero_of_comap (T : Subring L) (a : (A.comap f)) {n : ℕ}
    (hM : ∀ R : A[X], (∀ i, ((R.coeff i : A) : L) ∈ T) → R.natDegree < n →
      R.map (residue A) ≠ 0 →
      (R.map (residue A)).eval (residue A (comapHom A (f := f) a)) ≠ 0)
    (R : (A.comap f)[X]) (hRT : ∀ i, f ((R.coeff i : (A.comap f)) : K) ∈ T)
    (hRn : R.natDegree < n) (hRne : R.map (residue (A.comap f)) ≠ 0) :
    (R.map (residue (A.comap f))).eval (residue (A.comap f) a) ≠ 0 := by
  have hcoe : ∀ i, (((R.map (comapHom A (f := f))).coeff i : A) : L) ∈ T := fun i => by
    rw [Polynomial.coeff_map, coe_comapHom]
    exact hRT i
  have hdeg : (R.map (comapHom A (f := f))).natDegree < n := by
    rwa [Polynomial.natDegree_map_eq_of_injective (comapHom_injective A)]
  have hmapne : (R.map (comapHom A (f := f))).map (residue A) ≠ 0 := by
    obtain ⟨i, hi⟩ := (map_residue_ne_zero_iff _ R).mp hRne
    refine (map_residue_ne_zero_iff A _).mpr ⟨i, ?_⟩
    rw [Polynomial.coeff_map]
    exact (isUnit_comapHom_iff A _).mpr hi
  have hMapp := hM (R.map (comapHom A (f := f))) hcoe hdeg hmapne
  rw [eval_map_residue_ne_zero_iff] at hMapp ⊢
  rw [← isUnit_comapHom_iff A, show comapHom A (f := f) (R.eval a)
      = (R.map (comapHom A (f := f))).eval (comapHom A (f := f) a) by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]]
  exact hMapp

end Residue

end ValuationSubring
