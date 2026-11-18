/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Theory.Structure
public import MultisortedLogic.Algebra.ACVF.ValuedField.Residue
public import MultisortedLogic.Algebra.ACVF.ValuedField.Extend

/-!
# The residue field inside the leading-term structure

The `RV` sort of `L_RV` does not merely *have* a residue field somewhere behind it: it **contains**
one. The fiber of `rvVal` over `1`, together with `0`, is a copy of `ResidueField A` — `IsResidue`
in `Algebra/ACVF/Theory/Structure.lean` — and on it the multiplication of `A.RV` and the addition
`rvAdd` are the residue field's own operations.

This is what justifies calling the language *leading terms*: the residue field needs no sort of
its own, and, more to the point for the quantifier elimination, an `L_RV`-embedding automatically
carries residues to residues. Rideau-Kikuchi's Proposition 2.1.5 computes `rv (Q a)` from the
residue of `a`; `resEmbed` is what lets that computation be transported along an embedding without
ever mentioning a residue field map.

## Main definitions

* `Language.resEmbed` : the map `ResidueField A → A.RV`.

## Main statements

* `Language.resEmbed_residue` : `resEmbed (res x) = rv x` for a unit `x` — the defining property.
* `Language.resEmbed_injective`, `Language.isResidue_iff_mem_range` : it is a bijection onto the
  residue part of `A.RV`.
* `Language.resEmbed_add` : it turns the addition of the residue field into `rvAdd`.
* `Language.resRingHom` : the homomorphism of residue fields induced by an embedding, assuming
  only monotonicity for `val` and compatibility with `rvAdd`.
* `Language.rv_eval_eq_of_residual_transfer`, `Language.rvTypeEq_of_residual` : Rideau-Kikuchi's
  Proposition 2.1.5(3), the purely residual extension step.
-/

@[expose] public section

namespace ManySorted.Language

open Arity ValuationSubring IsLocalRing

universe u

variable {F : Type u} [Field F] (A : ValuationSubring F)

/-- A choice of preimage in the valuation ring for an element of the residue field. -/
noncomputable def residueSection (ρ : ResidueField A) : A := (residue_surjective ρ).choose

@[simp]
theorem residue_residueSection (ρ : ResidueField A) :
    residue A (residueSection A ρ) = ρ := (residue_surjective ρ).choose_spec

open scoped Classical in
/-- **The residue field inside `A.RV`.** A nonzero residue is the leading term of any of its
unit representatives; the zero residue is the zero of `A.RV`. -/
noncomputable def resEmbed (ρ : ResidueField A) : A.RV :=
  if ρ = 0 then 0 else rv (A := A) ((residueSection A ρ : A) : F)

variable {A}

@[simp]
theorem resEmbed_zero : resEmbed A 0 = 0 := by rw [resEmbed, ite_eq_left rfl]

/-- **The defining property.** On a unit, `resEmbed ∘ residue` is `rv`. -/
theorem resEmbed_residue {x : A} (hx : IsUnit x) :
    resEmbed A (residue A x) = rv (A := A) ((x : A) : F) := by
  classical
  have hne : residue A x ≠ 0 := (residue_ne_zero_iff_isUnit x).mpr hx
  rw [resEmbed, ite_eq_right hne]
  have hres : residue A (residueSection A (residue A x)) = residue A x :=
    residue_residueSection A _
  exact (rv_eq_iff_residue_eq hx).mpr hres

@[simp]
theorem resEmbed_eq_zero_iff {ρ : ResidueField A} : resEmbed A ρ = 0 ↔ ρ = 0 := by
  classical
  constructor
  · intro h
    by_contra hρ
    rw [resEmbed, ite_eq_right hρ, rv_eq_zero_iff] at h
    have hu : IsUnit (residueSection A ρ) := by
      rw [← residue_ne_zero_iff_isUnit, residue_residueSection]
      exact hρ
    exact absurd (Subtype.ext h : residueSection A ρ = 0) (by simpa using hu.ne_zero)
  · rintro rfl
    exact resEmbed_zero

/-- Everything in the image is a residue. -/
theorem isResidue_resEmbed (ρ : ResidueField A) : IsResidue (A := A) (resEmbed A ρ) := by
  classical
  by_cases hρ : ρ = 0
  · rw [hρ, resEmbed_zero]
    exact isResidue_zero A
  · have hu : IsUnit (residueSection A ρ) := by
      rw [← residue_ne_zero_iff_isUnit, residue_residueSection]
      exact hρ
    rw [resEmbed, ite_eq_right hρ]
    exact isResidue_rv A ((A.valuation_eq_one_iff _).mp hu)

/-- Conversely, every residue is in the image: `resEmbed` is a bijection onto `IsResidue`. -/
theorem isResidue_iff_mem_range {ξ : A.RV} :
    IsResidue (A := A) ξ ↔ ∃ ρ : ResidueField A, resEmbed A ρ = ξ := by
  constructor
  · rintro (h | h)
    · obtain ⟨x, rfl⟩ := rv_surjective ξ
      rw [rvVal_rv] at h
      have hxA : x ∈ A := A.mem_of_valuation_le_one x (le_of_eq h)
      refine ⟨residue A ⟨x, hxA⟩, resEmbed_residue ?_⟩
      exact (A.valuation_eq_one_iff ⟨x, hxA⟩).mpr h
    · rw [rvVal_eq_zero_iff] at h
      exact ⟨0, by rw [resEmbed_zero, h]⟩
  · rintro ⟨ρ, rfl⟩
    exact isResidue_resEmbed ρ

theorem resEmbed_injective : Function.Injective (resEmbed A) := by
  classical
  intro ρ σ h
  by_cases hρ : ρ = 0
  · subst hρ
    rw [resEmbed_zero] at h
    exact ((resEmbed_eq_zero_iff (ρ := σ)).mp h.symm).symm
  · have hσ : σ ≠ 0 := fun hs => hρ (by rwa [hs, resEmbed_zero, resEmbed_eq_zero_iff] at h)
    have hur : IsUnit (residueSection A ρ) := by
      rw [← residue_ne_zero_iff_isUnit, residue_residueSection]; exact hρ
    have hus : IsUnit (residueSection A σ) := by
      rw [← residue_ne_zero_iff_isUnit, residue_residueSection]; exact hσ
    rw [resEmbed, ite_eq_right hρ, resEmbed, ite_eq_right hσ] at h
    rw [← residue_residueSection A ρ, ← residue_residueSection A σ]
    exact (rv_eq_iff_residue_eq hus).mp h

@[simp]
theorem resEmbed_one : resEmbed A (1 : ResidueField A) = 1 := by
  have h := resEmbed_residue (A := A) (x := 1) isUnit_one
  rwa [map_one, OneMemClass.coe_one, map_one] at h

theorem resEmbed_mul (ρ σ : ResidueField A) :
    resEmbed A (ρ * σ) = resEmbed A ρ * resEmbed A σ := by
  classical
  by_cases hρ : ρ = 0
  · rw [hρ, zero_mul, resEmbed_zero, zero_mul]
  by_cases hσ : σ = 0
  · rw [hσ, mul_zero, resEmbed_zero, mul_zero]
  have hur : IsUnit (residueSection A ρ) := by
    rw [← residue_ne_zero_iff_isUnit, residue_residueSection]; exact hρ
  have hus : IsUnit (residueSection A σ) := by
    rw [← residue_ne_zero_iff_isUnit, residue_residueSection]; exact hσ
  conv_lhs => rw [← residue_residueSection A ρ, ← residue_residueSection A σ, ← map_mul]
  rw [resEmbed_residue (hur.mul hus), resEmbed, ite_eq_right hρ, resEmbed, ite_eq_right hσ]
  push_cast
  rw [map_mul]

/-- **The negation transfers.** The negation of the residue field is `rvNeg`. -/
theorem resEmbed_neg (ρ : ResidueField A) :
    resEmbed A (-ρ) = rvNeg A (resEmbed A ρ) := by
  have hone : ((-1 : A) : F) = -1 := by push_cast; ring
  rw [show -ρ = (-1 : ResidueField A) * ρ by ring,
    show (-1 : ResidueField A) = residue A (-1) by rw [map_neg, map_one],
    resEmbed_mul, resEmbed_residue isUnit_one.neg, hone, rvNeg]

/-- **The addition transfers.** The addition of the residue field is `rvAdd`. -/
theorem resEmbed_add (ρ σ : ResidueField A) :
    resEmbed A (ρ + σ) = rvAdd A (resEmbed A ρ) (resEmbed A σ) := by
  classical
  by_cases hρ : ρ = 0
  · rw [hρ, zero_add, resEmbed_zero, rvAdd_zero_left A (isResidue_resEmbed σ)]
  by_cases hσ : σ = 0
  · rw [hσ, add_zero, resEmbed_zero, rvAdd_zero_right A (isResidue_resEmbed ρ)]
  set x := residueSection A ρ with hx
  set y := residueSection A σ with hy
  have hur : IsUnit x := by
    rw [hx, ← residue_ne_zero_iff_isUnit, residue_residueSection]; exact hρ
  have hus : IsUnit y := by
    rw [hy, ← residue_ne_zero_iff_isUnit, residue_residueSection]; exact hσ
  have hvx : A.valuation ((x : A) : F) = 1 := (A.valuation_eq_one_iff x).mp hur
  have hvy : A.valuation ((y : A) : F) = 1 := (A.valuation_eq_one_iff y).mp hus
  have hρx : resEmbed A ρ = rv (A := A) ((x : A) : F) := by rw [resEmbed, ite_eq_right hρ]
  have hσy : resEmbed A σ = rv (A := A) ((y : A) : F) := by rw [resEmbed, ite_eq_right hσ]
  have hsum : ρ + σ = residue A (x + y) := by
    rw [map_add, residue_residueSection, residue_residueSection]
  by_cases hu : IsUnit (x + y)
  · -- the residues do not cancel
    have hv : A.valuation (((x + y : A) : F)) = 1 := (A.valuation_eq_one_iff _).mp hu
    rw [hsum, resEmbed_residue hu, hρx, hσy]
    have : ((x + y : A) : F) = ((x : A) : F) + ((y : A) : F) := by push_cast; ring
    rw [this] at hv ⊢
    exact (rvAdd_rv_rv A hvx hvy hv).symm
  · -- the residues cancel: both sides are the residue `0`
    have hzero : residue A (x + y) = 0 := by
      by_contra hne
      exact hu ((residue_ne_zero_iff_isUnit _).mp hne)
    rw [hsum, hzero, resEmbed_zero, hρx, hσy]
    by_contra hcon
    -- a nonzero value would have to be the leading term of `x + y`, which is not a unit
    have hne : rvAdd A (rv (A := A) ((x : A) : F)) (rv (A := A) ((y : A) : F)) ≠ 0 :=
      fun hh => hcon hh.symm
    have heq := rvAdd_eq_rv_add A hvx hvy hne
    have hres := isResidue_rvAdd A (rv (A := A) ((x : A) : F)) (rv (A := A) ((y : A) : F))
    rw [heq] at hres hne
    have hxy : ((x : A) : F) + ((y : A) : F) = ((x + y : A) : F) := by push_cast; ring
    rw [hxy] at hres hne
    rcases hres with h | h
    · rw [rvVal_rv] at h
      exact hu ((A.valuation_eq_one_iff _).mpr h)
    · exact hne (by rwa [rvVal_eq_zero_iff] at h)

variable (A)

section Transfer

/-!
### The residue field map induced by an embedding

An `L_RV`-embedding is monotone for `val` and respects `rvAdd`. That is already enough to
induce a homomorphism of residue fields, with no residue field map assumed: monotonicity pins
down the fiber of `rvVal` over `1`, so the embedding carries `IsResidue` to `IsResidue`, and
`resEmbed` transports the operations.
-/

variable {A}
variable {L : Type*} [Field L] {AL : ValuationSubring L} {fRV : A.RV →*₀ AL.RV}

/-- Monotonicity for `rvVal` pins down the unit fiber, because `1` is in it on both sides. -/
theorem rvVal_eq_one_iff_of_mono
    (hmono : ∀ ξ η : A.RV, rvVal ξ < rvVal η ↔ rvVal (fRV ξ) < rvVal (fRV η))
    (ξ : A.RV) : rvVal (fRV ξ) = 1 ↔ rvVal ξ = 1 := by
  have hone : rvVal (A := A) 1 = 1 := map_one _
  have hone' : rvVal (A := AL) (fRV 1) = 1 := by rw [map_one, map_one]
  have hlt := hmono ξ 1
  have hgt := hmono 1 ξ
  rw [hone, hone'] at hlt hgt
  constructor
  · intro h
    rcases lt_trichotomy (rvVal (A := A) ξ) 1 with hc | hc | hc
    · exact absurd (hlt.mp hc) (by rw [h]; exact lt_irrefl _)
    · exact hc
    · exact absurd (hgt.mp hc) (by rw [h]; exact lt_irrefl _)
  · intro h
    rcases lt_trichotomy (rvVal (A := AL) (fRV ξ)) 1 with hc | hc | hc
    · exact absurd (hlt.mpr hc) (by rw [h]; exact lt_irrefl _)
    · exact hc
    · exact absurd (hgt.mpr hc) (by rw [h]; exact lt_irrefl _)

/-- Hence the embedding carries the residue field into the residue field. -/
theorem isResidue_map_of_mono
    (hmono : ∀ ξ η : A.RV, rvVal ξ < rvVal η ↔ rvVal (fRV ξ) < rvVal (fRV η))
    {ξ : A.RV} (hξ : IsResidue (A := A) ξ) : IsResidue (A := AL) (fRV ξ) := by
  rcases hξ with h | h
  · exact Or.inl ((rvVal_eq_one_iff_of_mono hmono ξ).mpr h)
  · rw [rvVal_eq_zero_iff] at h
    rw [h, map_zero]
    exact Or.inr (map_zero _)

/-- The map of residue fields induced by `fRV`, through `resEmbed` on both sides. It is pinned
down by `resEmbed_resMap`; the `0` is junk, used only when `fRV` is not monotone. -/
noncomputable def resMap (fRV : A.RV →*₀ AL.RV) (ρ : ResidueField A) : ResidueField AL :=
  haveI := Classical.dec (∃ σ : ResidueField AL, resEmbed AL σ = fRV (resEmbed A ρ))
  if h : ∃ σ : ResidueField AL, resEmbed AL σ = fRV (resEmbed A ρ) then h.choose else 0

theorem resEmbed_resMap
    (hmono : ∀ ξ η : A.RV, rvVal ξ < rvVal η ↔ rvVal (fRV ξ) < rvVal (fRV η))
    (ρ : ResidueField A) : resEmbed AL (resMap fRV ρ) = fRV (resEmbed A ρ) := by
  have h : ∃ σ : ResidueField AL, resEmbed AL σ = fRV (resEmbed A ρ) :=
    isResidue_iff_mem_range.mp (isResidue_map_of_mono hmono (isResidue_resEmbed ρ))
  rw [resMap, dite_eq_left h]
  exact h.choose_spec

/-- **The induced homomorphism of residue fields.** Nothing beyond monotonicity for `val` and
compatibility with `rvAdd` is assumed: the residue field is definable inside `RV`, so an
`L_RV`-embedding induces a map of residue fields whether or not one was given. -/
noncomputable def resRingHom (fRV : A.RV →*₀ AL.RV)
    (hmono : ∀ ξ η : A.RV, rvVal ξ < rvVal η ↔ rvVal (fRV ξ) < rvVal (fRV η))
    (hadd : ∀ ξ η : A.RV, fRV (rvAdd A ξ η) = rvAdd AL (fRV ξ) (fRV η)) :
    ResidueField A →+* ResidueField AL where
  toFun := resMap fRV
  map_zero' := resEmbed_injective (by
    rw [resEmbed_resMap hmono, resEmbed_zero, resEmbed_zero, map_zero])
  map_one' := resEmbed_injective (by
    rw [resEmbed_resMap hmono, resEmbed_one, resEmbed_one, map_one])
  map_mul' ρ σ := resEmbed_injective (by
    rw [resEmbed_resMap hmono, resEmbed_mul, resEmbed_mul, map_mul,
      resEmbed_resMap hmono, resEmbed_resMap hmono])
  map_add' ρ σ := resEmbed_injective (by
    rw [resEmbed_resMap hmono, resEmbed_add, resEmbed_add, hadd,
      resEmbed_resMap hmono, resEmbed_resMap hmono])

@[simp]
theorem resRingHom_apply
    (hmono : ∀ ξ η : A.RV, rvVal ξ < rvVal η ↔ rvVal (fRV ξ) < rvVal (fRV η))
    (hadd : ∀ ξ η : A.RV, fRV (rvAdd A ξ η) = rvAdd AL (fRV ξ) (fRV η))
    (ρ : ResidueField A) : resRingHom fRV hmono hadd ρ = resMap fRV ρ := rfl

/-! ### Transporting residues along the embedding -/

variable (hmono : ∀ ξ η : A.RV, rvVal ξ < rvVal η ↔ rvVal (fRV ξ) < rvVal (fRV η))

include hmono

/-- Being a unit of the valuation ring is preserved. -/
theorem isUnit_iff_of_mono {x : A} {y : AL}
    (h : fRV (rv (A := A) ((x : A) : F)) = rv (A := AL) ((y : AL) : L)) :
    IsUnit x ↔ IsUnit y := by
  rw [A.valuation_eq_one_iff, AL.valuation_eq_one_iff, ← rvVal_rv (A := A) ((x : A) : F),
    ← rvVal_rv (A := AL) ((y : AL) : L), ← h]
  exact (rvVal_eq_one_iff_of_mono hmono _).symm

/-- **Residues transport.** If `fRV` matches the leading terms of `x` and `y`, the induced map
of residue fields matches their residues — and conversely on units. This is the bridge that
lets a residue field computation be carried along an `L_RV`-embedding. -/
theorem resMap_residue {x : A} {y : AL}
    (h : fRV (rv (A := A) ((x : A) : F)) = rv (A := AL) ((y : AL) : L)) :
    resMap fRV (residue A x) = residue AL y := by
  by_cases hu : IsUnit x
  · have hv : IsUnit y := (isUnit_iff_of_mono hmono h).mp hu
    refine resEmbed_injective ?_
    rw [resEmbed_resMap hmono, resEmbed_residue hu, resEmbed_residue hv, h]
  · have hv : ¬ IsUnit y := fun hv => hu ((isUnit_iff_of_mono hmono h).mpr hv)
    rw [← residue_ne_zero_iff_isUnit, not_not] at hu hv
    rw [hu, hv]
    refine resEmbed_injective ?_
    rw [resEmbed_resMap hmono, resEmbed_zero, resEmbed_zero, map_zero]

/-- The converse on units: matching residues give matching leading terms. -/
theorem rv_eq_of_resMap_residue {x : A} {y : AL} (hu : IsUnit x) (hv : IsUnit y)
    (h : resMap fRV (residue A x) = residue AL y) :
    fRV (rv (A := A) ((x : A) : F)) = rv (A := AL) ((y : AL) : L) := by
  rw [← resEmbed_residue hu, ← resEmbed_residue hv, ← h, resEmbed_resMap hmono]

/-! ### Proposition 2.1.5(3), the purely residual extension step -/

open Arity Polynomial

variable {R : Type*} [Field R] {φ : R →+* F} {ψ : R →+* L}

omit hmono in
/-- **Proposition 2.1.5(3), transfer step (purely residual).** If `res a` has degree at least `n`
over the residues of the coefficient field, then for polynomials of degree `< n` nothing cancels,
and the leading term of `Q a` is determined by those of the coefficients together with the residue
of `a`.

As in the ramified case, only the `K` side carries a hypothesis: monotonicity transports the
choice of dominant coefficient, and the induced map of residue fields — which exists because the
residue field is definable inside `RV` — transports the residue computation, so `b` needs no
assumption of its own. -/
theorem rv_eval_eq_of_residual_transfer {a : A} {b : AL} {n : ℕ}
    (θ : ResidueField A →+* ResidueField AL)
    (hθ : ∀ (x : A) (y : AL),
      fRV (rv (A := A) ((x : A) : F)) = rv (A := AL) ((y : AL) : L) →
      θ (residue A x) = residue AL y)
    (hθ' : ∀ (x : A) (y : AL), IsUnit x → IsUnit y →
      θ (residue A x) = residue AL y →
      fRV (rv (A := A) ((x : A) : F)) = rv (A := AL) ((y : AL) : L))
    (hmono : ∀ r r' : R,
      AL.valuation (ψ r) < AL.valuation (ψ r') → A.valuation (φ r) < A.valuation (φ r'))
    (hcompat : ∀ r : R, fRV (rv (A := A) (φ r)) = rv (A := AL) (ψ r))
    (hab : fRV (rv (A := A) ((a : A) : F)) = rv (A := AL) ((b : AL) : L))
    (hdeg : ∀ RQ : A[X], (∀ i, ((RQ.coeff i : A) : F) ∈ φ.fieldRange) → RQ.natDegree < n →
      RQ.map (residue A) ≠ 0 → (RQ.map (residue A)).eval (residue A a) ≠ 0) :
    ∀ Q : R[X], Q.natDegree < n →
      fRV (rv (A := A) (evalOn φ ((a : A) : F) Q))
        = rv (A := AL) (evalOn' ψ ((b : AL) : L) Q) := by
  classical
  intro Q hQn
  by_cases hQ : Q = 0
  · simp [hQ]
  have hevK : evalOn φ ((a : A) : F) Q = (Q.map φ).eval ((a : A) : F) :=
    (Polynomial.eval_map _ _).symm
  have hevL : evalOn' ψ ((b : AL) : L) Q = (Q.map ψ).eval ((b : AL) : L) :=
    (Polynomial.eval_map _ _).symm
  have hQK : Q.map φ ≠ 0 := Polynomial.map_ne_zero hQ
  -- the coefficient of largest valuation, chosen on the `K` side
  obtain ⟨i₀, hi₀, hmaxK⟩ := Finset.exists_max_image (Q.map φ).support
    (fun i => A.valuation ((Q.map φ).coeff i)) (Polynomial.support_nonempty.mpr hQK)
  have hi₀Q : i₀ ∈ Q.support := (mem_support_map_of_injective φ.injective).mp hi₀
  have hi₀L : i₀ ∈ (Q.map ψ).support := (mem_support_map_of_injective ψ.injective).mpr hi₀Q
  -- monotonicity transports the choice to the `L` side
  have hmaxL : ∀ i ∈ (Q.map ψ).support,
      AL.valuation ((Q.map ψ).coeff i) ≤ AL.valuation ((Q.map ψ).coeff i₀) := by
    intro i hi
    by_contra hlt
    rw [not_le] at hlt
    refine absurd (hmaxK i ((mem_support_map_of_injective φ.injective).mpr
      ((mem_support_map_of_injective ψ.injective).mp hi))) (not_le.mpr ?_)
    have h₁ : AL.valuation (ψ (Q.coeff i₀)) < AL.valuation (ψ (Q.coeff i)) := by
      simpa [Polynomial.coeff_map] using hlt
    simpa [Polynomial.coeff_map] using hmono (Q.coeff i₀) (Q.coeff i) h₁
  -- scale by that coefficient on each side
  obtain ⟨RK, hcK, hdegK, honeK, hevalK⟩ := exists_toSubring_of_max hi₀ hmaxK
  obtain ⟨RL, hcL, -, -, hevalL⟩ := exists_toSubring_of_max hi₀L hmaxL
  -- the two scaled polynomials correspond coefficientwise
  have hcoeff : ∀ i, fRV (rv (A := A) ((RK.coeff i : A) : F))
      = rv (A := AL) ((RL.coeff i : AL) : L) := by
    intro i
    have hK : ((RK.coeff i : A) : F) = φ ((Q.coeff i₀)⁻¹ * Q.coeff i) := by
      rw [hcK i]; simp [Polynomial.coeff_map]
    have hL : ((RL.coeff i : AL) : L) = ψ ((Q.coeff i₀)⁻¹ * Q.coeff i) := by
      rw [hcL i]; simp [Polynomial.coeff_map]
    rw [hK, hL, hcompat]
  -- so do their reductions, and so do their values at `a` and `b`
  have hres : ∀ i, θ (residue A (RK.coeff i)) = residue AL (RL.coeff i) :=
    fun i => hθ _ _ (hcoeff i)
  have hpoly : RK.map (θ.comp (residue A)) = RL.map (residue AL) := by
    ext i
    simp only [Polynomial.coeff_map, RingHom.comp_apply]
    exact hres i
  have hevalres : θ (residue A (RK.eval a)) = residue AL (RL.eval b) := by
    have hab' : θ (residue A a) = residue AL b := hθ _ _ hab
    rw [← Polynomial.eval₂_at_apply (residue A) a, Polynomial.hom_eval₂,
      ← Polynomial.eval_map, hpoly, hab', Polynomial.eval_map, Polynomial.eval₂_at_apply]
  -- `RK a` is a unit, by the degree hypothesis
  have hRKF : ∀ i, ((RK.coeff i : A) : F) ∈ φ.fieldRange := by
    intro i
    rw [hcK i]
    simp only [Polynomial.coeff_map]
    exact ⟨(Q.coeff i₀)⁻¹ * Q.coeff i, by simp⟩
  have hRKne : RK.map (residue A) ≠ 0 := by
    intro h0
    have : (RK.map (residue A)).coeff i₀ = 0 := by rw [h0, Polynomial.coeff_zero]
    rw [Polynomial.coeff_map, honeK, map_one] at this
    exact one_ne_zero this
  have hRKn : RK.natDegree < n := by
    rw [hdegK, Polynomial.natDegree_map]; exact hQn
  have hnv := hdeg RK hRKF hRKn hRKne
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, residue_ne_zero_iff_isUnit] at hnv
  -- hence so is `RL b`, since a homomorphism of fields is injective
  have hunitL : IsUnit (RL.eval b) := by
    rw [← residue_ne_zero_iff_isUnit, ← hevalres]
    intro h0
    exact absurd ((map_eq_zero_iff _ θ.injective).mp h0)
      ((residue_ne_zero_iff_isUnit _).mpr hnv)
  have hunits := hθ' _ _ hnv hunitL hevalres
  -- and the two scalings match
  rw [hevK, hevL, hevalK a, hevalL b, map_mul, map_mul, hunits]
  simp only [Polynomial.coeff_map, hcompat]
  exact (map_mul _ _ _).symm

omit hmono in
/-- **Proposition 2.1.5(3).** The purely residual case in full: if `a` is a root of a monic `P` over
the coefficient field whose degree is the degree of `res a` over the residues of that field, and `b`
is a root of the image of `P`, then `a` and `b` have the same leading-term type, so the embedding
extends by `ValuationSubring.extend` and preserves leading terms by `ValuationSubring.rv_extend`.

This is what step `res(K(C)) = k(C)` of Proposition 2.1.10 applies in order to lift a residue: `P`
is an exact lifting of the minimal polynomial of `res a`, with one root on each side. -/
theorem rvTypeEq_of_residual {a : A} {b : AL} {n : ℕ} {P : R[X]} (hP : P.Monic)
    (hPn : P.natDegree = n)
    (hPa : evalOn φ ((a : A) : F) P = 0) (hPb : evalOn' ψ ((b : AL) : L) P = 0)
    (θ : ResidueField A →+* ResidueField AL)
    (hθ : ∀ (x : A) (y : AL),
      fRV (rv (A := A) ((x : A) : F)) = rv (A := AL) ((y : AL) : L) →
      θ (residue A x) = residue AL y)
    (hθ' : ∀ (x : A) (y : AL), IsUnit x → IsUnit y →
      θ (residue A x) = residue AL y →
      fRV (rv (A := A) ((x : A) : F)) = rv (A := AL) ((y : AL) : L))
    (hmonoR : ∀ r r' : R,
      AL.valuation (ψ r) < AL.valuation (ψ r') → A.valuation (φ r) < A.valuation (φ r'))
    (hcompat : ∀ r : R, fRV (rv (A := A) (φ r)) = rv (A := AL) (ψ r))
    (hab : fRV (rv (A := A) ((a : A) : F)) = rv (A := AL) ((b : AL) : L))
    (hdeg : ∀ RQ : A[X], (∀ i, ((RQ.coeff i : A) : F) ∈ φ.fieldRange) → RQ.natDegree < n →
      RQ.map (residue A) ≠ 0 → (RQ.map (residue A)).eval (residue A a) ≠ 0) :
    RvTypeEq fRV φ ψ ((a : A) : F) ((b : AL) : L) :=
  rvTypeEq_of_modByMonic hP hPa hPb fun Q hQ =>
    rv_eval_eq_of_residual_transfer θ hθ hθ' hmonoR hcompat hab hdeg Q (hPn ▸ hQ)

end Transfer

end ManySorted.Language
