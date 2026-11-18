/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Theory.Model

/-!
# A model of `ACVF` is the leading-term structure of its own valuation subring

`Algebra/ACVF/Theory/Model.lean` reads a valued field off a model `M` of `ACVFTheory`: the sort
`K` is an algebraically closed field and `modelValSubring M` is the valuation subring of
`v x = val (rv x)`. This file closes the loop: the three sorts of `M` *are* the three sorts of that
valued field, compatibly with every symbol of `L_RV`, so

  `M ≃[rvLang] rvFam (modelValSubring M)`.

The comparison maps are forced. On the sort `K` it is the identity — the field `rvFam A` is built
from is `M K` itself. On `RV` and `Γ` it is "pick a representative in `K` and apply the valued
field's own `rv` / `v`": both sorts of `M` are quotients of `K`, by the axioms `rvSurj` and
`valSurj`, and the content of the theorem is that they are quotients by the *same* relations.
For `RV` that is the axiom `ball`, which says the fibers of `rv` are the open balls; for `Γ` it
is `Valuation.IsEquiv`, which says `v` and `A.valuation` order elements of `K` the same way.

The file has two uses.

* **A dictionary for the proof.** The embedding test hands the proof abstract models, while the
  algebra of Rideau-Kikuchi's argument runs on a concrete valued field. The comparison map `toRV`
  and lemmas such as `rvMap_eq_iff_rv_eq` and `valMap_le_iff_valuation` translate between the two:
  equality in the sort `RV` and the order of the sort `Γ` of `M` are those of the valued field.
* **The meaning of the theorem.** Together with the soundness theorem `models_ACVFTheory`,
  `exists_valuationSubring_equiv` says that the models of `ACVFTheory` are, up to isomorphism,
  exactly the leading-term structures of algebraically closed fields with a nontrivial valuation.
  So quantifier elimination for `ACVFTheory` is quantifier elimination for those valued fields.

## Main definitions

* `Language.toRV`, `Language.toGamma` : the comparison maps on the sorts `RV` and `Γ`.
* `Language.modelEquivRvFam` : the isomorphism `M ≃[rvLang] rvFam (modelValSubring M)`.

## Main statements

* `Language.exists_valuationSubring_equiv` : every model of `ACVFTheory` is the leading-term
  structure of an algebraically closed field with a nontrivial valuation.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]

/-! ### The two valuations agree -/

/-- `v` and the valuation of the subring it defines have the same order relation. -/
theorem valuation_le_iff_model (x y : M RVSort.K) :
    (modelValSubring M).valuation x ≤ (modelValSubring M).valuation y
      ↔ modelValuation M x ≤ modelValuation M y :=
  (modelValuation_isEquiv (M := M) x y).symm

theorem valuation_lt_iff_model (x y : M RVSort.K) :
    (modelValSubring M).valuation x < (modelValSubring M).valuation y
      ↔ modelValuation M x < modelValuation M y :=
  (modelValuation_isEquiv (M := M)).lt_iff_lt.symm

theorem valuation_eq_iff_model (x y : M RVSort.K) :
    (modelValSubring M).valuation x = (modelValSubring M).valuation y
      ↔ modelValuation M x = modelValuation M y :=
  (modelValuation_isEquiv (M := M)).eq_iff.symm

/-- `val (rv x) = 0` in the language is `v x = 1` in Mathlib's notation: the element is a unit
of the valuation ring. -/
theorem valMap_eq_zero_iff_valuation_eq_one {x : M RVSort.K} :
    valMap (rvMap x) = 0 ↔ (modelValSubring M).valuation x = 1 := by
  have h : modelValuation M x = 1 ↔ (modelValSubring M).valuation x = 1 := by
    constructor
    · intro hx
      have := (modelValuation_isEquiv (M := M)).eq_iff (r := x) (s := 1)
      rw [map_one, map_one] at this
      exact this.mp hx
    · intro hx
      have := (modelValuation_isEquiv (M := M)).eq_iff (r := x) (s := 1)
      rw [map_one, map_one] at this
      exact this.mpr hx
  exact (mval_eq_one_iff (ξ := rvMap x)).symm.trans h

/-! ### The sort `RV`

Both `M RV` and `A.RV` are quotients of `K` — by `rvSurj`, and because `rv` is onto — and the
axiom `ball` says they are quotients by the same relation. -/

/-- A representative in `K` of an element of the `RV` sort of a model. -/
noncomputable def rvSectionModel (ξ : M RVSort.RV) : M RVSort.K :=
  Function.surjInv model_rv_surjective ξ

@[simp]
theorem rvMap_rvSectionModel (ξ : M RVSort.RV) : rvMap (rvSectionModel ξ) = ξ :=
  Function.surjInv_eq _ _

/-- **The fibers of `rv` are the same on both sides.** In the model this is the axiom `ball`;
in the valued field it is `rv_eq_iff_valuation_sub_lt`; and the two agree because `v` and
`A.valuation` are equivalent valuations. -/
theorem rvMap_eq_iff_rv_eq {x y : M RVSort.K} :
    rvMap x = rvMap y ↔ rv (A := modelValSubring M) x = rv (A := modelValSubring M) y := by
  by_cases hy : y = 0
  · subst hy
    rw [show rvMap (0 : M RVSort.K) = 0 from model_rv_eq_zero_iff.mpr rfl, rv_zero,
      model_rv_eq_zero_iff, rv_eq_zero_iff]
  · rw [model_ball hy, eq_comm, rv_eq_iff_valuation_sub_lt (A := modelValSubring M) hy,
      show x + -y = x - y by ring]
    rw [valuation_lt_iff_model]
    constructor
    · intro h
      exact lt_of_not_ge fun hc => h (mval_le_iff.mpr hc)
    · intro h hc
      exact absurd (mval_le_iff.mp hc) (not_le.mpr h)

/-- **The comparison map on the leading-term sort.** -/
noncomputable def toRV (ξ : M RVSort.RV) : (modelValSubring M).RV :=
  rv (A := modelValSubring M) (rvSectionModel ξ)

@[simp]
theorem toRV_rvMap (x : M RVSort.K) :
    toRV (rvMap x) = rv (A := modelValSubring M) x :=
  rvMap_eq_iff_rv_eq.mp (rvMap_rvSectionModel (rvMap x))

theorem toRV_injective : Function.Injective (toRV (M := M)) := by
  intro ξ η h
  rw [← rvMap_rvSectionModel ξ, ← rvMap_rvSectionModel η]
  exact rvMap_eq_iff_rv_eq.mpr (by rwa [toRV, toRV] at h)

theorem toRV_surjective : Function.Surjective (toRV (M := M)) := by
  intro ζ
  obtain ⟨x, rfl⟩ := rv_surjective (A := modelValSubring M) ζ
  exact ⟨rvMap x, toRV_rvMap x⟩

theorem toRV_bijective : Function.Bijective (toRV (M := M)) :=
  ⟨toRV_injective, toRV_surjective⟩

/-! ### The sort `Γ`

The same pattern once more: `Γ` is a quotient of `K`, by `valSurj` together with `rvSurj`, and
`A.ValueGroup` is a quotient of `K` by construction. That they are the same quotient is
`Valuation.IsEquiv`. -/

theorem valrv_surjective : Function.Surjective (fun x : M RVSort.K => valMap (rvMap x)) := by
  intro g
  obtain ⟨ξ, rfl⟩ := model_val_surjective g
  obtain ⟨x, rfl⟩ := model_rv_surjective ξ
  exact ⟨x, rfl⟩

/-- A representative in `K` of an element of the `Γ` sort of a model. -/
noncomputable def gammaSectionModel (g : M RVSort.Γ) : M RVSort.K :=
  Function.surjInv valrv_surjective g

@[simp]
theorem valMap_rvMap_gammaSectionModel (g : M RVSort.Γ) :
    valMap (rvMap (gammaSectionModel g)) = g :=
  Function.surjInv_eq (f := fun x : M RVSort.K => valMap (rvMap x)) valrv_surjective g

/-- **Elements of `K` with the same value have the same value.** The left-hand `val` is the
model's, the right-hand one the valuation subring's. -/
theorem valuation_eq_of_valMap_eq {x y : M RVSort.K}
    (h : valMap (rvMap x) = valMap (rvMap y)) :
    (modelValSubring M).valuation x = (modelValSubring M).valuation y :=
  (valuation_eq_iff_model x y).mpr (congrArg (fun g => Multiplicative.ofAdd
    (OrderDual.toDual g)) h)

/-- **The comparison map on the value-group sort.** -/
noncomputable def toGamma (g : M RVSort.Γ) : RVGamma (modelValSubring M) :=
  Additive.ofMul (OrderDual.toDual ((modelValSubring M).valuation (gammaSectionModel g)))

@[simp]
theorem toGamma_valMap (x : M RVSort.K) :
    toGamma (valMap (rvMap x)) =
      Additive.ofMul (OrderDual.toDual ((modelValSubring M).valuation x)) := by
  rw [toGamma]
  exact congrArg _ (congrArg _ (valuation_eq_of_valMap_eq
    (by rw [valMap_rvMap_gammaSectionModel])))

theorem toGamma_le_iff {g h : M RVSort.Γ} : toGamma g ≤ toGamma h ↔ g ≤ h := by
  obtain ⟨x, rfl⟩ := valrv_surjective g
  obtain ⟨y, rfl⟩ := valrv_surjective h
  rw [toGamma_valMap, toGamma_valMap]
  exact (valuation_le_iff_model y x).trans (mval_le_iff (ξ := rvMap y) (η := rvMap x))

theorem toGamma_injective : Function.Injective (toGamma (M := M)) := fun _ _ h =>
  le_antisymm (toGamma_le_iff.mp (le_of_eq h)) (toGamma_le_iff.mp (le_of_eq h.symm))

theorem toGamma_surjective : Function.Surjective (toGamma (M := M)) := by
  intro γ
  obtain ⟨x, hx⟩ := (modelValSubring M).valuation_surjective
    (OrderDual.ofDual (Additive.toMul γ))
  exact ⟨valMap (rvMap x), by rw [toGamma_valMap, hx]; rfl⟩

theorem toGamma_bijective : Function.Bijective (toGamma (M := M)) :=
  ⟨toGamma_injective, toGamma_surjective⟩

@[simp]
theorem toGamma_zero : toGamma (0 : M RVSort.Γ) = 0 := by
  have h : (0 : M RVSort.Γ) = valMap (rvMap (1 : M RVSort.K)) := by
    rw [model_rv_one, model_val_one]
  rw [h, toGamma_valMap, map_one]
  rfl

@[simp]
theorem toGamma_top : toGamma (⊤ : M RVSort.Γ) = ⊤ := by
  have h : (⊤ : M RVSort.Γ) = valMap (rvMap (0 : M RVSort.K)) := model_val_zero.symm
  rw [h, toGamma_valMap, map_zero]
  rfl

theorem toGamma_add (g h : M RVSort.Γ) : toGamma (g + h) = toGamma g + toGamma h := by
  obtain ⟨x, rfl⟩ := valrv_surjective g
  obtain ⟨y, rfl⟩ := valrv_surjective h
  have hsum : valMap (rvMap x) + valMap (rvMap y) = valMap (rvMap (x * y)) := by
    rw [model_rv_mul, model_val_mul]
  rw [hsum, toGamma_valMap, toGamma_valMap, toGamma_valMap, map_mul]
  rfl

theorem toGamma_neg (g : M RVSort.Γ) : toGamma (-g) = -toGamma g := by
  by_cases hg : g = ⊤
  · subst hg
    rw [LinearOrderedAddCommGroupWithTop.neg_top, toGamma_top,
      LinearOrderedAddCommGroupWithTop.neg_top]
  · have hsum : toGamma g + toGamma (-g) = 0 := by
      rw [← toGamma_add, LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hg,
        toGamma_zero]
    have hne : toGamma g ≠ (⊤ : RVGamma (modelValSubring M)) := by
      intro hc
      exact hg (toGamma_injective (hc.trans toGamma_top.symm))
    calc toGamma (-g) = 0 + toGamma (-g) := (zero_add _).symm
      _ = (-toGamma g + toGamma g) + toGamma (-g) := by
          rw [add_comm (-toGamma g), LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hne]
      _ = -toGamma g + (toGamma g + toGamma (-g)) := add_assoc _ _ _
      _ = -toGamma g := by rw [hsum, add_zero]

/-! ### The comparison map respects the operations of the `RV` sort

The multiplication is pinned down by `rvMul` together with `rvSurj`; the remaining operations
are pinned down by the axioms `rvOne`, `negRV` and the three `rvAdd` axioms, which is what
those axioms are for. -/

theorem isResidue_rv_iff_valMap {x : M RVSort.K} :
    IsResidue (modelValSubring M) (rv (A := modelValSubring M) x)
      ↔ (valMap (rvMap x) = 0 ∨ x = 0) := by
  rw [isResidue_rv_iff, valMap_eq_zero_iff_valuation_eq_one]

@[simp]
theorem toRV_zero : toRV (0 : M RVSort.RV) = 0 := by
  have h : (0 : M RVSort.RV) = rvMap (0 : M RVSort.K) := (model_rv_eq_zero_iff.mpr rfl).symm
  rw [h, toRV_rvMap, rv_zero]

@[simp]
theorem toRV_one : toRV (1 : M RVSort.RV) = 1 := by
  rw [← model_rv_one, toRV_rvMap, map_one]

theorem toRV_mul (ξ η : M RVSort.RV) : toRV (ξ * η) = toRV ξ * toRV η := by
  obtain ⟨x, rfl⟩ := model_rv_surjective ξ
  obtain ⟨y, rfl⟩ := model_rv_surjective η
  rw [← model_rv_mul, toRV_rvMap, toRV_rvMap, toRV_rvMap, map_mul]

theorem toRV_neg (ξ : M RVSort.RV) : toRV (-ξ) = rvNeg (modelValSubring M) (toRV ξ) := by
  obtain ⟨x, rfl⟩ := model_rv_surjective ξ
  rw [model_neg_rv, ← model_rv_mul, toRV_rvMap, toRV_rvMap, rvNeg, map_mul]

theorem toRV_add (ξ η : M RVSort.RV) :
    toRV (ξ + η) = rvAdd (modelValSubring M) (toRV ξ) (toRV η) := by
  obtain ⟨x, rfl⟩ := model_rv_surjective ξ
  obtain ⟨y, rfl⟩ := model_rv_surjective η
  rw [toRV_rvMap, toRV_rvMap]
  by_cases hxy : valMap (rvMap (x + y)) = 0
  · by_cases hx : valMap (rvMap x) = 0 ∨ x = 0
    · by_cases hy : valMap (rvMap y) = 0 ∨ y = 0
      · rw [model_add_res hx hy hxy, toRV_rvMap]
        exact (rvAdd_rv_rv_of_isResidue _ (isResidue_rv_iff_valMap.mpr hx)
          (isResidue_rv_iff_valMap.mpr hy)
          (valMap_eq_zero_iff_valuation_eq_one.mp hxy)).symm
      · obtain ⟨hy1, hy2⟩ := not_or.mp hy
        rw [model_add_zero_right x hy1 hy2, toRV_zero]
        exact (rvAdd_eq_zero_of_not_isResidue _
          fun hc => hy (isResidue_rv_iff_valMap.mp hc.2.1)).symm
    · obtain ⟨hx1, hx2⟩ := not_or.mp hx
      rw [model_add_zero_left y hx1 hx2, toRV_zero]
      exact (rvAdd_eq_zero_of_not_isResidue _
        fun hc => hx (isResidue_rv_iff_valMap.mp hc.1)).symm
  · rw [model_add_zero_sum hxy, toRV_zero]
    exact (rvAdd_eq_zero_of_not_isResidue _
      fun hc => hxy (valMap_eq_zero_iff_valuation_eq_one.mpr hc.2.2)).symm

@[simp]
theorem toRV_inv (ξ : M RVSort.RV) : toRV ξ⁻¹ = (toRV ξ)⁻¹ := by
  by_cases hξ : ξ = 0
  · subst hξ
    rw [model_inv_zero, toRV_zero, inv_zero]
  · have h : toRV ξ * toRV ξ⁻¹ = 1 := by
      rw [← toRV_mul, model_mul_inv hξ, toRV_one]
    exact eq_inv_of_mul_eq_one_right h

theorem toGamma_valMap_apply (ξ : M RVSort.RV) :
    toGamma (valMap ξ) = Additive.ofMul (OrderDual.toDual (rvVal (toRV ξ))) := by
  obtain ⟨x, rfl⟩ := model_rv_surjective ξ
  rw [toGamma_valMap, toRV_rvMap, rvVal_rv]

/-! ### The isomorphism -/

/-- **Model recovery.** A model of `ACVFTheory` is isomorphic, as an `L_RV`-structure, to the
leading-term structure of its own valuation subring. The sort `K` is carried by the identity;
the other two sorts are carried by `toRV` and `toGamma`. -/
noncomputable def modelEquivRvFam : M ≃[rvLang] rvFam (modelValSubring M) :=
  { toEquiv
      | RVSort.K => _root_.Equiv.refl (M RVSort.K)
      | RVSort.RV => _root_.Equiv.ofBijective _ (toRV_bijective (M := M))
      | RVSort.Γ => _root_.Equiv.ofBijective _ (toGamma_bijective (M := M))
    map_fun' := by
      intro σ t f x
      match t, σ, f with
      | _, _, .zeroK => rfl
      | _, _, .oneK => rfl
      | _, _, .negK => rfl
      | _, _, .addK => rfl
      | _, _, .mulK => rfl
      | _, _, .zeroRV => exact toRV_zero
      | _, _, .oneRV => exact toRV_one
      | _, _, .negRV => exact toRV_neg _
      | _, _, .addRV => exact toRV_add _ _
      | _, _, .mulRV => exact toRV_mul _ _
      | _, _, .invRV => exact toRV_inv _
      | _, _, .zeroΓ => exact toGamma_zero
      | _, _, .negΓ => exact toGamma_neg _
      | _, _, .addΓ => exact toGamma_add _ _
      | _, _, .inftyΓ => exact toGamma_top
      | _, _, .rv => exact toRV_rvMap _
      | _, _, .val => exact toGamma_valMap_apply _
    map_rel' := by
      intro σ r x
      match σ, r with
      | _, .leΓ => exact toGamma_le_iff }

/-- The order of the `Γ` sort is the reverse order of the valuation. -/
theorem valMap_le_iff_valuation (x y : M RVSort.K) :
    valMap (rvMap x) ≤ valMap (rvMap y)
      ↔ (modelValSubring M).valuation y ≤ (modelValSubring M).valuation x := by
  rw [← toGamma_le_iff, toGamma_valMap, toGamma_valMap]
  exact Iff.rfl

/-- Equality in the `Γ` sort is equality of valuations. -/
theorem valMap_eq_iff_valuation (x y : M RVSort.K) :
    valMap (rvMap x) = valMap (rvMap y)
      ↔ (modelValSubring M).valuation x = (modelValSubring M).valuation y := by
  constructor
  · intro h
    exact le_antisymm ((valMap_le_iff_valuation y x).mp (le_of_eq h.symm))
      ((valMap_le_iff_valuation x y).mp (le_of_eq h))
  · intro h
    exact le_antisymm ((valMap_le_iff_valuation x y).mpr (le_of_eq h.symm))
      ((valMap_le_iff_valuation y x).mpr (le_of_eq h))

/-! ### Consequences

The recovered valued field is one the algebraic half of the proof can be run on: its field is
algebraically closed (`instIsAlgClosedModelK`) and its valuation is nontrivial. -/

/-- The recovered valuation subring has a nontrivial valuation. -/
theorem modelValSubring_nontrivial :
    ∃ x : M RVSort.K, x ≠ 0 ∧ (modelValSubring M).valuation x ≠ 1 := by
  obtain ⟨x, hx0, hx⟩ := modelValuation_nontrivial (M := M)
  refine ⟨x, hx0, fun hc => hx ?_⟩
  have h := (modelValuation_isEquiv (M := M)).eq_iff (r := x) (s := 1)
  rw [map_one, map_one] at h
  exact h.mpr hc

/-- **Model recovery, as a statement about `ACVFTheory` alone.** Every model of the theory is,
up to isomorphism of `L_RV`-structures, the leading-term structure of an algebraically closed
field with a nontrivial valuation. -/
theorem exists_valuationSubring_equiv :
    ∃ (A : ValuationSubring (M RVSort.K)),
      (∃ x : M RVSort.K, x ≠ 0 ∧ A.valuation x ≠ 1) ∧
      Nonempty (M ≃[rvLang] rvFam A) :=
  ⟨modelValSubring M, modelValSubring_nontrivial, ⟨modelEquivRvFam⟩⟩

end ManySorted.Language
