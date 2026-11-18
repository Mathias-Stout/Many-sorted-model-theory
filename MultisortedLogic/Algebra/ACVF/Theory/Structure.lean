/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Theory.Language
public import MultisortedLogic.AlgebraicBackground.RV

/-!
# Valued fields as `L_RV`-structures

A valued field `(F, A)` — a field `F` with a valuation subring `A` — is made into a structure for
the three-sorted leading-term language `L_RV` of `Algebra/ACVF/Theory/Language.lean` by interpreting

* the sort `K` as `F`,
* the sort `RV` as the leading term structure `A.RV = Fˣ / (1 + 𝔪) ∪ {0}`,
* the sort `Γ` as `Additive (A.ValueGroupᵒᵈ)`, the value group written additively with `∞`.

The order dual is what puts `∞ = v 0` at the *top*, as in the usual additive convention for
valuations; Mathlib's `ValueGroup` is multiplicative with `v 0 = 0` at the bottom.

On `RV` the multiplication is the quotient multiplication, `0 = rv 0` and `1 = rv 1` come from
the monoid-with-zero structure, negation is multiplication by `rv (-1)` (the negation of the
field sort, descended to `RV`), and addition is the addition of the residue field
`k = rvVal⁻¹(1) ∪ {0}` extended by `0`, i.e. `ξ + η` is `rv (a + b)` for representatives `a, b` when
`ξ`, `η` and `ξ + η` all lie in the residue field, and is `0` otherwise.

The residue field sits inside `A.RV` as `IsResidue`: the fiber of `rvVal` over `1`, **together
with `0`**. The `0` has to be included — it is the residue field's own zero, while
`rvVal 0 = 0`, not `1` — and without it the addition would have no identity.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring

universe u

variable {F : Type u} [Field F] (A : ValuationSubring F)

/-- The value group of `A`, written additively with `∞` on top. -/
abbrev RVGamma := Additive (A.ValueGroupᵒᵈ)

/-- A choice of representative in `F` for an element of `A.RV`. -/
noncomputable def rvSection (ξ : A.RV) : F := (rv_surjective ξ).choose

@[simp]
theorem rv_rvSection (ξ : A.RV) : rv (A := A) (rvSection A ξ) = ξ := (rv_surjective ξ).choose_spec

-- TODO: It should be possible (with slight refactoring) to replace
-- the hypothesis that `ξ` has `rvVal` of zero, to just `ξ = 0`.
/-- The copy of the residue field inside `A.RV`: the fiber of `rvVal` over `1`, together with
`0`. The `0` matters — it is the residue field's own zero, and `rvVal 0 = 0`, not `1`, so it is
not in the fiber. Leaving it out would give an addition with no identity. -/
abbrev IsResidue (ξ : A.RV) : Prop := rvVal ξ = 1 ∨ rvVal ξ = 0

theorem isResidue_zero : IsResidue (A := A) 0 := Or.inr (map_zero _)

theorem isResidue_rv {a : F} (ha : A.valuation a = 1) : IsResidue (A := A) (rv (A := A) a) :=
  Or.inl (by rw [rvVal_rv]; exact ha)

/-- Addition on `A.RV`: the residue field addition, extended by `0`.

On the residue field — the fiber of `rvVal` over `1`, together with `0` — this is the addition
of the residue field, computed on representatives; everywhere else it is `0`. The last
conjunct is what makes the choice of representatives immaterial: if the residues cancel, the
leading term of the sum genuinely depends on the representatives, and the answer is the
residue `0`. -/
noncomputable def rvAdd (ξ η : A.RV) : A.RV :=
  if IsResidue (A := A) ξ ∧ IsResidue (A := A) η ∧
      A.valuation (rvSection A ξ + rvSection A η) = 1 then
    rv (A := A) (rvSection A ξ + rvSection A η)
  else 0

@[simp]
theorem rvSection_zero : rvSection A (0 : A.RV) = 0 :=
  rv_eq_zero_iff.mp (rv_rvSection A 0)

/-- `0` is an identity for the residue addition. -/
theorem rvAdd_zero_left {η : A.RV} (hη : IsResidue (A := A) η) : rvAdd A 0 η = η := by
  rcases hη with h | h
  · have hval : A.valuation (rvSection A (0 : A.RV) + rvSection A η) = 1 := by
      rw [rvSection_zero, zero_add, ← rvVal_rv (A := A), rv_rvSection]
      exact h
    rw [rvAdd, ite_eq_left ⟨isResidue_zero A, Or.inl h, hval⟩, rvSection_zero, zero_add,
      rv_rvSection]
  · rw [rvVal_eq_zero_iff] at h
    subst h
    rw [rvAdd, ite_eq_right]
    rintro ⟨-, -, hv⟩
    rw [rvSection_zero, add_zero, map_zero] at hv
    exact zero_ne_one hv

/-- `rvAdd` lands in the residue field. -/
theorem isResidue_rvAdd (ξ η : A.RV) : IsResidue (A := A) (rvAdd A ξ η) := by
  rw [rvAdd]
  split
  · rename_i h
    exact Or.inl (by rw [rvVal_rv]; exact h.2.2)
  · exact isResidue_zero A

/-- The residue addition is commutative. -/
theorem rvAdd_comm (ξ η : A.RV) : rvAdd A ξ η = rvAdd A η ξ := by
  unfold rvAdd
  rw [add_comm (rvSection A ξ) (rvSection A η)]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.2.1, h1.1, h1.2.2⟩ h2
  · exact absurd ⟨h2.2.1, h2.1, h2.2.2⟩ h1
  · rfl

/-- `0` is an identity for the residue addition, on the right. -/
theorem rvAdd_zero_right {ξ : A.RV} (hξ : IsResidue (A := A) ξ) : rvAdd A ξ 0 = ξ := by
  rw [rvAdd_comm]
  exact rvAdd_zero_left A hξ

/-- **`rvAdd` computes on representatives.** If `a` and `b` have valuation `1` and their sum
does too — that is, their residues do not cancel — then the residue addition of their leading
terms is the leading term of their sum. This is what pins `rvAdd` down: it is defined through an
arbitrary choice of representatives, and this says the choice does not matter exactly when the
sum is well-defined. -/
theorem rvAdd_rv_rv {a b : F} (ha : A.valuation a = 1) (hb : A.valuation b = 1)
    (hab : A.valuation (a + b) = 1) :
    rvAdd A (rv (A := A) a) (rv (A := A) b) = rv (A := A) (a + b) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  set a' := rvSection A (rv (A := A) a) with ha'def
  set b' := rvSection A (rv (A := A) b) with hb'def
  have hra : rv (A := A) a' = rv (A := A) a := rv_rvSection A _
  have hrb : rv (A := A) b' = rv (A := A) b := rv_rvSection A _
  -- the chosen representatives are close to `a` and `b`
  have hda : A.valuation (a' - a) < A.valuation a :=
    (rv_eq_iff_valuation_sub_lt ha0).mp hra.symm
  have hdb : A.valuation (b' - b) < A.valuation b :=
    (rv_eq_iff_valuation_sub_lt hb0).mp hrb.symm
  -- hence their sum is close to `a + b`, so has the same leading term
  have hsum : A.valuation ((a' + b') - (a + b)) < A.valuation (a + b) := by
    have hle : A.valuation ((a' - a) + (b' - b))
        ≤ max (A.valuation (a' - a)) (A.valuation (b' - b)) :=
      A.valuation.map_add_le_max' _ _
    rw [show (a' + b') - (a + b) = (a' - a) + (b' - b) by ring]
    refine lt_of_le_of_lt hle ?_
    rw [hab]
    exact max_lt (ha ▸ hda) (hb ▸ hdb)
  have hab0 : a + b ≠ 0 := fun h => by simp [h] at hab
  have key : rv (A := A) (a' + b') = rv (A := A) (a + b) :=
    ((rv_eq_iff_valuation_sub_lt hab0).mpr hsum).symm
  have hcond : IsResidue (A := A) (rv (A := A) a) ∧ IsResidue (A := A) (rv (A := A) b) ∧
      A.valuation (a' + b') = 1 := by
    refine ⟨isResidue_rv A ha, isResidue_rv A hb, ?_⟩
    rw [← rvVal_rv (A := A) (a' + b'), key, rvVal_rv]
    exact hab
  rw [rvAdd, ite_eq_left hcond]
  exact key

/-- The converse reading of `rvAdd`: a nonzero residue sum is the leading term of the sum of
any representatives. `rvAdd` returns `0` exactly in the canceling case. -/
theorem rvAdd_eq_rv_add {a b : F} (ha : A.valuation a = 1) (hb : A.valuation b = 1)
    (h : rvAdd A (rv (A := A) a) (rv (A := A) b) ≠ 0) :
    rvAdd A (rv (A := A) a) (rv (A := A) b) = rv (A := A) (a + b) := by
  by_cases hab : A.valuation (a + b) = 1
  · exact rvAdd_rv_rv A ha hb hab
  · exfalso
    apply h
    rw [rvAdd, ite_eq_right]
    rintro ⟨-, -, h3⟩
    -- the chosen representatives are close to `a` and `b`, so their sum is close to `a + b`
    have ha0 : a ≠ 0 := fun h0 => by simp [h0] at ha
    have hb0 : b ≠ 0 := fun h0 => by simp [h0] at hb
    have hda : A.valuation (rvSection A (rv (A := A) a) - a) < A.valuation a :=
      (rv_eq_iff_valuation_sub_lt ha0).mp (rv_rvSection A _).symm
    have hdb : A.valuation (rvSection A (rv (A := A) b) - b) < A.valuation b :=
      (rv_eq_iff_valuation_sub_lt hb0).mp (rv_rvSection A _).symm
    have hlt : A.valuation ((rvSection A (rv (A := A) a) + rvSection A (rv (A := A) b))
        - (a + b)) < 1 := by
      have hle := A.valuation.map_add_le_max' (rvSection A (rv (A := A) a) - a)
        (rvSection A (rv (A := A) b) - b)
      rw [show (rvSection A (rv (A := A) a) + rvSection A (rv (A := A) b)) - (a + b)
        = (rvSection A (rv (A := A) a) - a) + (rvSection A (rv (A := A) b) - b) by ring]
      exact lt_of_le_of_lt hle (max_lt (ha ▸ hda) (hb ▸ hdb))
    -- so `a + b` has valuation `1` too, contradicting `hab`
    apply hab
    have := A.valuation.map_add_of_distinct_val (x := (rvSection A (rv (A := A) a)
      + rvSection A (rv (A := A) b)))
      (y := -((rvSection A (rv (A := A) a) + rvSection A (rv (A := A) b)) - (a + b)))
    rw [show (rvSection A (rv (A := A) a) + rvSection A (rv (A := A) b))
      + -((rvSection A (rv (A := A) a) + rvSection A (rv (A := A) b)) - (a + b)) = a + b by ring,
      Valuation.map_neg] at this
    rw [this (by rw [h3]; exact ne_of_gt hlt), h3, max_eq_left (le_of_lt hlt)]

/-! ### `rvAdd` through arbitrary representatives

`rvAdd` is defined through the chosen representatives `rvSection`, which is what makes it a
function, but it is a poor thing to reason with: the model-recovery layer meets the addition
through *arbitrary* representatives, as `rv x + rv y`. The two agree, because the guard
`val (x + y) = 1` does not depend on the representatives — moving `x` and `y` inside their own
balls moves `x + y` by less than `1`. -/

/-- The chosen representative of `ξ` has the valuation of `ξ`. -/
@[simp]
theorem valuation_rvSection (ξ : A.RV) : A.valuation (rvSection A ξ) = rvVal (A := A) ξ := by
  conv_rhs => rw [← rv_rvSection A ξ]
  rw [rvVal_rv]

/-- Being in the residue field is a condition on a representative: valuation `1`, or zero. -/
theorem isResidue_rv_iff {x : F} :
    IsResidue (A := A) (rv (A := A) x) ↔ A.valuation x = 1 ∨ x = 0 := by
  simp only [IsResidue, rvVal_rv, Valuation.zero_iff]

/-- A residue-field element is at distance less than `1` from its chosen representative. -/
theorem valuation_rvSection_sub_lt_one {x : F} (hx : A.valuation x = 1 ∨ x = 0) :
    A.valuation (rvSection A (rv (A := A) x) - x) < 1 := by
  rcases hx with hx | hx
  · have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hx
      exact zero_ne_one hx
    have := (rv_eq_iff_valuation_sub_lt (A := A) hx0).mp (rv_rvSection A (rv (A := A) x)).symm
    rwa [hx] at this
  · subst hx
    rw [rv_zero, rvSection_zero, sub_zero, map_zero]
    exact zero_lt_one

/-- Adding something of valuation less than `1` does not change whether the valuation is `1`. -/
theorem valuation_add_eq_one_iff_of_lt {a b : F} (hb : A.valuation b < 1) :
    A.valuation (a + b) = 1 ↔ A.valuation a = 1 := by
  constructor
  · intro hab
    have hne : A.valuation (a + b) ≠ A.valuation (-b) := by
      rw [Valuation.map_neg, hab]
      exact ne_of_gt hb
    have := A.valuation.map_add_of_distinct_val hne
    rw [show a + b + -b = a by ring, Valuation.map_neg, hab, max_eq_left (le_of_lt hb)] at this
    exact this
  · intro ha
    have hne : A.valuation a ≠ A.valuation b := by rw [ha]; exact ne_of_gt hb
    rw [A.valuation.map_add_of_distinct_val hne, ha, max_eq_left (le_of_lt hb)]

/-- **The guard of `rvAdd` does not depend on the representatives.** -/
theorem valuation_rvSection_add_eq_one_iff {x y : F}
    (hx : IsResidue (A := A) (rv (A := A) x)) (hy : IsResidue (A := A) (rv (A := A) y)) :
    A.valuation (rvSection A (rv (A := A) x) + rvSection A (rv (A := A) y)) = 1
      ↔ A.valuation (x + y) = 1 := by
  rw [isResidue_rv_iff] at hx hy
  have hdx := valuation_rvSection_sub_lt_one (A := A) hx
  have hdy := valuation_rvSection_sub_lt_one (A := A) hy
  set x' := rvSection A (rv (A := A) x)
  set y' := rvSection A (rv (A := A) y)
  have hd : A.valuation ((x' - x) + (y' - y)) < 1 :=
    lt_of_le_of_lt (A.valuation.map_add_le_max' _ _) (max_lt hdx hdy)
  rw [show x' + y' = (x + y) + ((x' - x) + (y' - y)) by ring]
  exact valuation_add_eq_one_iff_of_lt A hd

/-- **`rvAdd` computed on arbitrary representatives.** -/
theorem rvAdd_rv_rv_of_isResidue {x y : F}
    (hx : IsResidue (A := A) (rv (A := A) x)) (hy : IsResidue (A := A) (rv (A := A) y))
    (hxy : A.valuation (x + y) = 1) :
    rvAdd A (rv (A := A) x) (rv (A := A) y) = rv (A := A) (x + y) := by
  have hguard : A.valuation (rvSection A (rv (A := A) x) + rvSection A (rv (A := A) y)) = 1 :=
    (valuation_rvSection_add_eq_one_iff A hx hy).mpr hxy
  rw [rvAdd, ite_eq_left ⟨hx, hy, hguard⟩]
  have hxy0 : x + y ≠ 0 := by
    intro h
    rw [h, map_zero] at hxy
    exact zero_ne_one hxy
  refine ((rv_eq_iff_valuation_sub_lt (A := A) hxy0).mpr ?_).symm
  rw [isResidue_rv_iff] at hx hy
  have hdx := valuation_rvSection_sub_lt_one (A := A) hx
  have hdy := valuation_rvSection_sub_lt_one (A := A) hy
  rw [show rvSection A (rv (A := A) x) + rvSection A (rv (A := A) y) - (x + y)
    = (rvSection A (rv (A := A) x) - x) + (rvSection A (rv (A := A) y) - y) by ring, hxy]
  exact lt_of_le_of_lt (A.valuation.map_add_le_max' _ _) (max_lt hdx hdy)

/-- **`rvAdd` is `0` exactly outside the residue field**, again on arbitrary representatives. -/
theorem rvAdd_eq_zero_of_not_isResidue {x y : F}
    (h : ¬(IsResidue (A := A) (rv (A := A) x) ∧ IsResidue (A := A) (rv (A := A) y)
      ∧ A.valuation (x + y) = 1)) :
    rvAdd A (rv (A := A) x) (rv (A := A) y) = 0 := by
  rw [rvAdd, ite_eq_right]
  rintro ⟨h1, h2, h3⟩
  exact h ⟨h1, h2, (valuation_rvSection_add_eq_one_iff A h1 h2).mp h3⟩

/-- Negation on `A.RV`, descending from the valued field: `-ξ = rv (-1) * ξ`. -/
noncomputable def rvNeg (ξ : A.RV) : A.RV := rv (A := A) (-1) * ξ

/-- The family interpreting the three sorts of `L_RV` for the valued field `(F, A)`. -/
abbrev rvFam : RVSort → Type u
  | RVSort.K => F
  | RVSort.RV => A.RV
  -- TODO: Eventually, we would like for this to also be written multiplicatively.
  -- Moving away from the custom `RVGamma` definition.
  | RVSort.Γ => RVGamma A

/-- A valued field is an `L_RV`-structure. -/
noncomputable instance rvStructure : rvLang.Structure (rvFam A) where
  funMap := fun {σ s} f =>
    match s, σ, f with
    | _, _, .zeroK => fun _ => (0 : F)
    | _, _, .oneK => fun _ => (1 : F)
    | _, _, .negK => fun x => -x
    | _, _, .addK => fun x => x.1 + x.2
    | _, _, .mulK => fun x => x.1 * x.2
    | _, _, .zeroRV => fun _ => (0 : A.RV)
    | _, _, .oneRV => fun _ => (1 : A.RV)
    | _, _, .negRV => fun x => rvNeg A x
    | _, _, .addRV => fun x => rvAdd A x.1 x.2
    | _, _, .mulRV => fun x => x.1 * x.2
    | _, _, .invRV => fun x => x⁻¹
    | _, _, .zeroΓ => fun _ => (0 : RVGamma A)
    | _, _, .negΓ => fun x => -x
    | _, _, .addΓ => fun x => x.1 + x.2
    | _, _, .inftyΓ => fun _ => (⊤ : RVGamma A)
    | _, _, .rv => fun x => rv (A := A) x
    | _, _, .val => fun x => Additive.ofMul (OrderDual.toDual (rvVal (A := A) x))
  RelMap := fun {σ} r =>
    match σ, r with
    | _, .leΓ => fun x => x.1 ≤ x.2

/-! ### The operations of the interpreted sorts

Instance search unfolds `rvFam`, so the sorts `K` and `Γ` carry the operations of `F` and of
`RVGamma A`, and the sort `RV` the multiplication, `0`, `1` and inverse of `A.RV`. Only the
addition and the negation of the `RV` sort are new; they are instances on `A.RV` itself.

They are stated for `A.RV` rather than for `rvFam A RVSort.RV`: `simp` does not reduce the
`match` in `rvFam` when it indexes a lemma, so a lemma stated for `rvFam A RVSort.RV` never
fires, while one stated for `A.RV` fires on both. -/

/-- Addition on the `RV` sort: the residue field addition extended by `0`. -/
noncomputable instance instAddRV : Add A.RV := ⟨rvAdd A⟩

/-- Negation on the `RV` sort, descending from the field. -/
noncomputable instance instNegRV : Neg A.RV := ⟨rvNeg A⟩

@[simp]
theorem add_eq_rvAdd (ξ η : A.RV) : ξ + η = rvAdd A ξ η := rfl

@[simp]
theorem neg_eq_rvNeg (ξ : A.RV) : -ξ = rvNeg A ξ := rfl

/-- Every sort of a valued field is nonempty. -/
instance instNonemptyRVFam : ∀ s : RVSort, Nonempty ((rvFam A) s)
  | RVSort.K => ⟨(0 : F)⟩
  | RVSort.RV => ⟨(0 : A.RV)⟩
  | RVSort.Γ => ⟨(0 : RVGamma A)⟩

/-! ### Compatibility of the interpretation with the language -/

instance compatibleRingK : CompatibleRingL rvLang (rvFam A) RVSort.K where
  funMap_add _ := rfl
  funMap_zero := rfl
  funMap_neg _ := rfl
  funMap_mul _ := rfl
  funMap_one := rfl

instance compatibleRingRV : CompatibleRingL rvLang (rvFam A) RVSort.RV where
  funMap_add _ := rfl
  funMap_zero := rfl
  funMap_neg _ := rfl
  funMap_mul _ := rfl
  funMap_one := rfl

instance compatibleOAGroupΓ : CompatibleOAGroupL rvLang (rvFam A) RVSort.Γ where
  funMap_add _ := rfl
  funMap_zero := rfl
  funMap_neg _ := rfl
  realize_orderF _ := Iff.rfl

instance compatibleTopΓ : CompatibleTopL rvLang (rvFam A) RVSort.Γ where
  funMap_infty := rfl

/-! ### The two maps at the level of terms -/

variable {A}

@[simp]
theorem realize_rvT {σ : Arity RVSort} (t : rvLang.Term σ ⦃RVSort.K⦄) (xs : rvFam A [^] σ) :
    (rvT t).realize xs = rv (A := A) (t.realize xs) :=
  rfl

@[simp]
theorem realize_invT {σ : Arity RVSort} (t : rvLang.Term σ ⦃RVSort.RV⦄) (xs : rvFam A [^] σ) :
    (invT t).realize xs = (t.realize xs : A.RV)⁻¹ :=
  rfl

@[simp]
theorem realize_valT {σ : Arity RVSort} (t : rvLang.Term σ ⦃RVSort.RV⦄) (xs : rvFam A [^] σ) :
    (valT t).realize xs = Additive.ofMul (OrderDual.toDual (rvVal (A := A) (t.realize xs))) :=
  rfl

end ManySorted.Language
