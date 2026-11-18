/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Theory.Axioms
public import MultisortedLogic.Algebra.EOGroupModel

/-!
# Models of `ACVF` are valued fields

This is the model-recovery half of the `L_RV` story. Given an
abstract model `M` of `ACVFTheory`, we read a valued field off it: the sort `K` is an
algebraically closed field, the sort `Γ` is a linearly ordered abelian group with `∞`, and
`v x := val (rv x)`, read multiplicatively, is a nontrivial valuation on it. The valuation
subring it defines is the valued field the algebraic half of the proof works with.

The pattern is the model algebra of `Algebra/ACF/Basic.lean` and `Algebra/DOAG/Basic.lean`: the
operations are read off from the interpretation of the language, the axioms are then statements
about them, and the Mathlib structures are assembled from those statements.

Two points of orientation.

* `Γ` is *additive with `∞` on top*, while Mathlib's valuations are *multiplicative with `0` at
  the bottom*. The passage between them is `Multiplicative (M Γ)ᵒᵈ`, which Mathlib already knows
  to be a `LinearOrderedCommGroupWithZero`. So `mval` below reverses both the order and the
  notation, and `v x ≤ v y` in Mathlib's sense is `val (rv y) ≤ val (rv x)` in the language's.
* Nontriviality of the valuation is what makes the sort `Γ` nontrivial, which is a hypothesis of
  `LinearOrderedAddCommGroupWithTop`. The group axioms alone do not give it: a one-point `Γ`,
  where `∞ = 0`, satisfies all of them.

## Main definitions

* `Language.rvMap`, `Language.valMap` : `rv` and `val` in a model.
* `Language.mval` : `val`, read as a multiplicative value with zero.
* `Language.modelValuation` : the valuation `v x = val (rv x)` on the sort `K`.
* `Language.modelValSubring` : the valuation subring it defines.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring

universe w

variable {M : RVSort → Type w} [rvLang.Structure M]

/-- The leading-term map of a model. -/
def rvMap (x : M RVSort.K) : M RVSort.RV := funMap (L := rvLang) RVFunc.rv x

/-- The valuation map of a model, from the `RV` sort to the `Γ` sort. -/
def valMap (ξ : M RVSort.RV) : M RVSort.Γ := funMap (L := rvLang) RVFunc.val ξ

@[simp]
theorem realize_rvT_model {σ : Arity RVSort} (t : rvLang.Term σ ⦃RVSort.K⦄) (xs : M [^] σ) :
    (rvT t).realize xs = rvMap (t.realize xs) :=
  rfl

@[simp]
theorem realize_valT_model {σ : Arity RVSort} (t : rvLang.Term σ ⦃RVSort.RV⦄) (xs : M [^] σ) :
    (valT t).realize xs = valMap (t.realize xs) :=
  rfl

/-! ### The theory splits -/

section SubTheories

variable (M) [M ⊨ ACVFTheory]

instance model_RVTheory : M ⊨ (RVTheory : rvLang.Theory) :=
  Theory.Model.mono (T' := ACVFTheory) inferInstance fun _ h => Or.inl (Or.inl (Or.inl h))

instance model_GammaTheory : M ⊨ (GammaTheory : rvLang.Theory) :=
  Theory.Model.mono (T' := ACVFTheory) inferInstance fun _ h => Or.inl (Or.inl (Or.inr h))

instance model_ACFTheory_K : M ⊨ ACFTheory rvLang RVSort.K :=
  Theory.Model.mono (T' := ACVFTheory) inferInstance fun _ h => Or.inl (Or.inr h)

instance model_EOCommGroupTheory : M ⊨ EOCommGroupTheory rvLang RVSort.Γ :=
  model_GammaTheory M

theorem model_nontriviallyValued : M ⊨ nontriviallyValued :=
  Theory.realize_sentence_of_mem (T := ACVFTheory) (M := M) (Or.inr rfl)

/-- Each leading-term axiom holds in a model of `ACVFTheory`. -/
theorem model_rvAxiom (ax : RVAxiom) : M ⊨ ax.toSentence :=
  Theory.realize_sentence_of_mem (T := RVTheory) (M := M) (Set.mem_range_self ax)

end SubTheories

/-! ### The field sort

A model of `ACVFTheory` models `ACFTheory` on the sort `K`, so the model algebra of
`Algebra/ACF/Basic.lean` applies verbatim. -/

section FieldSort

variable (M) [M ⊨ ACVFTheory]

noncomputable instance instFieldModelK : Field (M RVSort.K) :=
  modelField rvLang M RVSort.K

instance instCompatibleRingModelK : CompatibleRingL rvLang M RVSort.K :=
  modelFieldCompatible rvLang M RVSort.K

instance instIsAlgClosedModelK : IsAlgClosed (M RVSort.K) :=
  modelIsAlgClosed rvLang M RVSort.K

end FieldSort

/-! ### The value-group sort

The group axioms make `Γ` a linearly ordered abelian group with top, *provided* it has more
than one element. That last point is where nontriviality of the valuation enters: if `∞ = 0`
in `Γ` then `g = 0 + g = ∞ + g = ∞ = 0` for every `g`, so every element of `K` would have
value `0`, contradicting `nontriviallyValued`. -/

section GammaSort

open EOCommGroupModel

variable (M) [M ⊨ ACVFTheory]

-- TODO: As we have not at this point built the instance
-- for `Γ`, we have to do lots of manual work i.e. the letI
-- statements below. It would perhaps be stylistically better
-- to first build an instance on `Γ`.
/-- The witness to nontriviality, read off from `nontriviallyValued`. -/
theorem model_exists_nontrivial :
   letI := modelZero rvLang M RVSort.Γ
    ∃ x : M RVSort.K, x ≠ 0 ∧ valMap (rvMap x) ≠ 0 := by
  let := modelAdd rvLang M RVSort.Γ
  let := modelNeg rvLang M RVSort.Γ
  let := modelZero rvLang M RVSort.Γ
  let := modelLE rvLang M RVSort.Γ
  have := modelOAGroupCompatible rvLang M RVSort.Γ
  simpa [nontriviallyValued] using model_nontriviallyValued M

/-- **The value group of a model is nontrivial.** -/
theorem model_top_ne_zero :
    letI := modelZero rvLang M RVSort.Γ
    letI := modelTop rvLang M RVSort.Γ
    (⊤ : M RVSort.Γ) ≠ 0 := by
  let := modelAdd rvLang M RVSort.Γ
  let := modelNeg rvLang M RVSort.Γ
  let := modelZero rvLang M RVSort.Γ
  let := modelTop rvLang M RVSort.Γ
  let := modelLE rvLang M RVSort.Γ
  intro htop
  have hall : ∀ g : M RVSort.Γ, g = 0 := by
    intro g
    have h1 := model_toProp rvLang M RVSort.Γ .zeroAdd g
    have h2 := model_toProp rvLang M RVSort.Γ .topAdd g
    rw [htop] at h2
    exact h1.symm.trans h2
  obtain ⟨x, -, hx⟩ := model_exists_nontrivial M
  exact hx (hall _)

/-- **The value group of a model is a linearly ordered abelian group with `∞`.** -/
noncomputable instance instGammaModel : LinearOrderedAddCommGroupWithTop (M RVSort.Γ) :=
  modelLinearOrderedAddCommGroupWithTop rvLang M RVSort.Γ (model_top_ne_zero M)

instance instCompatibleOAGroupModelGamma : CompatibleOAGroupL rvLang M RVSort.Γ :=
  modelDerivedCompatible rvLang M RVSort.Γ (model_top_ne_zero M)

instance instCompatibleTopModelGamma : CompatibleTopL rvLang M RVSort.Γ :=
  modelDerivedCompatibleTop rvLang M RVSort.Γ (model_top_ne_zero M)

end GammaSort

/-! ### The leading-term sort

The `RV` sort carries no algebraic axioms — its addition is not associative — so only the raw
operations are read off the structure. They are what the leading-term axioms speak about. -/

section RVSortOps

/-! The operations are instances only for models of `ACVFTheory`, although they do not use the
theory: as instances on every `L_RV`-structure they would overlap, on `rvFam A`, with the
operations of `A.RV` that `Algebra/ACVF/Theory/Structure.lean` declares. -/

variable (M)

@[nolint unusedArguments]
noncomputable instance instMulModelRV [M ⊨ ACVFTheory] : Mul (M RVSort.RV) :=
  modelMul rvLang M RVSort.RV
@[nolint unusedArguments]
noncomputable instance instAddModelRV [M ⊨ ACVFTheory] : Add (M RVSort.RV) :=
  modelAdd rvLang M RVSort.RV
@[nolint unusedArguments]
noncomputable instance instNegModelRV [M ⊨ ACVFTheory] : Neg (M RVSort.RV) :=
  modelNeg rvLang M RVSort.RV
@[nolint unusedArguments]
noncomputable instance instZeroModelRV [M ⊨ ACVFTheory] : Zero (M RVSort.RV) :=
  modelZero rvLang M RVSort.RV
@[nolint unusedArguments]
noncomputable instance instOneModelRV [M ⊨ ACVFTheory] : One (M RVSort.RV) :=
  modelOne rvLang M RVSort.RV

/-- The inverse of the leading-term sort, read off from the structure. -/
@[nolint unusedArguments]
noncomputable instance instInvModelRV [M ⊨ ACVFTheory] : Inv (M RVSort.RV) :=
  ⟨fun ξ => funMap (L := rvLang) RVFunc.invRV ξ⟩

variable [M ⊨ ACVFTheory]

instance instCompatibleRingModelRV : CompatibleRingL rvLang M RVSort.RV :=
  modelRingCompatible rvLang M RVSort.RV

variable {M}

@[simp]
theorem realize_invT_model {σ : Arity RVSort} (t : rvLang.Term σ ⦃RVSort.RV⦄) (xs : M [^] σ) :
    (invT t).realize xs = (t.realize xs : M RVSort.RV)⁻¹ :=
  rfl

end RVSortOps

/-! ### What the axioms say in a model -/

section Axioms

variable [M ⊨ ACVFTheory]

theorem model_rv_mul (x y : M RVSort.K) : rvMap (x * y) = rvMap x * rvMap y := by
  have h := model_rvAxiom M RVAxiom.rvMul
  rw [RVAxiom.toSentence] at h
  simpa using h x y

@[simp]
theorem model_rv_eq_zero_iff {x : M RVSort.K} : rvMap x = 0 ↔ x = 0 := by
  have h := model_rvAxiom M RVAxiom.rvZero
  rw [RVAxiom.toSentence] at h
  simpa using h x

theorem model_rv_surjective : Function.Surjective (rvMap (M := M)) := by
  have h := model_rvAxiom M RVAxiom.rvSurj
  rw [RVAxiom.toSentence] at h
  simpa [Function.Surjective] using h

theorem model_val_mul (ξ η : M RVSort.RV) : valMap (ξ * η) = valMap ξ + valMap η := by
  have h := model_rvAxiom M RVAxiom.valMul
  rw [RVAxiom.toSentence] at h
  simpa using h ξ η

theorem model_ball {x y : M RVSort.K} (hy : y ≠ 0) :
    rvMap x = rvMap y ↔ ¬ (valMap (rvMap (x + -y)) ≤ valMap (rvMap y)) := by
  have h := model_rvAxiom M RVAxiom.ball
  rw [RVAxiom.toSentence] at h
  simpa using h x y hy

theorem model_ultrametric (x y : M RVSort.K) :
    valMap (rvMap x) ≤ valMap (rvMap (x + y)) ∨ valMap (rvMap y) ≤ valMap (rvMap (x + y)) := by
  have h := model_rvAxiom M RVAxiom.ultrametric
  rw [RVAxiom.toSentence] at h
  simpa using h x y

theorem model_val_surjective : Function.Surjective (valMap (M := M)) := by
  have h := model_rvAxiom M RVAxiom.valSurj
  rw [RVAxiom.toSentence] at h
  simpa [Function.Surjective] using h

theorem model_val_zero : valMap (rvMap (0 : M RVSort.K)) = ⊤ := by
  have h := model_rvAxiom M RVAxiom.valZero
  rw [RVAxiom.toSentence] at h
  simpa using h

theorem model_rv_one : rvMap (1 : M RVSort.K) = 1 := by
  have h := model_rvAxiom M RVAxiom.rvOne
  rw [RVAxiom.toSentence] at h
  simpa using h

theorem model_neg_rv (ξ : M RVSort.RV) : -ξ = rvMap (-1 : M RVSort.K) * ξ := by
  have h := model_rvAxiom M RVAxiom.negRV
  rw [RVAxiom.toSentence] at h
  simpa using h ξ

theorem model_add_res {x y : M RVSort.K}
    (hx : valMap (rvMap x) = 0 ∨ x = 0) (hy : valMap (rvMap y) = 0 ∨ y = 0)
    (hxy : valMap (rvMap (x + y)) = 0) :
    rvMap x + rvMap y = rvMap (x + y) := by
  have h := model_rvAxiom M RVAxiom.rvAddRes
  rw [RVAxiom.toSentence] at h
  simpa using
    h x y (or_iff_not_imp_left.mp hx) (or_iff_not_imp_left.mp hy) hxy

theorem model_add_zero_left {x : M RVSort.K} (y : M RVSort.K)
    (hx : valMap (rvMap x) ≠ 0) (hx0 : x ≠ 0) : rvMap x + rvMap y = 0 := by
  have h := model_rvAxiom M RVAxiom.rvAddZeroL
  rw [RVAxiom.toSentence] at h
  simpa using h x y hx hx0

theorem model_add_zero_right (x : M RVSort.K) {y : M RVSort.K}
    (hy : valMap (rvMap y) ≠ 0) (hy0 : y ≠ 0) : rvMap x + rvMap y = 0 := by
  have h := model_rvAxiom M RVAxiom.rvAddZeroR
  rw [RVAxiom.toSentence] at h
  simpa using h x y hy hy0

@[simp]
theorem model_inv_zero : (0 : M RVSort.RV)⁻¹ = 0 := by
  have h := model_rvAxiom M RVAxiom.invZero
  rw [RVAxiom.toSentence] at h
  simpa using h

theorem model_mul_inv {ξ : M RVSort.RV} (hξ : ξ ≠ 0) : ξ * ξ⁻¹ = 1 := by
  have h := model_rvAxiom M RVAxiom.mulInv
  rw [RVAxiom.toSentence] at h
  simpa using h ξ hξ

/-- `rv` commutes with inversion. -/
@[simp]
theorem model_rv_inv (x : M RVSort.K) : rvMap x⁻¹ = (rvMap x)⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    rw [inv_zero, model_rv_eq_zero_iff.mpr rfl, model_inv_zero]
  · -- the `RV` sort carries no multiplicative axioms, so cancellation has to be done through
    -- `rv`, which is where the monoid structure comes from
    obtain ⟨w, hw⟩ := model_rv_surjective ((rvMap x)⁻¹)
    have hxne : rvMap x ≠ 0 := fun hc => hx (model_rv_eq_zero_iff.mp hc)
    have h1 : rvMap (x * w) = rvMap 1 := by
      rw [model_rv_mul, hw, model_mul_inv hxne, model_rv_one]
    have e : x⁻¹ * (x * w) = w := by field_simp
    calc rvMap x⁻¹ = rvMap x⁻¹ * rvMap 1 := by rw [← model_rv_mul, mul_one]
      _ = rvMap x⁻¹ * rvMap (x * w) := by rw [h1]
      _ = rvMap (x⁻¹ * (x * w)) := (model_rv_mul _ _).symm
      _ = rvMap w := by rw [e]
      _ = (rvMap x)⁻¹ := hw

theorem model_add_zero_sum {x y : M RVSort.K} (hxy : valMap (rvMap (x + y)) ≠ 0) :
    rvMap x + rvMap y = 0 := by
  have h := model_rvAxiom M RVAxiom.rvAddZeroSum
  rw [RVAxiom.toSentence] at h
  simpa using h x y hxy

end Axioms

/-! ### The valuation

Mathlib's valuations are multiplicative with `0` at the bottom; the `Γ` sort is additive with
`∞` at the top. `Multiplicative (M Γ)ᵒᵈ` is the passage between the two, and Mathlib already
knows it to be a `LinearOrderedCommGroupWithZero`. Note that it reverses the order, so
`mval ξ ≤ mval η` is `val η ≤ val ξ`. -/

section Valuation

variable [M ⊨ ACVFTheory]

/-- **Nonzero elements have a value below `∞`.** This is the axiom `ball`, read at `x = y`: the
ball of radius `val x` around `x` is nonempty only if `val 0 = ∞` is strictly above `val x`. -/
theorem model_val_ne_top {x : M RVSort.K} (hx : x ≠ 0) : valMap (rvMap x) ≠ ⊤ := by
  have h := (model_ball (x := x) hx).mp rfl
  rw [show x + -x = 0 by ring, model_val_zero] at h
  exact fun hc => h (le_of_eq hc.symm)

theorem model_val_eq_top_iff {x : M RVSort.K} : valMap (rvMap x) = ⊤ ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; exact model_val_zero⟩
  by_contra hx
  exact model_val_ne_top hx h

/-- `val 1 = 0`: the leading term of `1` is idempotent, and its value is not `∞`. -/
theorem model_val_one : valMap (1 : M RVSort.RV) = 0 := by
  have hmul : rvMap (1 : M RVSort.K) * rvMap (1 : M RVSort.K) = rvMap (1 : M RVSort.K) := by
    rw [← model_rv_mul, one_mul]
  have hval := model_val_mul (rvMap (1 : M RVSort.K)) (rvMap (1 : M RVSort.K))
  rw [hmul] at hval
  have hne : valMap (rvMap (1 : M RVSort.K)) ≠ ⊤ := model_val_ne_top one_ne_zero
  have : valMap (rvMap (1 : M RVSort.K)) + 0 = valMap (rvMap (1 : M RVSort.K))
      + valMap (rvMap (1 : M RVSort.K)) := by rw [add_zero]; exact hval
  rw [← model_rv_one]
  exact ((add_right_inj_of_ne_top hne).mp this).symm

variable (M)

/-- The value group of a model, written multiplicatively with `0` at the bottom. -/
abbrev ModelValueGroup : Type w := Multiplicative (M RVSort.Γ)ᵒᵈ

/-- `val`, read as a multiplicative value with zero. -/
def mval (ξ : M RVSort.RV) : ModelValueGroup M :=
  Multiplicative.ofAdd (OrderDual.toDual (valMap ξ))

variable {M}

theorem mval_eq_zero_iff {ξ : M RVSort.RV} : mval M ξ = 0 ↔ valMap ξ = ⊤ := Iff.rfl

theorem mval_eq_one_iff {ξ : M RVSort.RV} : mval M ξ = 1 ↔ valMap ξ = 0 := Iff.rfl

theorem mval_le_iff {ξ η : M RVSort.RV} : mval M ξ ≤ mval M η ↔ valMap η ≤ valMap ξ := Iff.rfl

theorem mval_mul (ξ η : M RVSort.RV) : mval M (ξ * η) = mval M ξ * mval M η := by
  rw [mval, mval, mval, model_val_mul]
  rfl

variable (M)

/-- **The valuation of a model of `ACVF`**: `v x = val (rv x)`, read multiplicatively. -/
noncomputable def modelValuation : Valuation (M RVSort.K) (ModelValueGroup M) where
  toFun x := mval M (rvMap x)
  map_zero' := mval_eq_zero_iff.mpr model_val_zero
  map_one' := mval_eq_one_iff.mpr (by rw [model_rv_one]; exact model_val_one)
  map_mul' x y := by rw [model_rv_mul, mval_mul]
  map_add_le_max' x y := by
    rcases model_ultrametric x y with h | h
    · exact le_max_of_le_left (mval_le_iff.mpr h)
    · exact le_max_of_le_right (mval_le_iff.mpr h)

@[simp]
theorem modelValuation_apply (x : M RVSort.K) : modelValuation M x = mval M (rvMap x) := rfl

/-- **The valuation subring of a model of `ACVF`.** -/
noncomputable def modelValSubring : ValuationSubring (M RVSort.K) :=
  (modelValuation M).valuationSubring

variable {M}

/-- The valuation of a model is nontrivial. -/
theorem modelValuation_nontrivial :
    ∃ x : M RVSort.K, x ≠ 0 ∧ modelValuation M x ≠ 1 := by
  obtain ⟨x, hx0, hx⟩ := model_exists_nontrivial M
  exact ⟨x, hx0, fun hc => hx (mval_eq_one_iff.mp hc)⟩

/-- The model's own valuation and the valuation of the subring it defines agree, in the sense
of `Valuation.IsEquiv`: they have the same order relation, which is all that the leading-term
structure depends on. -/
theorem modelValuation_isEquiv :
    (modelValuation M).IsEquiv (modelValSubring M).valuation :=
  Valuation.isEquiv_valuation_valuationSubring _

end Valuation

end ManySorted.Language
