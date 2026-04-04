import ProdExpr.Semantics

/-!
# Sentence Quantification over All Free Variables

This file provides versions of `Formula.iAlls`, `Formula.iExs`, and `Formula.iExsUnique`
that work for any `L.Formula α` (without finiteness assumptions on `α`), producing
sentences by quantifying over **all** free variables.

## Mechanism

Given `φ : L.Formula α` with `[DecidableEq Sorts] [∀ s, DecidableEq (α s)]`:

1. Restrict to free variables: `φ' := φ.restrictFreeVar FamMap.idₛ : L.Formula φ.freeVarFam`.
   The family `φ.freeVarFam` is automatically finite via `freeVarFamFinite`.

2. Inject into the right of an empty sum:
   `φ'' := φ'.rename Fam.inr : L.Formula (Fam.EmptyFam ⊕ₛ φ.freeVarFam)`.

3. Apply `iAlls`/`iExs`/`iExsUnique` (which require `[Finite (Sigma β)]`, here satisfied
   by `freeVarFamFinite`) to obtain `L.Sentence = L.Formula Fam.EmptyFam`.

## Main Definitions

- `Formula.iAlls_sentence φ` : universally quantify all free variables of `φ`.
- `Formula.iExs_sentence φ`  : existentially quantify all free variables of `φ`.
- `Formula.iExsUnique_sentence φ` : uniquely-existentially quantify all free variables of `φ`.

## Main Results

**Free-variable-assignment forms** (no extra hypothesis needed):

- `Formula.realize_iAlls_sentence_freeVars` :
  `M ⊨ φ.iAlls_sentence ↔ ∀ i : φ.freeVarFam →ₛ M, Formula.Realize (φ.restrictFreeVar idₛ) i`
- `Formula.realize_iExs_sentence_freeVars`
- `Formula.realize_iExsUnique_sentence_freeVars`

**Full-assignment forms** (require `[∀ s, Nonempty (M s)]`):

- `Formula.realize_iAlls_sentence` : `M ⊨ φ.iAlls_sentence ↔ ∀ v : α →ₛ M, φ.Realize v`
- `Formula.realize_iExs_sentence`  : `M ⊨ φ.iExs_sentence ↔ ∃ v : α →ₛ M, φ.Realize v`
-/

universe u v w z u' v'

namespace MSFirstOrder

namespace MSLanguage

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts}
variable {M : Fam.{w} Sorts} [L.MSStructure M]
variable {α : Fam.{u'} Sorts}

open MSStructure MSLanguage Fam Signature BoundedFormula

/-! ## Definitions -/

namespace Formula

section sentence_quantification

variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)]

/-- `iAlls_sentence φ` universally quantifies all free variables of `φ : L.Formula α`,
producing a `L.Sentence`.

Steps: (1) restrict to `φ.freeVarFam`, (2) embed on the right of `EmptyFam`, (3) apply `iAlls`. -/
noncomputable def iAlls_sentence (φ : L.Formula α) : L.Sentence :=
  Formula.iAlls (β := φ.freeVarFam) ((φ.restrictFreeVar FamMap.idₛ).rename Fam.inr)

/-- `iExs_sentence φ` existentially quantifies all free variables of `φ : L.Formula α`,
producing a `L.Sentence`. -/
noncomputable def iExs_sentence (φ : L.Formula α) : L.Sentence :=
  Formula.iExs (β := φ.freeVarFam) ((φ.restrictFreeVar FamMap.idₛ).rename Fam.inr)

/-- `iExsUnique_sentence φ` uniquely-existentially quantifies all free variables of
`φ : L.Formula α`, producing a `L.Sentence`. -/
noncomputable def iExsUnique_sentence (φ : L.Formula α) : L.Sentence :=
  Formula.iExsUnique (β := φ.freeVarFam) ((φ.restrictFreeVar FamMap.idₛ).rename Fam.inr)

end sentence_quantification

end Formula

/-! ## Semantic Correctness -/

namespace Formula

variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)]

/-! ### Free-variable-assignment forms

These characterizations require no nonemptiness assumption. -/

section freevar_forms

/-- `M ⊨ φ.iAlls_sentence` iff `φ.restrictFreeVar id` holds for every
free-variable assignment. -/
theorem realize_iAlls_sentence_freeVars {φ : L.Formula α} :
    M ⊨ φ.iAlls_sentence ↔
    ∀ (i : (φ.freeVarFam : Fam Sorts) →ₛ M),
      Formula.Realize (φ.restrictFreeVar FamMap.idₛ) i := by
  unfold Formula.iAlls_sentence Sentence.Realize
  rw [Formula.realize_iAlls]
  simp only [Formula.Realize, PUnit.default_eq_unit,
    BoundedFormula.realize_rename, Fam.sumElim_inr]

/-- `M ⊨ φ.iExs_sentence` iff there exists a free-variable assignment making
`φ.restrictFreeVar id` hold. -/
theorem realize_iExs_sentence_freeVars {φ : L.Formula α} :
    M ⊨ φ.iExs_sentence ↔
    ∃ (i : (φ.freeVarFam : Fam Sorts) →ₛ M),
      Formula.Realize (φ.restrictFreeVar FamMap.idₛ) i := by
  unfold Formula.iExs_sentence Sentence.Realize
  rw [Formula.realize_iExs]
  simp only [Formula.Realize, PUnit.default_eq_unit,
    BoundedFormula.realize_rename, Fam.sumElim_inr]

/-- `M ⊨ φ.iExsUnique_sentence` iff there is a unique free-variable assignment making
`φ.restrictFreeVar id` hold. -/
theorem realize_iExsUnique_sentence_freeVars {φ : L.Formula α} :
    M ⊨ φ.iExsUnique_sentence ↔
    ∃! (i : (φ.freeVarFam : Fam Sorts) →ₛ M),
      Formula.Realize (φ.restrictFreeVar FamMap.idₛ) i := by
  unfold Formula.iExsUnique_sentence Sentence.Realize
  rw [Formula.realize_iExsUnique]
  simp only [Formula.Realize, PUnit.default_eq_unit,
    BoundedFormula.realize_rename, Fam.sumElim_inr]

end freevar_forms

/-! ### Full-assignment forms

These require `[∀ s, Nonempty (M s)]` to extend free-variable assignments to all of `α`. -/

section full_assign_forms

variable [∀ s, Nonempty (M s)]

/-- Bridge: quantifying over free-variable assignments ↔ quantifying over all `α`-assignments.

- Forward: restrict `v : α →ₛ M` to free variables via `x.val`.
- Backward: extend `i : φ.freeVarFam →ₛ M` to `α` using `Classical.choice` for non-free vars.
-/
private theorem forall_freeVar_iff_forall_assign {φ : L.Formula α} :
    (∀ i : (φ.freeVarFam : Fam Sorts) →ₛ M,
        Formula.Realize (φ.restrictFreeVar FamMap.idₛ) i) ↔
    (∀ v : α →ₛ M, φ.Realize v) := by
  constructor
  · intro h v
    -- Restrict v to free variables
    have key := h ⟨fun s x => v s x.val⟩
    exact (BoundedFormula.realize_restrictFreeVar (σ := nil) φ FamMap.idₛ
              ⟨fun s x => v s x.val⟩ v
              (fun _ _ _ => rfl) default).mp key
  · intro h i
    -- Extend i to all of α using Classical.choice for non-free variables
    refine (BoundedFormula.realize_restrictFreeVar (σ := nil) φ FamMap.idₛ i
              ⟨fun s a =>
                if hm : ⟨s, a⟩ ∈ BoundedFormula.freeVarFinset φ
                then i s ⟨a, hm⟩
                else Classical.choice inferInstance⟩
              ?_ default).mpr (h _)
    intro s a hm
    simp only [FamMap.idₛ_apply', FamMap.mk_apply, dif_pos hm]

/-- Bridge for existentials. -/
private theorem exists_freeVar_iff_exists_assign {φ : L.Formula α} :
    (∃ i : (φ.freeVarFam : Fam Sorts) →ₛ M,
        Formula.Realize (φ.restrictFreeVar FamMap.idₛ) i) ↔
    (∃ v : α →ₛ M, φ.Realize v) := by
  constructor
  · rintro ⟨i, hi⟩
    -- Extend i to all of α
    refine ⟨⟨fun s a =>
              if hm : ⟨s, a⟩ ∈ BoundedFormula.freeVarFinset φ
              then i s ⟨a, hm⟩
              else Classical.choice inferInstance⟩,
            (BoundedFormula.realize_restrictFreeVar (σ := nil) φ FamMap.idₛ i _
              ?_ default).mp hi⟩
    intro s a hm
    simp only [FamMap.idₛ_apply', FamMap.mk_apply, dif_pos hm]
  · rintro ⟨v, hv⟩
    -- Restrict v to free variables
    exact ⟨⟨fun s x => v s x.val⟩,
           (BoundedFormula.realize_restrictFreeVar (σ := nil) φ FamMap.idₛ
              ⟨fun s x => v s x.val⟩ v (fun _ _ _ => rfl) default).mpr hv⟩

/-- `M ⊨ φ.iAlls_sentence` iff `φ` holds for every variable assignment `v : α →ₛ M`. -/
theorem realize_iAlls_sentence {φ : L.Formula α} :
    M ⊨ φ.iAlls_sentence ↔ ∀ v : α →ₛ M, φ.Realize v := by
  rw [realize_iAlls_sentence_freeVars, forall_freeVar_iff_forall_assign]

/-- `M ⊨ φ.iExs_sentence` iff `φ` holds for some variable assignment `v : α →ₛ M`. -/
theorem realize_iExs_sentence {φ : L.Formula α} :
    M ⊨ φ.iExs_sentence ↔ ∃ v : α →ₛ M, φ.Realize v := by
  rw [realize_iExs_sentence_freeVars, exists_freeVar_iff_exists_assign]

end full_assign_forms

end Formula

end MSLanguage

end MSFirstOrder
