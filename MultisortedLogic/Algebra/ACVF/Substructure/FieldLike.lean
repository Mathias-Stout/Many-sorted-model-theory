/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Theory.Model
public import MultisortedLogic.Substructures

/-!
# Field-like substructures of a model of `ACVF`

Rideau-Kikuchi's argument runs over a *valued subfield*: a subfield `F` of the field sort, together
with its leading terms and their values. This file makes that a substructure of the ambient model in
the sense of `Substructures.lean`, so that the embedding test of `EmbeddingTest.lean` can be fed
with it.

That the three sorts of `fieldCarrier F` really are closed under every symbol of `L_RV` is where
the axioms of `ACVFTheory` are spent, and in particular the axioms for the operations of the `RV`
sort: the `RV`-part is `rv '' F`, and it has to be closed under the `RV`-sort's own addition and
negation, which is exactly what `rvAddRes`, `rvAddZeroL/R/Sum` and `negRV` say.

Both halves of the proof then work with embeddings of such substructures as purely algebraic data,
and this file sets up that dictionary: an `L_RV`-embedding of a field-like substructure is the
same thing as a ring homomorphism of the subfield reflecting equality of leading terms and the
order of values (`FieldEmbeddingData`). It also provides the two ways of enlarging the field part
of an arbitrary substructure without touching its `RV`- and `Γ`-parts, which `RVLift` iterates:
adjoining a subring (`adjoinSubstructure`, `adjoinEmbedding`) and passing to the fraction field
(`fracAdjoin`, `fracEmbedding`).

## Main definitions

* `Language.fieldCarrier`, `Language.fieldSubstructure` : the substructure attached to a subfield.
* `Language.FieldEmbeddingData` : the algebraic data of an embedding of a field-like substructure,
  with `FieldEmbeddingData.toEmbedding` and `FieldEmbeddingData.ofEmbedding` the two directions.
* `Language.subringOfSubstructure` : the field-sort part of a substructure, as a subring.
* `Language.adjoinSubstructure`, `Language.adjoinEmbedding` : a larger field part, with the same
  `RV`- and `Γ`-parts, and an embedding of it from a ring homomorphism.
* `Language.fracAdjoin`, `Language.fracEmbedding` : the same for the fraction field.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]

/-! ### Two more facts about the value group of a model -/

/-- In a linearly ordered abelian group with top, an element other than `⊤` has a unique
additive inverse. -/
theorem eq_neg_of_add_eq_zero_of_ne_top {G : Type*} [LinearOrderedAddCommGroupWithTop G]
    {a b : G} (ha : a ≠ ⊤) (h : a + b = 0) : b = -a := by
  calc b = 0 + b := (zero_add b).symm
    _ = (-a + a) + b := by
        rw [add_comm (-a) a, LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top ha]
    _ = -a + (a + b) := add_assoc _ _ _
    _ = -a := by rw [h, add_zero]

/-- The negative of a value is the value of the inverse. -/
theorem model_neg_val (x : M RVSort.K) : -(valMap (rvMap x)) = valMap (rvMap x⁻¹) := by
  by_cases hx : x = 0
  · subst hx
    rw [model_val_zero, LinearOrderedAddCommGroupWithTop.neg_top, inv_zero, model_val_zero]
  · have hsum : valMap (rvMap x) + valMap (rvMap x⁻¹) = 0 := by
      rw [← model_val_mul, ← model_rv_mul, mul_inv_cancel₀ hx, model_rv_one, model_val_one]
    exact (eq_neg_of_add_eq_zero_of_ne_top (model_val_ne_top hx) hsum).symm

/-! ### The substructure attached to a subfield -/

variable (M)

/-- The family of sets attached to a subfield of the field sort: the subfield, its leading terms,
and their values. -/
noncomputable def fieldCarrier (F : Subfield (M RVSort.K)) : ∀ s, Set (M s)
  | RVSort.K => (F : Set (M RVSort.K))
  | RVSort.RV => rvMap '' (F : Set (M RVSort.K))
  | RVSort.Γ => (fun x => valMap (rvMap x)) '' (F : Set (M RVSort.K))

variable {M}

@[simp]
theorem mem_fieldCarrier_K {F : Subfield (M RVSort.K)} {x : M RVSort.K} :
    x ∈ fieldCarrier M F RVSort.K ↔ x ∈ F := Iff.rfl

@[simp]
theorem mem_fieldCarrier_RV {F : Subfield (M RVSort.K)} {ξ : M RVSort.RV} :
    ξ ∈ fieldCarrier M F RVSort.RV ↔ ∃ x ∈ F, rvMap x = ξ := Iff.rfl

@[simp]
theorem mem_fieldCarrier_Gamma {F : Subfield (M RVSort.K)} {γ : M RVSort.Γ} :
    γ ∈ fieldCarrier M F RVSort.Γ ↔ ∃ x ∈ F, valMap (rvMap x) = γ := Iff.rfl


/-! ### Closure of `fieldCarrier` under the operations -/

@[simp]
theorem model_rv_zero : rvMap (0 : M RVSort.K) = 0 := model_rv_eq_zero_iff.mpr rfl

/-- The `RV`-part of a subfield is closed under the `RV`-sort's addition. This is where the
axioms `rvAddRes` and `rvAddZeroL/R/Sum` are used: the sum is either the leading term of the sum
of the representatives, which stays in the subfield, or `0 = rv 0`. -/
theorem rvMap_add_mem {F : Subfield (M RVSort.K)} {x y : M RVSort.K} (hx : x ∈ F) (hy : y ∈ F) :
    ∃ z ∈ F, rvMap x + rvMap y = rvMap z := by
  by_cases h1 : valMap (rvMap x) = 0 ∨ x = 0
  · by_cases h2 : valMap (rvMap y) = 0 ∨ y = 0
    · by_cases h3 : valMap (rvMap (x + y)) = 0
      · exact ⟨x + y, F.add_mem hx hy, model_add_res h1 h2 h3⟩
      · exact ⟨0, F.zero_mem, by rw [model_add_zero_sum h3, model_rv_zero]⟩
    · obtain ⟨ha, hb⟩ := not_or.mp h2
      exact ⟨0, F.zero_mem, by rw [model_add_zero_right x ha hb, model_rv_zero]⟩
  · obtain ⟨ha, hb⟩ := not_or.mp h1
    exact ⟨0, F.zero_mem, by rw [model_add_zero_left y ha hb, model_rv_zero]⟩

/-- The `RV`-part of a subfield is closed under the `RV`-sort's negation (axiom `negRV`). -/
theorem rvMap_neg_mem {x : M RVSort.K} : -(rvMap x) = rvMap (-x) := by
  rw [model_neg_rv, ← model_rv_mul, neg_one_mul]

variable (M)

/-- **The family of sets attached to a subfield is a substructure.** -/
noncomputable def fieldSubstructure (F : Subfield (M RVSort.K)) : rvLang.Substructure M where
  carrier := fieldCarrier M F
  fun_mem := by
    intro σ t f x hx
    match t, σ, f with
    | _, _, .zeroK => exact F.zero_mem
    | _, _, .oneK => exact F.one_mem
    | _, _, .negK => exact F.neg_mem (hx RVSort.K Idx.var)
    | _, _, .addK =>
      exact F.add_mem (hx RVSort.K (Idx.left Idx.var))
        (hx RVSort.K (Idx.right Idx.var))
    | _, _, .mulK =>
      exact F.mul_mem (hx RVSort.K (Idx.left Idx.var))
        (hx RVSort.K (Idx.right Idx.var))
    | _, _, .zeroRV => exact ⟨0, F.zero_mem, model_rv_zero⟩
    | _, _, .oneRV => exact ⟨1, F.one_mem, model_rv_one⟩
    | _, _, .negRV =>
      obtain ⟨a, ha, hax⟩ := hx RVSort.RV Idx.var
      refine ⟨-a, F.neg_mem ha, ?_⟩
      have hf : funMap (L := rvLang) RVFunc.negRV x
          = -(x.get RVSort.RV Idx.var) := rfl
      rw [hf, ← hax, rvMap_neg_mem]
    | _, _, .addRV =>
      obtain ⟨a, ha, hax⟩ := hx RVSort.RV (Idx.left Idx.var)
      obtain ⟨b, hb, hbx⟩ := hx RVSort.RV (Idx.right Idx.var)
      obtain ⟨z, hz, hzeq⟩ := rvMap_add_mem ha hb
      refine ⟨z, hz, ?_⟩
      have hf : funMap (L := rvLang) RVFunc.addRV x
          = x.get RVSort.RV (Idx.left Idx.var)
            + x.get RVSort.RV (Idx.right Idx.var) := rfl
      rw [hf, ← hax, ← hbx]
      exact hzeq.symm
    | _, _, .invRV =>
      obtain ⟨a, ha, hax⟩ := hx RVSort.RV Idx.var
      refine ⟨a⁻¹, F.inv_mem ha, ?_⟩
      have hf : funMap (L := rvLang) RVFunc.invRV x
          = (x.get RVSort.RV Idx.var)⁻¹ := rfl
      rw [hf, ← hax, model_rv_inv]
    | _, _, .mulRV =>
      obtain ⟨a, ha, hax⟩ := hx RVSort.RV (Idx.left Idx.var)
      obtain ⟨b, hb, hbx⟩ := hx RVSort.RV (Idx.right Idx.var)
      refine ⟨a * b, F.mul_mem ha hb, ?_⟩
      have hf : funMap (L := rvLang) RVFunc.mulRV x
          = x.get RVSort.RV (Idx.left Idx.var)
            * x.get RVSort.RV (Idx.right Idx.var) := rfl
      rw [hf, ← hax, ← hbx, model_rv_mul]
    | _, _, .zeroΓ =>
      refine ⟨1, F.one_mem, ?_⟩
      change valMap (rvMap (1 : M RVSort.K)) = funMap (L := rvLang) RVFunc.zeroΓ x
      rw [model_rv_one, model_val_one]
      rfl
    | _, _, .inftyΓ =>
      refine ⟨0, F.zero_mem, ?_⟩
      change valMap (rvMap (0 : M RVSort.K)) = funMap (L := rvLang) RVFunc.inftyΓ x
      rw [model_val_zero]
      rfl
    | _, _, .negΓ =>
      obtain ⟨a, ha, hax⟩ := hx RVSort.Γ Idx.var
      refine ⟨a⁻¹, F.inv_mem ha, ?_⟩
      change valMap (rvMap a⁻¹) = funMap (L := rvLang) RVFunc.negΓ x
      have hf : funMap (L := rvLang) RVFunc.negΓ x
          = -(x.get RVSort.Γ Idx.var) := rfl
      rw [hf, ← hax, model_neg_val]
    | _, _, .addΓ =>
      obtain ⟨a, ha, hax⟩ := hx RVSort.Γ (Idx.left Idx.var)
      obtain ⟨b, hb, hbx⟩ := hx RVSort.Γ (Idx.right Idx.var)
      refine ⟨a * b, F.mul_mem ha hb, ?_⟩
      change valMap (rvMap (a * b)) = funMap (L := rvLang) RVFunc.addΓ x
      have hf : funMap (L := rvLang) RVFunc.addΓ x
          = x.get RVSort.Γ (Idx.left Idx.var)
            + x.get RVSort.Γ (Idx.right Idx.var) := rfl
      rw [hf, ← hax, ← hbx, model_rv_mul, model_val_mul]
    | _, _, .rv =>
      exact ⟨_, hx RVSort.K Idx.var, rfl⟩
    | _, _, .val =>
      obtain ⟨a, ha, hax⟩ := hx RVSort.RV Idx.var
      refine ⟨a, ha, ?_⟩
      change valMap (rvMap a) = funMap (L := rvLang) RVFunc.val x
      have hf : funMap (L := rvLang) RVFunc.val x
          = valMap (x.get RVSort.RV Idx.var) := rfl
      rw [hf, ← hax]

variable {M}

theorem fieldCarrier_mono {F F' : Subfield (M RVSort.K)} (h : F ≤ F') :
    fieldCarrier M F ≤ fieldCarrier M F' := by
  intro s x hx
  match s with
  | RVSort.K => exact h hx
  | RVSort.RV => obtain ⟨a, ha, rfl⟩ := hx; exact ⟨a, h ha, rfl⟩
  | RVSort.Γ => obtain ⟨a, ha, rfl⟩ := hx; exact ⟨a, h ha, rfl⟩

theorem mem_fieldSubstructure_RV {F : Subfield (M RVSort.K)} {ξ : M RVSort.RV} :
    ξ ∈ fieldSubstructure M F RVSort.RV ↔ ∃ x ∈ F, rvMap x = ξ := Iff.rfl

theorem mem_fieldSubstructure_Gamma {F : Subfield (M RVSort.K)} {γ : M RVSort.Γ} :
    γ ∈ fieldSubstructure M F RVSort.Γ ↔ ∃ x ∈ F, valMap (rvMap x) = γ := Iff.rfl

theorem fieldSubstructure_mono {F F' : Subfield (M RVSort.K)} (h : F ≤ F') :
    fieldSubstructure M F ≤ fieldSubstructure M F' :=
  fieldCarrier_mono h

@[simp]
theorem coe_fieldSubstructure (F : Subfield (M RVSort.K)) :
    ⇑(fieldSubstructure M F) = fieldCarrier M F := rfl


/-! ### Algebraic data gives an embedding

An embedding of a field-like substructure is determined by its field-sort part. The data is a ring
homomorphism of the subfield into the field sort of the target which reflects equality of leading
terms and the order of their values — that is, a valued-field embedding. Everything else follows,
including compatibility with the `RV` sort's own addition, because the axioms for the operations of
the `RV` sort determine it from `rv`. -/

section Bridge

variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]

/-- **Algebraic data for an embedding of a field-like substructure**: a ring homomorphism of the
subfield which reflects equality of leading terms and the order of their values. -/
structure FieldEmbeddingData (F : Subfield (M RVSort.K)) (N : RVSort → Type w)
    [rvLang.Structure N] [N ⊨ ACVFTheory] where
  /-- The ring homomorphism on the field sort. -/
  hom : F →+* N RVSort.K
  /-- It reflects equality of leading terms. -/
  rv_iff : ∀ x y : F,
    (rvMap (x : M RVSort.K) = rvMap (y : M RVSort.K) ↔ rvMap (hom x) = rvMap (hom y))
  /-- It reflects the order of values. -/
  val_iff : ∀ x y : F,
    (valMap (rvMap (x : M RVSort.K)) ≤ valMap (rvMap (y : M RVSort.K))
      ↔ valMap (rvMap (hom x)) ≤ valMap (rvMap (hom y)))

namespace FieldEmbeddingData

variable {F : Subfield (M RVSort.K)} (d : FieldEmbeddingData F N)

theorem val_eq_iff (x y : F) :
    valMap (rvMap (x : M RVSort.K)) = valMap (rvMap (y : M RVSort.K))
      ↔ valMap (rvMap (d.hom x)) = valMap (rvMap (d.hom y)) := by
  constructor
  · intro h
    exact le_antisymm ((d.val_iff x y).mp (le_of_eq h)) ((d.val_iff y x).mp (le_of_eq h.symm))
  · intro h
    exact le_antisymm ((d.val_iff x y).mpr (le_of_eq h)) ((d.val_iff y x).mpr (le_of_eq h.symm))

/-- The `RV`-component of the embedding. -/
noncomputable def rvComp (m : ↥(fieldSubstructure M F RVSort.RV)) : N RVSort.RV :=
  rvMap (d.hom ⟨Classical.choose (mem_fieldSubstructure_RV.1 m.2),
    (Classical.choose_spec (mem_fieldSubstructure_RV.1 m.2)).1⟩)

/-- The `Γ`-component of the embedding. -/
noncomputable def gammaComp (m : ↥(fieldSubstructure M F RVSort.Γ)) : N RVSort.Γ :=
  valMap (rvMap (d.hom ⟨Classical.choose (mem_fieldSubstructure_Gamma.1 m.2),
    (Classical.choose_spec (mem_fieldSubstructure_Gamma.1 m.2)).1⟩))

@[simp]
theorem rvComp_apply {x : M RVSort.K} (hx : x ∈ F)
    (h : rvMap x ∈ fieldSubstructure M F RVSort.RV) :
    d.rvComp ⟨rvMap x, h⟩ = rvMap (d.hom ⟨x, hx⟩) := by
  obtain ⟨hc1, hc2⟩ := Classical.choose_spec (mem_fieldSubstructure_RV.1 h)
  exact (d.rv_iff ⟨_, hc1⟩ ⟨x, hx⟩).mp hc2

@[simp]
theorem gammaComp_apply {x : M RVSort.K} (hx : x ∈ F)
    (h : valMap (rvMap x) ∈ fieldSubstructure M F RVSort.Γ) :
    d.gammaComp ⟨valMap (rvMap x), h⟩ = valMap (rvMap (d.hom ⟨x, hx⟩)) := by
  obtain ⟨hc1, hc2⟩ := Classical.choose_spec (mem_fieldSubstructure_Gamma.1 h)
  exact (d.val_eq_iff ⟨_, hc1⟩ ⟨x, hx⟩).mp hc2

theorem hom_injective : Function.Injective d.hom := (d.hom).injective

theorem eq_zero_iff (x : F) : (x : M RVSort.K) = 0 ↔ d.hom x = 0 := by
  constructor
  · intro h
    rw [show x = 0 from Subtype.ext h, map_zero]
  · intro h
    exact congrArg Subtype.val (d.hom_injective (h.trans (map_zero d.hom).symm))

theorem val_eq_zero_iff (x : F) :
    valMap (rvMap (x : M RVSort.K)) = 0 ↔ valMap (rvMap (d.hom x)) = 0 := by
  have e1 : (0 : M RVSort.Γ) = valMap (rvMap (1 : M RVSort.K)) := by
    rw [model_rv_one, model_val_one]
  have e2 : (0 : N RVSort.Γ) = valMap (rvMap (1 : N RVSort.K)) := by
    rw [model_rv_one, model_val_one]
  rw [e1, e2, show (1 : N RVSort.K) = d.hom 1 from (map_one d.hom).symm]
  exact d.val_eq_iff x 1

theorem res_iff (x : F) :
    ((valMap (rvMap (x : M RVSort.K)) = 0 ∨ (x : M RVSort.K) = 0)
      ↔ (valMap (rvMap (d.hom x)) = 0 ∨ d.hom x = 0)) :=
  or_congr (d.val_eq_zero_iff x) (d.eq_zero_iff x)

/-- The `RV`-sort addition is carried along: the case of `rvAdd` that applies on one side
applies on the other, because both cases are governed by conditions that `d` reflects. -/
theorem exists_rv_add (x y : F) :
    ∃ z : F, rvMap (x : M RVSort.K) + rvMap (y : M RVSort.K) = rvMap (z : M RVSort.K) ∧
      rvMap (d.hom x) + rvMap (d.hom y) = rvMap (d.hom z) := by
  have hcoe : ((x + y : F) : M RVSort.K) = (x : M RVSort.K) + (y : M RVSort.K) := rfl
  have hhom : d.hom (x + y) = d.hom x + d.hom y := map_add d.hom x y
  by_cases h1 : valMap (rvMap (x : M RVSort.K)) = 0 ∨ (x : M RVSort.K) = 0
  · by_cases h2 : valMap (rvMap (y : M RVSort.K)) = 0 ∨ (y : M RVSort.K) = 0
    · by_cases h3 : valMap (rvMap ((x : M RVSort.K) + (y : M RVSort.K))) = 0
      · have h3' : valMap (rvMap (d.hom x + d.hom y)) = 0 := by
          rw [← hhom]
          exact (d.val_eq_zero_iff (x + y)).mp (by rw [hcoe]; exact h3)
        exact ⟨x + y, by rw [hcoe]; exact model_add_res h1 h2 h3,
          by rw [hhom]; exact model_add_res ((d.res_iff x).mp h1) ((d.res_iff y).mp h2) h3'⟩
      · have h3' : valMap (rvMap (d.hom x + d.hom y)) ≠ 0 := by
          rw [← hhom]
          exact fun hc => h3 (by
            rw [← hcoe]
            exact (d.val_eq_zero_iff (x + y)).mpr hc)
        refine ⟨0, ?_, ?_⟩
        · rw [model_add_zero_sum h3]
          exact (model_rv_zero (M := M)).symm
        · rw [model_add_zero_sum h3', map_zero]
          exact (model_rv_zero (M := N)).symm
    · obtain ⟨ha, hb⟩ := not_or.mp h2
      obtain ⟨ha', hb'⟩ := not_or.mp (fun hc => h2 ((d.res_iff y).mpr hc))
      refine ⟨0, ?_, ?_⟩
      · rw [model_add_zero_right _ ha hb]
        exact (model_rv_zero (M := M)).symm
      · rw [model_add_zero_right _ ha' hb', map_zero]
        exact (model_rv_zero (M := N)).symm
  · obtain ⟨ha, hb⟩ := not_or.mp h1
    obtain ⟨ha', hb'⟩ := not_or.mp (fun hc => h1 ((d.res_iff x).mpr hc))
    refine ⟨0, ?_, ?_⟩
    · rw [model_add_zero_left _ ha hb]
      exact (model_rv_zero (M := M)).symm
    · rw [model_add_zero_left _ ha' hb', map_zero]
      exact (model_rv_zero (M := N)).symm




theorem rvComp_eq {m : ↥(fieldSubstructure M F RVSort.RV)} {a : M RVSort.K} (ha : a ∈ F)
    (h : rvMap a = m.1) : d.rvComp m = rvMap (d.hom ⟨a, ha⟩) := by
  obtain ⟨ξ, hξ⟩ := m
  subst h
  exact d.rvComp_apply ha hξ

theorem gammaComp_eq {m : ↥(fieldSubstructure M F RVSort.Γ)} {a : M RVSort.K} (ha : a ∈ F)
    (h : valMap (rvMap a) = m.1) : d.gammaComp m = valMap (rvMap (d.hom ⟨a, ha⟩)) := by
  obtain ⟨γ, hγ⟩ := m
  subst h
  exact d.gammaComp_apply ha hγ

theorem rvComp_injective : Function.Injective d.rvComp := by
  rintro ⟨ξ, hξ⟩ ⟨η, hη⟩ h
  obtain ⟨a, ha, hae⟩ := id hξ
  obtain ⟨b, hb, hbe⟩ := id hη
  subst hae
  subst hbe
  rw [d.rvComp_apply ha, d.rvComp_apply hb] at h
  exact Subtype.ext ((d.rv_iff ⟨a, ha⟩ ⟨b, hb⟩).mpr h)

theorem gammaComp_injective : Function.Injective d.gammaComp := by
  rintro ⟨γ, hγ⟩ ⟨δ, hδ⟩ h
  obtain ⟨a, ha, hae⟩ := id hγ
  obtain ⟨b, hb, hbe⟩ := id hδ
  subst hae
  subst hbe
  rw [d.gammaComp_apply ha, d.gammaComp_apply hb] at h
  exact Subtype.ext ((d.val_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).mpr h)

/-- **The embedding attached to the algebraic data.** -/
noncomputable def toEmbedding : (fun s => ↥(fieldSubstructure M F s)) ↪[rvLang] N where
  toEmbedding
    | RVSort.K => ⟨fun m => d.hom ⟨m.1, m.2⟩,
        fun _ _ h => Subtype.ext (congrArg Subtype.val (d.hom_injective h))⟩
    | RVSort.RV => ⟨d.rvComp, d.rvComp_injective⟩
    | RVSort.Γ => ⟨d.gammaComp, d.gammaComp_injective⟩
  map_fun' := by
    intro σ t f x
    match t, σ, f with
    | _, _, .zeroK => exact map_zero d.hom
    | _, _, .oneK => exact map_one d.hom
    | _, _, .negK => exact map_neg d.hom _
    | _, _, .addK => exact map_add d.hom _ _
    | _, _, .mulK => exact map_mul d.hom _ _
    | _, _, .zeroRV =>
      change d.rvComp _ = (0 : N RVSort.RV)
      rw [d.rvComp_eq F.zero_mem (a := (0 : M RVSort.K)) model_rv_zero]
      change rvMap (d.hom (0 : F)) = (0 : N RVSort.RV)
      rw [map_zero, model_rv_zero]
    | _, _, .oneRV =>
      change d.rvComp _ = (1 : N RVSort.RV)
      rw [d.rvComp_eq F.one_mem (a := (1 : M RVSort.K)) model_rv_one]
      change rvMap (d.hom (1 : F)) = (1 : N RVSort.RV)
      rw [map_one, model_rv_one]
    | _, _, .negRV =>
      obtain ⟨a, ha, hae⟩ := id (x.get RVSort.RV Idx.var).2
      change d.rvComp (_)
        = -(d.rvComp (x.get RVSort.RV Idx.var))
      rw [d.rvComp_eq (F.neg_mem ha) (a := -a) (by rw [← rvMap_neg_mem, hae]; rfl),
        d.rvComp_eq ha hae]
      change rvMap (d.hom (-(⟨a, ha⟩ : F))) = -(rvMap (d.hom ⟨a, ha⟩))
      rw [map_neg, rvMap_neg_mem]
    | _, _, .addRV =>
      obtain ⟨a, ha, hae⟩ := id (x.get RVSort.RV (Idx.left Idx.var)).2
      obtain ⟨b, hb, hbe⟩ := id (x.get RVSort.RV (Idx.right Idx.var)).2
      obtain ⟨z, hz1, hz2⟩ := d.exists_rv_add ⟨a, ha⟩ ⟨b, hb⟩
      change d.rvComp (_)
        = d.rvComp (x.get RVSort.RV (Idx.left Idx.var))
          + d.rvComp (x.get RVSort.RV (Idx.right Idx.var))
      rw [d.rvComp_eq z.2 (a := (z : M RVSort.K)) (by rw [← hz1, hae, hbe]; rfl),
        d.rvComp_eq ha hae, d.rvComp_eq hb hbe]
      exact hz2.symm
    | _, _, .invRV =>
      obtain ⟨a, ha, hae⟩ := id (x.get RVSort.RV Idx.var).2
      change d.rvComp _ = (d.rvComp (x.get RVSort.RV Idx.var))⁻¹
      rw [d.rvComp_eq (F.inv_mem ha) (a := a⁻¹) (by rw [model_rv_inv, hae]; rfl),
        d.rvComp_eq ha hae]
      change rvMap (d.hom ((⟨a, ha⟩ : F)⁻¹)) = (rvMap (d.hom ⟨a, ha⟩))⁻¹
      rw [map_inv₀, model_rv_inv]
    | _, _, .mulRV =>
      obtain ⟨a, ha, hae⟩ := id (x.get RVSort.RV (Idx.left Idx.var)).2
      obtain ⟨b, hb, hbe⟩ := id (x.get RVSort.RV (Idx.right Idx.var)).2
      change d.rvComp (_)
        = d.rvComp (x.get RVSort.RV (Idx.left Idx.var))
          * d.rvComp (x.get RVSort.RV (Idx.right Idx.var))
      rw [d.rvComp_eq (F.mul_mem ha hb) (a := a * b) (by rw [model_rv_mul, hae, hbe]; rfl),
        d.rvComp_eq ha hae, d.rvComp_eq hb hbe]
      change rvMap (d.hom ((⟨a, ha⟩ : F) * ⟨b, hb⟩)) = _
      rw [map_mul, model_rv_mul]
    | _, _, .zeroΓ =>
      change d.gammaComp _ = (0 : N RVSort.Γ)
      rw [d.gammaComp_eq F.one_mem (a := (1 : M RVSort.K))
        (by rw [model_rv_one, model_val_one]; rfl)]
      change valMap (rvMap (d.hom (1 : F))) = (0 : N RVSort.Γ)
      rw [map_one, model_rv_one, model_val_one]
    | _, _, .inftyΓ =>
      change d.gammaComp _ = (⊤ : N RVSort.Γ)
      rw [d.gammaComp_eq F.zero_mem (a := (0 : M RVSort.K)) (by rw [model_val_zero]; rfl)]
      change valMap (rvMap (d.hom (0 : F))) = (⊤ : N RVSort.Γ)
      rw [map_zero, model_val_zero]
    | _, _, .negΓ =>
      obtain ⟨a, ha, hae0⟩ := id (x.get RVSort.Γ Idx.var).2
      have hae : valMap (rvMap a) = (x.get RVSort.Γ Idx.var).1 := hae0
      change d.gammaComp (_)
        = -(d.gammaComp (x.get RVSort.Γ Idx.var))
      rw [d.gammaComp_eq (F.inv_mem ha) (a := a⁻¹) (by rw [← model_neg_val, hae]; rfl),
        d.gammaComp_eq ha hae]
      change valMap (rvMap (d.hom ((⟨a, ha⟩ : F)⁻¹))) = -(valMap (rvMap (d.hom ⟨a, ha⟩)))
      rw [map_inv₀, model_neg_val]
    | _, _, .addΓ =>
      obtain ⟨a, ha, hae0⟩ := id (x.get RVSort.Γ (Idx.left Idx.var)).2
      obtain ⟨b, hb, hbe0⟩ := id (x.get RVSort.Γ (Idx.right Idx.var)).2
      have hae : valMap (rvMap a)
        = (x.get RVSort.Γ (Idx.left Idx.var)).1 := hae0
      have hbe : valMap (rvMap b)
        = (x.get RVSort.Γ (Idx.right Idx.var)).1 := hbe0
      change d.gammaComp (_)
        = d.gammaComp (x.get RVSort.Γ (Idx.left Idx.var))
          + d.gammaComp (x.get RVSort.Γ (Idx.right Idx.var))
      rw [d.gammaComp_eq (F.mul_mem ha hb) (a := a * b)
          (by rw [model_rv_mul, model_val_mul, hae, hbe]; rfl),
        d.gammaComp_eq ha hae, d.gammaComp_eq hb hbe]
      change valMap (rvMap (d.hom ((⟨a, ha⟩ : F) * ⟨b, hb⟩))) = _
      rw [map_mul, model_rv_mul, model_val_mul]
    | _, _, .rv =>
      change d.rvComp (_)
        = rvMap (d.hom ⟨(x.get RVSort.K Idx.var).1,
            (x.get RVSort.K Idx.var).2⟩)
      exact d.rvComp_eq (x.get RVSort.K Idx.var).2 rfl
    | _, _, .val =>
      obtain ⟨a, ha, hae⟩ := id (x.get RVSort.RV Idx.var).2
      change d.gammaComp (_)
        = valMap (d.rvComp (x.get RVSort.RV Idx.var))
      rw [d.gammaComp_eq ha (by rw [hae]; rfl), d.rvComp_eq ha hae]
  map_rel' := by
    intro σ r x
    match σ, r with
    | _, .leΓ =>
      obtain ⟨a, ha, hae⟩ := id x.1.2
      obtain ⟨b, hb, hbe⟩ := id x.2.2
      change d.gammaComp x.1 ≤ d.gammaComp x.2 ↔ _
      rw [d.gammaComp_eq ha hae, d.gammaComp_eq hb hbe]
      change _ ↔ (x.1 : ↥(fieldSubstructure M F RVSort.Γ)).1 ≤ (x.2).1
      rw [← hae, ← hbe]
      exact (d.val_iff ⟨a, ha⟩ ⟨b, hb⟩).symm

end FieldEmbeddingData


/-! ### An embedding gives algebraic data

The converse of `toEmbedding`. Together they say that `L_RV`-embeddings of a field-like
substructure and valued-field embeddings of the subfield are the same thing, which is the
interface the algebra works through. -/

section OfEmbedding

variable {F : Subfield (M RVSort.K)} (h : (fun s => ↥(fieldSubstructure M F s)) ↪[rvLang] N)

omit [N ⊨ ACVFTheory] in
/-- The embedding commutes with `rv`. -/
theorem emb_rvMap {x : M RVSort.K} (hx : x ∈ F) (hrv : rvMap x ∈ fieldSubstructure M F RVSort.RV) :
    h RVSort.RV ⟨rvMap x, hrv⟩ = rvMap (h RVSort.K ⟨x, hx⟩) :=
  h.map_fun' RVFunc.rv (⟨x, hx⟩ : ↥(fieldSubstructure M F RVSort.K))

omit [N ⊨ ACVFTheory] in
/-- The embedding commutes with `val`. -/
theorem emb_valMap {ξ : M RVSort.RV} (hξ : ξ ∈ fieldSubstructure M F RVSort.RV)
    (hv : valMap ξ ∈ fieldSubstructure M F RVSort.Γ) :
    h RVSort.Γ ⟨valMap ξ, hv⟩ = valMap (h RVSort.RV ⟨ξ, hξ⟩) :=
  h.map_fun' RVFunc.val (⟨ξ, hξ⟩ : ↥(fieldSubstructure M F RVSort.RV))

/-- The embedding reflects the order of the value sort. -/
theorem emb_le_iff {γ δ : M RVSort.Γ} (hγ : γ ∈ fieldSubstructure M F RVSort.Γ)
    (hδ : δ ∈ fieldSubstructure M F RVSort.Γ) :
    h RVSort.Γ ⟨γ, hγ⟩ ≤ h RVSort.Γ ⟨δ, hδ⟩ ↔ γ ≤ δ :=
  h.map_rel' RVRel.leΓ
    ((⟨γ, hγ⟩, ⟨δ, hδ⟩) : (fun s => ↥(fieldSubstructure M F s)) [^] (⦃RVSort.Γ⦄ ⨯ ⦃RVSort.Γ⦄))

/-- The ring homomorphism carried by an embedding of a field-like substructure. -/
noncomputable def embHom : F →+* N RVSort.K where
  toFun x := h RVSort.K ⟨x.1, x.2⟩
  map_one' := h.map_fun' RVFunc.oneK default
  map_zero' := h.map_fun' RVFunc.zeroK default
  map_add' x y := h.map_fun' RVFunc.addK
    ((⟨x.1, x.2⟩, ⟨y.1, y.2⟩) : (fun s => ↥(fieldSubstructure M F s)) [^] (⦃RVSort.K⦄ ⨯ ⦃RVSort.K⦄))
  map_mul' x y := h.map_fun' RVFunc.mulK
    ((⟨x.1, x.2⟩, ⟨y.1, y.2⟩) : (fun s => ↥(fieldSubstructure M F s)) [^] (⦃RVSort.K⦄ ⨯ ⦃RVSort.K⦄))

@[simp]
theorem embHom_apply (x : F) : embHom h x = h RVSort.K ⟨x.1, x.2⟩ := rfl

/-- **An `L_RV`-embedding of a field-like substructure is a valued-field embedding.** -/
noncomputable def FieldEmbeddingData.ofEmbedding : FieldEmbeddingData F N where
  hom := embHom h
  rv_iff x y := by
    have hx : rvMap (x : M RVSort.K) ∈ fieldSubstructure M F RVSort.RV := ⟨x.1, x.2, rfl⟩
    have hy : rvMap (y : M RVSort.K) ∈ fieldSubstructure M F RVSort.RV := ⟨y.1, y.2, rfl⟩
    change rvMap (x : M RVSort.K) = rvMap (y : M RVSort.K)
      ↔ rvMap (h RVSort.K ⟨x.1, x.2⟩) = rvMap (h RVSort.K ⟨y.1, y.2⟩)
    rw [← emb_rvMap h x.2 hx, ← emb_rvMap h y.2 hy]
    exact ⟨fun hc => congrArg _ (Subtype.ext hc),
      fun hc => congrArg Subtype.val (h.injective RVSort.RV hc)⟩
  val_iff x y := by
    have hx : rvMap (x : M RVSort.K) ∈ fieldSubstructure M F RVSort.RV := ⟨x.1, x.2, rfl⟩
    have hy : rvMap (y : M RVSort.K) ∈ fieldSubstructure M F RVSort.RV := ⟨y.1, y.2, rfl⟩
    have hgx : valMap (rvMap (x : M RVSort.K)) ∈ fieldSubstructure M F RVSort.Γ := ⟨x.1, x.2, rfl⟩
    have hgy : valMap (rvMap (y : M RVSort.K)) ∈ fieldSubstructure M F RVSort.Γ := ⟨y.1, y.2, rfl⟩
    change valMap (rvMap (x : M RVSort.K)) ≤ valMap (rvMap (y : M RVSort.K))
      ↔ valMap (rvMap (h RVSort.K ⟨x.1, x.2⟩)) ≤ valMap (rvMap (h RVSort.K ⟨y.1, y.2⟩))
    rw [← emb_rvMap h x.2 hx, ← emb_rvMap h y.2 hy, ← emb_valMap h hx hgx,
      ← emb_valMap h hy hgy]
    exact (emb_le_iff h hgx hgy).symm

@[simp]
theorem FieldEmbeddingData.ofEmbedding_hom (x : F) :
    (FieldEmbeddingData.ofEmbedding h).hom x = h RVSort.K ⟨x.1, x.2⟩ := rfl

end OfEmbedding


end Bridge


/-! ### The `RV`-part of a substructure, and why the inverse matters

A substructure `S` of a model has `S K` a subring of the field sort, `S RV` a submonoid of the
leading-term sort closed under inversion and residue addition and containing `rv (S K)`, and
`S Γ` a subgroup containing `val (S RV)`.

The inverse makes the first real step of Rideau-Kikuchi's argument free. The leading terms of the
*fraction field* of `S K` are **already** in `S RV`, because `rv (y / z) = rv y · (rv z)⁻¹`. So
passing from the ring part to its fraction field adds nothing at all to the leading-term part
(`rvMap_mem_RV_of_mem_subfieldClosure`), and extending an embedding across it is a question about
the field sort alone (`fracEmbedding`). Without the inverse this step would create new leading
terms, with no way to say where they should go. -/

section SubstructureRV

variable (S : rvLang.Substructure M)

/-- The field-sort part of a substructure, as a subring. -/
def subringOfSubstructure : Subring (M RVSort.K) where
  carrier := S RVSort.K
  zero_mem' := S.fun_mem RVFunc.zeroK _ (fun _ i => nomatch i)
  one_mem' := S.fun_mem RVFunc.oneK _ (fun _ i => nomatch i)
  neg_mem' := fun {x} hx => S.fun_mem RVFunc.negK x (fun _ i => by cases i; exact hx)
  add_mem' := fun {x y} hx hy =>
    S.fun_mem RVFunc.addK (x, y) (fun _ i => by
      cases i with
      | left i' => cases i'; exact hx
      | right i' => cases i'; exact hy)
  mul_mem' := fun {x y} hx hy =>
    S.fun_mem RVFunc.mulK (x, y) (fun _ i => by
      cases i with
      | left i' => cases i'; exact hx
      | right i' => cases i'; exact hy)

@[simp]
theorem mem_subringOfSubstructure {x : M RVSort.K} :
    x ∈ subringOfSubstructure S ↔ x ∈ S RVSort.K := Iff.rfl

variable {S}

omit [M ⊨ ACVFTheory] in
/-- A substructure is closed under `rv`. -/
theorem rvMap_mem_RV {x : M RVSort.K} (hx : x ∈ S RVSort.K) :
    rvMap x ∈ S RVSort.RV :=
  S.fun_mem RVFunc.rv x (fun _ i => by cases i; exact hx)

/-- A substructure's `RV`-part is closed under multiplication. -/
theorem mul_mem_RV {ξ η : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (hη : η ∈ S RVSort.RV) : ξ * η ∈ S RVSort.RV :=
  S.fun_mem RVFunc.mulRV (ξ, η) (fun _ i => by
    cases i with
    | left i' => cases i'; exact hξ
    | right i' => cases i'; exact hη)

/-- A substructure's `RV`-part is closed under inversion. -/
theorem inv_mem_RV {ξ : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV) :
    ξ⁻¹ ∈ S RVSort.RV :=
  S.fun_mem RVFunc.invRV ξ (fun _ i => by cases i; exact hξ)

omit [M ⊨ ACVFTheory] in
/-- A substructure is closed under `val`. -/
theorem valMap_mem_Gamma {ξ : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV) :
    valMap ξ ∈ S RVSort.Γ :=
  S.fun_mem RVFunc.val ξ (fun _ i => by cases i; exact hξ)

/-- **A subring whose leading terms are already in the `RV`-part generates a subfield with the
same property.** This is what the inverse on the `RV` sort buys: passing to fractions creates no
new leading terms, because `rv (y / z) = rv y · (rv z)⁻¹`. -/
theorem rvMap_mem_RV_of_mem_subfieldClosure {T : Subring (M RVSort.K)}
    (hT : ∀ x ∈ T, rvMap x ∈ S RVSort.RV) {x : M RVSort.K}
    (hx : x ∈ Subfield.closure (T : Set (M RVSort.K))) :
    rvMap x ∈ S RVSort.RV := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hx
  rw [Subring.closure_eq] at hy hz
  rw [div_eq_mul_inv, model_rv_mul, model_rv_inv]
  exact mul_mem_RV (hT _ hy) (inv_mem_RV (hT _ hz))


/-- A substructure's `RV`-part contains `1`. -/
theorem one_mem_RV : (1 : M RVSort.RV) ∈ S RVSort.RV :=
  S.fun_mem RVFunc.oneRV _ (fun _ i => nomatch i)

/-- A substructure's `RV`-part contains `0`. -/
theorem zero_mem_RV : (0 : M RVSort.RV) ∈ S RVSort.RV :=
  S.fun_mem RVFunc.zeroRV _ (fun _ i => nomatch i)

/-- A substructure's `RV`-part is closed under the `RV`-sort's negation. -/
theorem neg_mem_RV {ξ : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV) :
    -ξ ∈ S RVSort.RV :=
  S.fun_mem RVFunc.negRV ξ (fun _ i => by cases i; exact hξ)

/-- A substructure's `Γ`-part contains `0`. -/
theorem zero_mem_Gamma : (0 : M RVSort.Γ) ∈ S RVSort.Γ :=
  S.fun_mem RVFunc.zeroΓ _ (fun _ i => nomatch i)

/-- A substructure's `RV`-part is closed under the leading terms of powers. The `RV` sort of a
model carries no `Monoid` instance — its addition is not associative, so the theory puts no
algebraic structure on it — so the power is taken in the field sort. -/
theorem rvMap_pow_mem_RV {x : M RVSort.K} (hx : rvMap x ∈ S RVSort.RV) (i : ℕ) :
    rvMap (x ^ i) ∈ S RVSort.RV := by
  induction i with
  | zero => rw [pow_zero, model_rv_one]; exact one_mem_RV
  | succ i ih => rw [pow_succ, model_rv_mul]; exact mul_mem_RV ih hx

/-- A substructure's `RV`-part is closed under the residue addition. -/
theorem add_mem_RV {ξ η : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (hη : η ∈ S RVSort.RV) : ξ + η ∈ S RVSort.RV :=
  S.fun_mem RVFunc.addRV (ξ, η) (fun _ i => by
    cases i with
    | left i' => cases i'; exact hξ
    | right i' => cases i'; exact hη)


variable (S)

/-- **Growing the field sort without new leading terms.** If a subring `T` of the field sort
contains the field part of `S` and every element of it already has its leading term in the
`RV`-part of `S`, then `T` together with the `RV`- and `Γ`-parts of `S` is again a substructure.
So such an enlargement is a question about the field sort alone. -/
noncomputable def adjoinSubstructure (T : Subring (M RVSort.K))
    (_hTS : ∀ x ∈ S RVSort.K, x ∈ T)
    (hT : ∀ x ∈ T, rvMap x ∈ S RVSort.RV) : rvLang.Substructure M where
  carrier
    | RVSort.K => (T : Set (M RVSort.K))
    | RVSort.RV => S RVSort.RV
    | RVSort.Γ => S RVSort.Γ
  fun_mem := by
    intro σ t f x hx
    match t, σ, f with
    | _, _, .zeroK => exact T.zero_mem
    | _, _, .oneK => exact T.one_mem
    | _, _, .negK => exact T.neg_mem (hx RVSort.K Idx.var)
    | _, _, .addK =>
      exact T.add_mem (hx RVSort.K (Idx.left Idx.var))
        (hx RVSort.K (Idx.right Idx.var))
    | _, _, .mulK =>
      exact T.mul_mem (hx RVSort.K (Idx.left Idx.var))
        (hx RVSort.K (Idx.right Idx.var))
    | _, _, .zeroRV => exact S.fun_mem RVFunc.zeroRV _ (fun _ i => nomatch i)
    | _, _, .oneRV => exact one_mem_RV
    | _, _, .negRV =>
      exact S.fun_mem RVFunc.negRV _ (fun _ i => by
        cases i; exact hx RVSort.RV Idx.var)
    | _, _, .addRV =>
      exact add_mem_RV (hx RVSort.RV (Idx.left Idx.var))
        (hx RVSort.RV (Idx.right Idx.var))
    | _, _, .mulRV =>
      exact mul_mem_RV (hx RVSort.RV (Idx.left Idx.var))
        (hx RVSort.RV (Idx.right Idx.var))
    | _, _, .invRV => exact inv_mem_RV (hx RVSort.RV Idx.var)
    | _, _, .zeroΓ => exact S.fun_mem RVFunc.zeroΓ _ (fun _ i => nomatch i)
    | _, _, .inftyΓ => exact S.fun_mem RVFunc.inftyΓ _ (fun _ i => nomatch i)
    | _, _, .negΓ =>
      exact S.fun_mem RVFunc.negΓ _ (fun _ i => by
        cases i; exact hx RVSort.Γ Idx.var)
    | _, _, .addΓ =>
      exact S.fun_mem RVFunc.addΓ _ (fun _ i => by
        cases i with
        | left i' => cases i'; exact hx RVSort.Γ (Idx.left Idx.var)
        | right i' => cases i'; exact hx RVSort.Γ (Idx.right Idx.var))
    | _, _, .rv => exact hT _ (hx RVSort.K Idx.var)
    | _, _, .val => exact valMap_mem_Gamma (hx RVSort.RV Idx.var)

end SubstructureRV


/-! ### Transporting a ring homomorphism along an injective one -/

/-- A ring homomorphism `g : A →+* C`, transported along an injective `ι : A →+* B`, as a
homomorphism defined on the range of `ι`. -/
noncomputable def rangeLift {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    {ι : A →+* B} (hι : Function.Injective ι) (g : A →+* C) : ι.range →+* C where
  toFun x := g (Classical.choose (RingHom.mem_range.mp x.2))
  map_one' := by
    have h : Classical.choose (RingHom.mem_range.mp (1 : ι.range).2) = 1 := by
      refine hι ?_
      rw [Classical.choose_spec (RingHom.mem_range.mp (1 : ι.range).2), map_one]
      rfl
    change g _ = 1
    rw [h, map_one]
  map_zero' := by
    have h : Classical.choose (RingHom.mem_range.mp (0 : ι.range).2) = 0 := by
      refine hι ?_
      rw [Classical.choose_spec (RingHom.mem_range.mp (0 : ι.range).2), map_zero]
      rfl
    change g _ = 0
    rw [h, map_zero]
  map_add' x y := by
    change g _ = g _ + g _
    rw [← map_add g]
    refine congrArg g (hι ?_)
    rw [Classical.choose_spec (RingHom.mem_range.mp (x + y).2), map_add,
      Classical.choose_spec (RingHom.mem_range.mp x.2),
      Classical.choose_spec (RingHom.mem_range.mp y.2)]
    rfl
  map_mul' x y := by
    change g _ = g _ * g _
    rw [← map_mul g]
    refine congrArg g (hι ?_)
    rw [Classical.choose_spec (RingHom.mem_range.mp (x * y).2), map_mul,
      Classical.choose_spec (RingHom.mem_range.mp x.2),
      Classical.choose_spec (RingHom.mem_range.mp y.2)]
    rfl

theorem rangeLift_eq {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    {ι : A →+* B} (hι : Function.Injective ι) (g : A →+* C) {x : ι.range} {a : A}
    (h : ι a = x.1) : rangeLift hι g x = g a := by
  refine congrArg g (hι ?_)
  rw [Classical.choose_spec (RingHom.mem_range.mp x.2), h]

theorem rangeLift_injective {A B C : Type*} [CommRing A] [CommRing B] [Field C]
    {ι : A →+* B} (hι : Function.Injective ι) (g : A →+* C) (hg : Function.Injective g) :
    Function.Injective (rangeLift hι g) := by
  intro x y h
  have hx := Classical.choose_spec (RingHom.mem_range.mp x.2)
  have hy := Classical.choose_spec (RingHom.mem_range.mp y.2)
  exact Subtype.ext (by rw [← hx, ← hy, hg h])

/-! ### Extending an embedding along a field-sort enlargement

Since an `adjoinSubstructure` differs from `S` only in the field sort, an embedding of it is an
embedding of `S` together with a ring homomorphism of the adjoined subring, compatible with `rv`.
Nothing about the `RV`- or `Γ`-sorts has to be said again. -/

section AdjoinEmbedding

variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]
variable (S : rvLang.Substructure M) {T : Subring (M RVSort.K)}
variable (hTS : ∀ x ∈ S RVSort.K, x ∈ T)
variable (hT : ∀ x ∈ T, rvMap x ∈ S RVSort.RV)

/-- **An embedding of `S` plus a ring homomorphism of the adjoined subring gives an embedding of
the enlargement.** -/
noncomputable def adjoinEmbedding (e : (fun s => ↥(S s)) ↪[rvLang] N) (φ : T →+* N RVSort.K)
    (hφinj : Function.Injective φ)
    (hφrv : ∀ x : T, e RVSort.RV ⟨rvMap (x : M RVSort.K), hT _ x.2⟩ = rvMap (φ x)) :
    (fun s => ↥(adjoinSubstructure S T hTS hT s)) ↪[rvLang] N where
  toEmbedding
    | RVSort.K => ⟨fun m => φ ⟨m.1, m.2⟩,
        fun _ _ h => Subtype.ext (congrArg Subtype.val (hφinj h))⟩
    | RVSort.RV => ⟨fun m => e RVSort.RV ⟨m.1, m.2⟩,
        fun _ _ h => Subtype.ext (congrArg Subtype.val (e.injective _ h))⟩
    | RVSort.Γ => ⟨fun m => e RVSort.Γ ⟨m.1, m.2⟩,
        fun _ _ h => Subtype.ext (congrArg Subtype.val (e.injective _ h))⟩
  map_fun' := by
    intro σ t f x
    match t, σ, f with
    | _, _, .zeroK => exact map_zero φ
    | _, _, .oneK => exact map_one φ
    | _, _, .negK => exact map_neg φ _
    | _, _, .addK => exact map_add φ _ _
    | _, _, .mulK => exact map_mul φ _ _
    | _, _, .zeroRV => exact e.map_fun' RVFunc.zeroRV default
    | _, _, .oneRV => exact e.map_fun' RVFunc.oneRV default
    | _, _, .negRV => exact e.map_fun' RVFunc.negRV _
    | _, _, .addRV => exact e.map_fun' RVFunc.addRV _
    | _, _, .mulRV => exact e.map_fun' RVFunc.mulRV _
    | _, _, .invRV => exact e.map_fun' RVFunc.invRV _
    | _, _, .zeroΓ => exact e.map_fun' RVFunc.zeroΓ default
    | _, _, .inftyΓ => exact e.map_fun' RVFunc.inftyΓ default
    | _, _, .negΓ => exact e.map_fun' RVFunc.negΓ _
    | _, _, .addΓ => exact e.map_fun' RVFunc.addΓ _
    | _, _, .rv =>
      exact hφrv ⟨(x.get RVSort.K Idx.var).1,
        (x.get RVSort.K Idx.var).2⟩
    | _, _, .val => exact e.map_fun' RVFunc.val _
  map_rel' := by
    intro σ r x
    match σ, r with
    | _, .leΓ => exact e.map_rel' RVRel.leΓ _

@[simp]
theorem adjoinEmbedding_apply_K (e : (fun s => ↥(S s)) ↪[rvLang] N) (φ : T →+* N RVSort.K)
    (hφinj) (hφrv) (m : ↥(adjoinSubstructure S T hTS hT RVSort.K)) :
    adjoinEmbedding S hTS hT e φ hφinj hφrv RVSort.K m = φ ⟨m.1, m.2⟩ := rfl

@[simp]
theorem adjoinEmbedding_apply_RV (e : (fun s => ↥(S s)) ↪[rvLang] N) (φ : T →+* N RVSort.K)
    (hφinj) (hφrv) (m : ↥(adjoinSubstructure S T hTS hT RVSort.RV)) :
    adjoinEmbedding S hTS hT e φ hφinj hφrv RVSort.RV m = e RVSort.RV ⟨m.1, m.2⟩ := rfl

@[simp]
theorem adjoinEmbedding_apply_Gamma (e : (fun s => ↥(S s)) ↪[rvLang] N) (φ : T →+* N RVSort.K)
    (hφinj) (hφrv) (m : ↥(adjoinSubstructure S T hTS hT RVSort.Γ)) :
    adjoinEmbedding S hTS hT e φ hφinj hφrv RVSort.Γ m = e RVSort.Γ ⟨m.1, m.2⟩ := rfl

end AdjoinEmbedding




/-! ### The fraction-field step, at the level of embeddings

Putting the pieces together: an embedding of `S` extends to an embedding of the substructure
whose field part is the subfield generated by `S K`, with the `RV`- and `Γ`-parts unchanged. -/

section FracEmbedding

variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]
variable (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N)

/-- The ring homomorphism on the field sort carried by an embedding of a substructure. -/
def subHom : subringOfSubstructure S →+* N RVSort.K where
  toFun x := e RVSort.K ⟨x.1, x.2⟩
  map_one' := e.map_fun' RVFunc.oneK default
  map_zero' := e.map_fun' RVFunc.zeroK default
  map_add' x y := e.map_fun' RVFunc.addK
    ((⟨x.1, x.2⟩, ⟨y.1, y.2⟩) : (fun s => ↥(S s)) [^] (⦃RVSort.K⦄ ⨯ ⦃RVSort.K⦄))
  map_mul' x y := e.map_fun' RVFunc.mulK
    ((⟨x.1, x.2⟩, ⟨y.1, y.2⟩) : (fun s => ↥(S s)) [^] (⦃RVSort.K⦄ ⨯ ⦃RVSort.K⦄))

@[simp]
theorem subHom_apply (x : subringOfSubstructure S) :
    subHom S e x = e RVSort.K ⟨x.1, x.2⟩ := rfl

theorem subHom_injective : Function.Injective (subHom S e) := fun _ _ h =>
  Subtype.ext (congrArg Subtype.val (e.injective RVSort.K h))


/-- The subfield generated by the ring part, presented as the range of the canonical map from
the fraction field of that ring. -/
noncomputable def fracIncl : FractionRing (subringOfSubstructure S) →+* M RVSort.K :=
  IsFractionRing.lift (g := (subringOfSubstructure S).subtype) Subtype.val_injective

theorem fracIncl_injective : Function.Injective (fracIncl S) := (fracIncl S).injective

@[simp]
theorem fracIncl_algebraMap (x : subringOfSubstructure S) :
    fracIncl S (algebraMap _ _ x) = (x : M RVSort.K) :=
  IsFractionRing.lift_algebraMap _ _

theorem mem_fracIncl_range_iff {x : M RVSort.K} :
    x ∈ (fracIncl S).range ↔
      ∃ y ∈ S RVSort.K, ∃ z ∈ S RVSort.K, y / z = x := by
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨y, z, -, rfl⟩ := IsFractionRing.div_surjective (A := subringOfSubstructure S) t
    exact ⟨y.1, y.2, z.1, z.2, by rw [map_div₀, fracIncl_algebraMap, fracIncl_algebraMap]⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    refine ⟨algebraMap (subringOfSubstructure S) _ ⟨y, hy⟩
      / algebraMap (subringOfSubstructure S) _ ⟨z, hz⟩, ?_⟩
    rw [map_div₀, fracIncl_algebraMap, fracIncl_algebraMap]

theorem subset_fracIncl_range : ∀ x ∈ S RVSort.K, x ∈ (fracIncl S).range := by
  intro x hx
  exact mem_fracIncl_range_iff S |>.mpr ⟨x, hx, 1, (subringOfSubstructure S).one_mem, div_one x⟩

theorem rvMap_mem_RV_of_mem_fracIncl_range :
    ∀ x ∈ (fracIncl S).range, rvMap x ∈ S RVSort.RV := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := (mem_fracIncl_range_iff S).mp hx
  rw [div_eq_mul_inv, model_rv_mul, model_rv_inv]
  exact mul_mem_RV (rvMap_mem_RV hy) (inv_mem_RV (rvMap_mem_RV hz))

/-- **The fraction-field enlargement of a substructure**, as a substructure: the field part is
the subfield generated by `S K`, and the `RV`- and `Γ`-parts are unchanged. -/
noncomputable def fracAdjoin : rvLang.Substructure M :=
  adjoinSubstructure S (fracIncl S).range (subset_fracIncl_range S)
    (rvMap_mem_RV_of_mem_fracIncl_range S)

/-- The embedding commutes with `rv` on the field part. -/
theorem e_rvMap {x : M RVSort.K} (hx : x ∈ S RVSort.K)
    (h : rvMap x ∈ S RVSort.RV) :
    e RVSort.RV ⟨rvMap x, h⟩ = rvMap (subHom S e ⟨x, hx⟩) :=
  e.map_fun' RVFunc.rv (⟨x, hx⟩ : ↥(S RVSort.K))

/-- The embedding is multiplicative on the `RV` part. -/
theorem e_mulRV {ξ η : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (hη : η ∈ S RVSort.RV) (h : ξ * η ∈ S RVSort.RV) :
    e RVSort.RV ⟨ξ * η, h⟩ = e RVSort.RV ⟨ξ, hξ⟩ * e RVSort.RV ⟨η, hη⟩ :=
  e.map_fun' RVFunc.mulRV
    ((⟨ξ, hξ⟩, ⟨η, hη⟩) : (fun s => ↥(S s)) [^] (⦃RVSort.RV⦄ ⨯ ⦃RVSort.RV⦄))

/-- The embedding commutes with inversion on the `RV` part. -/
theorem e_invRV {ξ : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (h : ξ⁻¹ ∈ S RVSort.RV) :
    e RVSort.RV ⟨ξ⁻¹, h⟩ = (e RVSort.RV ⟨ξ, hξ⟩)⁻¹ :=
  e.map_fun' RVFunc.invRV (⟨ξ, hξ⟩ : ↥(S RVSort.RV))


/-- The ring homomorphism of the fraction-field enlargement, obtained by lifting `subHom` to the
fraction field and transporting it along `fracIncl`. -/
noncomputable def fracHom : (fracIncl S).range →+* N RVSort.K :=
  rangeLift (fracIncl_injective S) (IsFractionRing.lift (subHom_injective S e))

theorem fracHom_div {y z : M RVSort.K} (hy : y ∈ S RVSort.K)
    (hz : z ∈ S RVSort.K) {x : (fracIncl S).range} (h : y / z = x.1) :
    fracHom S e x = subHom S e ⟨y, hy⟩ / subHom S e ⟨z, hz⟩ := by
  rw [fracHom, rangeLift_eq _ _
    (a := algebraMap (subringOfSubstructure S) _ ⟨y, hy⟩
      / algebraMap (subringOfSubstructure S) _ ⟨z, hz⟩)
    (by rw [map_div₀, fracIncl_algebraMap, fracIncl_algebraMap]; exact h),
    map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]

theorem fracHom_injective : Function.Injective (fracHom S e) :=
  let g : FractionRing (subringOfSubstructure S) →+* N RVSort.K :=
    IsFractionRing.lift (subHom_injective S e)
  rangeLift_injective (fracIncl_injective S) g g.injective

theorem fracHom_rv (x : (fracIncl S).range) :
    e RVSort.RV ⟨rvMap (x : M RVSort.K),
        rvMap_mem_RV_of_mem_fracIncl_range S _ x.2⟩ = rvMap (fracHom S e x) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, z, hz, rfl⟩ := (mem_fracIncl_range_iff S).mp hx
  rw [fracHom_div S e hy hz rfl]
  have h1 : rvMap y ∈ S RVSort.RV := rvMap_mem_RV hy
  have h2 : rvMap z ∈ S RVSort.RV := rvMap_mem_RV hz
  have h3 : (rvMap z)⁻¹ ∈ S RVSort.RV := inv_mem_RV h2
  have h4 : rvMap y * (rvMap z)⁻¹ ∈ S RVSort.RV := mul_mem_RV h1 h3
  have hcongr : e RVSort.RV ⟨rvMap (y / z),
      rvMap_mem_RV_of_mem_fracIncl_range S _ hx⟩
      = e RVSort.RV ⟨rvMap y * (rvMap z)⁻¹, h4⟩ :=
    congrArg _ (Subtype.ext (show rvMap (y / z) = rvMap y * (rvMap z)⁻¹ by
      rw [div_eq_mul_inv, model_rv_mul, model_rv_inv]))
  rw [hcongr, e_mulRV S e h1 h3, e_invRV S e h2, e_rvMap S e hy h1, e_rvMap S e hz h2,
    ← model_rv_inv, ← model_rv_mul, div_eq_mul_inv]

/-- **The fraction-field step, at the level of embeddings.** An embedding of `S` extends to an
embedding of the substructure whose field part is the subfield generated by `S K`, with the
`RV`- and `Γ`-parts unchanged. This is the reduction to "`K(A)` is a field" in Rideau-Kikuchi's
notes, and with the inverse on the `RV` sort it is an extension of the field sort alone. -/
noncomputable def fracEmbedding : (fun s => ↥(fracAdjoin S s)) ↪[rvLang] N :=
  adjoinEmbedding S (subset_fracIncl_range S) (rvMap_mem_RV_of_mem_fracIncl_range S) e
    (fracHom S e) (fracHom_injective S e) (fracHom_rv S e)

/-- It really is an extension. -/
theorem fracEmbedding_apply_K {x : M RVSort.K} (hx : x ∈ S RVSort.K)
    (h : x ∈ (fracIncl S).range) :
    fracEmbedding S e RVSort.K ⟨x, h⟩ = e RVSort.K ⟨x, hx⟩ := by
  change fracHom S e ⟨x, h⟩ = _
  rw [fracHom_div S e hx (subringOfSubstructure S).one_mem (z := 1) (div_one x)]
  have h1 : subHom S e ⟨(1 : M RVSort.K), (subringOfSubstructure S).one_mem⟩ = 1 := map_one _
  rw [h1, div_one]
  rfl

end FracEmbedding

end ManySorted.Language
