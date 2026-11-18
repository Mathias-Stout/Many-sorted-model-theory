/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Substructure.FieldLike
public import MultisortedLogic.Algebra.ACVF.Theory.Recovery
public import MultisortedLogic.EmbeddingTest

/-!
# Quantifier elimination for `ACVF` in `L_RV`: the reduction

This file carries out the model-theoretic half of the proof of

```lean
theorem ACVF_hasQERelTo_empty : ACVFTheory.HasQERelTo (∅ : Set RVSort)
```

(`Algebra/ACVF/QE.lean`), reducing it to a single statement about valued fields,
`FieldLikeExtension`.

The chain is:

* `Theory.hasQERelTo_of_exists_extension_substructure` (`EmbeddingTest.lean`) reduces to the
  case where the domain of the partial map is a *substructure*: the extension to a value of a
  term that has not yet been reached is forced and free, so that case never has to be argued
  about.
* `PartialMap.toEmbedding` turns the partial map into an `L_RV`-embedding, so the statement to
  prove is about maps commuting with the operations, not about formulas.
* `fieldSubstructure` and `Embedding.toPartialMap` turn an embedding of a *field-like*
  substructure — a subfield of the field sort together with its leading terms and their values —
  back into a partial quantifier-free map, and `PartialMap.restrict` cuts it down to the domain
  the test asks for.

`FieldLikeExtension` says: an embedding of a proper substructure extends to an embedding of a
field-like substructure containing a new element, after passing to an elementary extension of the
target. That is what the last three steps of the proof of Rideau-Kikuchi's Proposition 2.1.10,
the ACVF embedding lemma, provide: steps `res(K(C)) = k(C)` and `v(K(C)) = Γ(C)` replace the
`RV`- and `Γ`-parts of the domain by the leading terms and values of a subfield, and step
`K(C) = K(M)` adjoins a new element of the field sort.

Accordingly, `FieldLikeExtension` splits into `RVLift` (steps `res(K(C)) = k(C)` and
`v(K(C)) = Γ(C)`) and `FieldStep` (step `K(C) = K(M)`). `RVLift` is proved in the folder
`Algebra/ACVF/RVLift/` (`RVLift_holds`). `FieldStep` is proved in the folder
`Algebra/ACVF/FieldStep/`: it is reduced to `ValuePatternExt` (`fieldStep_of_valuePatternExt`),
which then holds (`valuePatternExt_holds`).

## Main definitions

* `Language.FieldLikeExtension` : the algebraic statement quantifier elimination is reduced to.
* `Language.RVLift`, `Language.FieldStep` : its two halves.

## Main statements

* `Language.ACVF_hasQERelTo_empty_of_fieldLikeExtension` : full quantifier elimination for `ACVF`
  in `L_RV`, given `FieldLikeExtension`.
* `Language.fieldLikeExtension_of_lift_step` : `FieldLikeExtension` from `RVLift` and `FieldStep`.
* `Language.ACVF_hasQERelTo_empty_of_lift_step` : the two combined.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

/-- **The algebraic extension property.** Given a model `M` of `ACVF`, a proper substructure `S` of
it and a partial quantifier-free map of `S` into another model `N`, there is a subfield `F` of the
field sort of `M` whose field-like substructure contains `S` and at least one element outside
`S`, and an `L_RV`-embedding of that field-like substructure into an elementary extension of `N`
extending the given map.

This is the content of the last three steps of the proof of Rideau-Kikuchi's Proposition 2.1.10:
steps `res(K(C)) = k(C)` and `v(K(C)) = Γ(C)` replace the `RV`- and `Γ`-parts of `S` by the
leading terms and the values of a subfield, and step `K(C) = K(M)` adjoins a new element of the
field sort. -/
def FieldLikeExtension : Prop :=
  ∀ (M N : RVSort → Type) [rvLang.Structure M] [rvLang.Structure N]
    [∀ s, Nonempty (M s)] [∀ s, Nonempty (N s)] [M ⊨ ACVFTheory] [N ⊨ ACVFTheory]
    (S : rvLang.Substructure M) (g : PartialMap (FormulaClass.qfRelTo rvLang ∅) ⇑S N),
    (∃ (s : RVSort) (x : M s), x ∉ S s) →
    ∃ (s : RVSort) (b : M s), b ∉ S s ∧
      ∃ (P : RVSort → Type) (_ : rvLang.Structure P) (_ : ∀ s, Nonempty (P s))
        (j : N ↪ₑ[rvLang] P) (F : Subfield (M RVSort.K)) (hsub : S ≤ fieldSubstructure M F),
        b ∈ fieldSubstructure M F s ∧
        ∃ h : (fun s => ↥(fieldSubstructure M F s)) ↪[rvLang] P,
          ∀ (s' : RVSort) (a : S s'), h s' (Substructure.inclusion hsub s' a) = j s' (g s' a)

/-! ### Decomposition of `FieldLikeExtension`

`FieldLikeExtension` splits along the steps of Rideau-Kikuchi's proof. `RVLift` is steps
`res(K(C)) = k(C)` and `v(K(C)) = Γ(C)`: the `RV`- and `Γ`-parts of a substructure are replaced by
the leading terms and the values of a subfield, by lifting residues and values to the field sort.
`FieldStep` is step `K(C) = K(M)`: a field-like substructure that is not everything is enlarged
by one element of the field sort, which is where Rideau-Kikuchi's three cases (ramified, residual
and immediate) live. -/

/-- **Steps `res(K(C)) = k(C)` and `v(K(C)) = Γ(C)`.** Every embedding of a substructure extends to
an embedding of a field-like substructure containing it. -/
def RVLift : Prop :=
  ∀ (M N : RVSort → Type) [rvLang.Structure M] [rvLang.Structure N]
    [∀ s, Nonempty (M s)] [∀ s, Nonempty (N s)] [M ⊨ ACVFTheory] [N ⊨ ACVFTheory]
    (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N),
    ∃ (P : RVSort → Type) (_ : rvLang.Structure P) (_ : ∀ s, Nonempty (P s))
      (j : N ↪ₑ[rvLang] P) (F : Subfield (M RVSort.K)) (hsub : S ≤ fieldSubstructure M F)
      (h : (fun s => ↥(fieldSubstructure M F s)) ↪[rvLang] P),
      ∀ (s' : RVSort) (a : S s'), h s' (Substructure.inclusion hsub s' a) = j s' (e s' a)

/-- **Step `K(C) = K(M)`.** An embedding of a field-like substructure whose subfield is not the
whole field sort extends to a strictly larger subfield. -/
def FieldStep : Prop :=
  ∀ (M N : RVSort → Type) [rvLang.Structure M] [rvLang.Structure N]
    [∀ s, Nonempty (M s)] [∀ s, Nonempty (N s)] [M ⊨ ACVFTheory] [N ⊨ ACVFTheory]
    (F : Subfield (M RVSort.K)) (h : (fun s => ↥(fieldSubstructure M F s)) ↪[rvLang] N),
    (∃ y : M RVSort.K, y ∉ F) →
    ∃ (P : RVSort → Type) (_ : rvLang.Structure P) (_ : ∀ s, Nonempty (P s))
      (j : N ↪ₑ[rvLang] P) (F' : Subfield (M RVSort.K)) (hFF' : F ≤ F') (x : M RVSort.K),
      x ∈ F' ∧ x ∉ F ∧
      ∃ h' : (fun s => ↥(fieldSubstructure M F' s)) ↪[rvLang] P,
        ∀ (s' : RVSort) (a : fieldSubstructure M F s'),
          h' s' (Substructure.inclusion (fieldSubstructure_mono hFF') s' a) = j s' (h s' a)

/-- **The decomposition.** `FieldLikeExtension` follows from `RVLift` and `FieldStep`. -/
theorem fieldLikeExtension_of_lift_step (hlift : RVLift) (hstep : FieldStep) :
    FieldLikeExtension := by
  intro M N _ _ _ _ _ _ S g hne
  obtain ⟨P₁, _, _, j₁, F, hsub, h₁, comm₁⟩ := hlift M N S g.toEmbedding
  by_cases hA : ∃ (s : RVSort) (b : M s), b ∈ fieldSubstructure M F s ∧ b ∉ S s
  · obtain ⟨s, b, hbF, hbS⟩ := hA
    exact ⟨s, b, hbS, P₁, inferInstance, inferInstance, j₁, F, hsub, hbF, h₁, comm₁⟩
  · -- the field-like closure adds nothing, so `S` is already field-like
    push Not at hA
    -- a field element outside `F`, extracted from the missing element of `S`
    obtain ⟨s, x, hx⟩ := hne
    have hyF : ∃ y : M RVSort.K, y ∉ F := by
      have hxF : x ∉ fieldSubstructure M F s := fun hc => hx (hA s x hc)
      match s with
      | RVSort.K => exact ⟨x, hxF⟩
      | RVSort.RV =>
        obtain ⟨y, hy⟩ := model_rv_surjective (M := M) x
        exact ⟨y, fun hc => hxF ⟨y, hc, hy⟩⟩
      | RVSort.Γ =>
        obtain ⟨y, hy⟩ := valrv_surjective (M := M) x
        exact ⟨y, fun hc => hxF ⟨y, hc, hy⟩⟩
    have : P₁ ⊨ ACVFTheory := j₁.theory_model
    obtain ⟨P₂, _, _, j₂, F', hFF', b, hbF', hbF, h₂, comm₂⟩ := hstep M P₁ F h₁ hyF
    refine ⟨RVSort.K, b, fun hc => hbF (hsub RVSort.K hc), P₂, inferInstance, inferInstance,
      j₂.comp j₁, F', hsub.trans (fieldSubstructure_mono hFF'), hbF', h₂, fun s' a => ?_⟩
    have hstep1 := comm₂ s' (Substructure.inclusion hsub s' a)
    rw [comm₁ s' a] at hstep1
    exact hstep1

/-- **Quantifier elimination for `ACVF` in the three-sorted leading-term language**, given the
algebraic extension property. Everything model-theoretic is discharged here. -/
theorem ACVF_hasQERelTo_empty_of_fieldLikeExtension (hFL : FieldLikeExtension) :
    ACVFTheory.HasQERelTo (∅ : Set RVSort) := by
  refine Theory.hasQERelTo_of_exists_extension_substructure ?_
  intro M N _ _ _ _ _ _ S g hne
  obtain ⟨s, b, hb, P, _, _, j, F, hsub, hbF, h, hcomm⟩ := hFL M N S g hne
  have hins : insertAt ⇑S s b ≤ ⇑(fieldSubstructure M F) := fun t x hx => by
    rw [mem_insertAt] at hx
    exact hx.elim (fun h => hsub t h) fun h => by cases h; exact hbF
  exact ⟨s, b, hb, P, inferInstance, inferInstance, j, h.toPartialMap.restrict hins,
    fun s' a => hcomm s' a⟩

/-- **Full quantifier elimination for `ACVF` in `L_RV`, from `RVLift` and `FieldStep`.**
Everything that is not about valued fields is discharged here. The two hypotheses are proved as
`RVLift_holds` and, through `fieldStep_of_valuePatternExt`, `valuePatternExt_holds`. -/
theorem ACVF_hasQERelTo_empty_of_lift_step (hlift : RVLift) (hstep : FieldStep) :
    ACVFTheory.HasQERelTo (∅ : Set RVSort) :=
  ACVF_hasQERelTo_empty_of_fieldLikeExtension (fieldLikeExtension_of_lift_step hlift hstep)

end ManySorted.Language
