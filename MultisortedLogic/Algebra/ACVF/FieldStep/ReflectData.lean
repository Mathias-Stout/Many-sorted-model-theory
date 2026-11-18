/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Substructure.AdjoinElement

/-!
# `FieldStep` — step `K(C) = K(M)` of Rideau-Kikuchi's Proposition 2.1.10

An embedding of a field-like substructure whose subfield is not the whole field sort extends to a
strictly larger subfield, after passing to an elementary extension of the target.

This file is the model-theoretic scaffolding: it reduces `FieldStep` to a purely algebraic statement
about one element, and the algebraic statement is the `ReflectData` of
`Algebra/ACVF/ValuedField/Extend.lean`, which `Algebra/ACVF/Substructure/AdjoinElement.lean` and
`Algebra/ACVF/ValuedField/ResidualReflect.lean` already establish in each of Rideau-Kikuchi's
three cases.

Two pieces of plumbing do the work.

* **Pushing embedding data along the target's extension** (`FieldEmbeddingData.comp`). `FieldStep`
  allows the target to grow, so the data of the embedding has to be read in the larger model
  before the algebra is applied. An embedding of models carries `rv` and `val` and reflects the
  order of `Γ`, so both reflection properties survive.
* **The reduction itself** (`exists_fieldStep_target`): given an `a` outside `F` and a `b` in the
  target with `ReflectData`, `exists_fieldEmbeddingData_adjoin` enlarges the subfield and
  `FieldEmbeddingData.toEmbedding` turns the result back into an `L_RV`-embedding.

## Main definitions

* `Language.embRingHom` : the ring homomorphism on the field sort carried by an embedding.
* `Language.FieldEmbeddingData.comp` : embedding data pushed along an embedding of the target.

## Main statements

* `Language.exists_fieldStep_target` : **the reduction of `FieldStep` to `ReflectData`.**
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]
variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]
variable {N' : RVSort → Type w} [rvLang.Structure N'] [N' ⊨ ACVFTheory]

/-! ### An embedding of models, read algebraically -/

section Comp

variable (k : N ↪[rvLang] N')

/-- The ring homomorphism on the field sort carried by an embedding of models. -/
def embRingHom : N RVSort.K →+* N' RVSort.K where
  toFun := k RVSort.K
  map_one' := k.map_fun' RVFunc.oneK default
  map_zero' := k.map_fun' RVFunc.zeroK default
  map_add' x y := k.map_fun' RVFunc.addK ((x, y) : N [^] (⦃RVSort.K⦄ ⨯ ⦃RVSort.K⦄))
  map_mul' x y := k.map_fun' RVFunc.mulK ((x, y) : N [^] (⦃RVSort.K⦄ ⨯ ⦃RVSort.K⦄))

@[simp]
theorem embRingHom_apply (x : N RVSort.K) : embRingHom k x = k RVSort.K x := rfl

omit [N ⊨ ACVFTheory] [N' ⊨ ACVFTheory] in
theorem emb_rvMap_model (x : N RVSort.K) : k RVSort.RV (rvMap x) = rvMap (k RVSort.K x) :=
  k.map_fun' RVFunc.rv x

omit [N ⊨ ACVFTheory] [N' ⊨ ACVFTheory] in
theorem emb_valMap_model (ξ : N RVSort.RV) : k RVSort.Γ (valMap ξ) = valMap (k RVSort.RV ξ) :=
  k.map_fun' RVFunc.val ξ

theorem emb_le_iff_model (γ δ : N RVSort.Γ) : k RVSort.Γ γ ≤ k RVSort.Γ δ ↔ γ ≤ δ :=
  k.map_rel' RVRel.leΓ ((γ, δ) : N [^] (⦃RVSort.Γ⦄ ⨯ ⦃RVSort.Γ⦄))

omit [N ⊨ ACVFTheory] [N' ⊨ ACVFTheory] in
/-- `val ∘ rv`, carried along. -/
theorem emb_valrv_model (x : N RVSort.K) :
    k RVSort.Γ (valMap (rvMap x)) = valMap (rvMap (k RVSort.K x)) := by
  rw [emb_valMap_model k, emb_rvMap_model k]

/-- **Embedding data pushed forward along an embedding of the target.** -/
noncomputable def FieldEmbeddingData.comp {F : Subfield (M RVSort.K)}
    (d : FieldEmbeddingData F N) : FieldEmbeddingData F N' where
  hom := (embRingHom k).comp d.hom
  rv_iff x y := by
    change rvMap (x : M RVSort.K) = rvMap (y : M RVSort.K)
      ↔ rvMap (k RVSort.K (d.hom x)) = rvMap (k RVSort.K (d.hom y))
    rw [← emb_rvMap_model k, ← emb_rvMap_model k, d.rv_iff x y]
    exact ⟨fun hc => congrArg _ hc, fun hc => k.injective RVSort.RV hc⟩
  val_iff x y := by
    change valMap (rvMap (x : M RVSort.K)) ≤ valMap (rvMap (y : M RVSort.K))
      ↔ valMap (rvMap (k RVSort.K (d.hom x))) ≤ valMap (rvMap (k RVSort.K (d.hom y)))
    rw [← emb_valrv_model k, ← emb_valrv_model k, emb_le_iff_model k]
    exact d.val_iff x y

@[simp]
theorem FieldEmbeddingData.comp_hom {F : Subfield (M RVSort.K)} (d : FieldEmbeddingData F N)
    (x : F) : (d.comp k).hom x = k RVSort.K (d.hom x) := rfl

/-- The pushed-forward data induces the composite embedding, which is what the compatibility
clause of `FieldStep` compares against. -/
theorem FieldEmbeddingData.comp_toEmbedding {F : Subfield (M RVSort.K)}
    (d : FieldEmbeddingData F N) (s : RVSort) (m : fieldSubstructure M F s) :
    (d.comp k).toEmbedding s m = k s (d.toEmbedding s m) := by
  match s with
  | RVSort.K => rfl
  | RVSort.RV =>
    obtain ⟨x, hx, hxm⟩ := m.2
    have hcast : m = ⟨rvMap x, ⟨x, hx, rfl⟩⟩ := Subtype.ext hxm.symm
    subst hcast
    change (d.comp k).rvComp _ = k RVSort.RV (d.rvComp _)
    rw [(d.comp k).rvComp_apply hx ⟨x, hx, rfl⟩, d.rvComp_apply hx ⟨x, hx, rfl⟩,
      FieldEmbeddingData.comp_hom, emb_rvMap_model k]
  | RVSort.Γ =>
    obtain ⟨x, hx, hxm⟩ := m.2
    have hcast : m = ⟨valMap (rvMap x), ⟨x, hx, rfl⟩⟩ := Subtype.ext hxm.symm
    subst hcast
    change (d.comp k).gammaComp _ = k RVSort.Γ (d.gammaComp _)
    rw [(d.comp k).gammaComp_apply hx ⟨x, hx, rfl⟩, d.gammaComp_apply hx ⟨x, hx, rfl⟩,
      FieldEmbeddingData.comp_hom, emb_valrv_model k]

end Comp

/-! ### The reduction of `FieldStep` -/

/-- **`FieldStep`, once the target is fixed.** Given a field-like embedding into `N'`, an element
`a` of the field sort outside `F`, and a `b` in `N'` with the same leading-term type over `F` —
in the form `ReflectData`, which is all the three cases have to establish — the subfield grows
across `a` and the embedding extends.

This is everything model-theoretic in step `K(C) = K(M)`. The rest of `FieldStep` is producing `a`,
the elementary extension and `b`, which `fieldStep_of_valuePatternExt` does. -/
theorem exists_fieldStep_target (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N')
    {a : M RVSort.K} {b : N' RVSort.K} (haF : a ∉ F)
    (href : ReflectData F.subtype d.hom (modelValSubring M) (modelValSubring N') a b) :
    ∃ (F' : Subfield (M RVSort.K)) (hFF' : F ≤ F') (x : M RVSort.K), x ∈ F' ∧ x ∉ F ∧
      ∃ h' : (fun s => ↥(fieldSubstructure M F' s)) ↪[rvLang] N',
        ∀ (s : RVSort) (m : fieldSubstructure M F s),
          h' s (Substructure.inclusion (fieldSubstructure_mono hFF') s m) = d.toEmbedding s m := by
  obtain ⟨F', hFF', haF', d', hext, -⟩ := exists_fieldEmbeddingData_adjoin F d href
  refine ⟨F', hFF', a, haF', haF, d'.toEmbedding, fun s m => ?_⟩
  match s with
  | RVSort.K => exact hext m.1 m.2
  | RVSort.RV =>
    obtain ⟨x, hx, hxm⟩ := m.2
    have hcast : m = ⟨rvMap x, ⟨x, hx, rfl⟩⟩ := Subtype.ext hxm.symm
    subst hcast
    change d'.rvComp ⟨rvMap x, ⟨x, hFF' hx, rfl⟩⟩ = d.rvComp ⟨rvMap x, ⟨x, hx, rfl⟩⟩
    rw [d'.rvComp_apply (hFF' hx) ⟨x, hFF' hx, rfl⟩, d.rvComp_apply hx ⟨x, hx, rfl⟩, hext x hx]
  | RVSort.Γ =>
    obtain ⟨x, hx, hxm⟩ := m.2
    have hcast : m = ⟨valMap (rvMap x), ⟨x, hx, rfl⟩⟩ := Subtype.ext hxm.symm
    subst hcast
    change d'.gammaComp ⟨valMap (rvMap x), ⟨x, hFF' hx, rfl⟩⟩
      = d.gammaComp ⟨valMap (rvMap x), ⟨x, hx, rfl⟩⟩
    rw [d'.gammaComp_apply (hFF' hx) ⟨x, hFF' hx, rfl⟩, d.gammaComp_apply hx ⟨x, hx, rfl⟩,
      hext x hx]

end ManySorted.Language
