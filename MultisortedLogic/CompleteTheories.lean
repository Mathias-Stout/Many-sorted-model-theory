/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, Mathias Stout
-/
module

public import MultisortedLogic.LowenheimSkolem

/-!
# Complete theories

## Main definitions

* `Theory.closure T`: the sentences that are consequences of `T`.
* `Theory.IsComplete T`: `T` is satisfiable, and every sentence or its negation is a consequence
  of `T`.
* `Theory.IsMaximal T`: `T` is satisfiable, and contains every sentence or its negation.
* `Theory.Categorical κ T`: any two models of `T` of size `κ` are isomorphic, the size of a
  structure `M` being the size of `Σ s, M s`. This is Mathlib's `Cardinal.Categorical`.

## Main results

* `Theory.IsComplete.models_elementarily_equivalent`: the models of a complete theory are
  elementarily equivalent; `Theory.isComplete_iff_models_elementarily_equivalent` is the converse.
* `completeTheory.isMaximal`: the complete theory of a structure with nonempty sorts is maximal.
* `Theory.Categorical.isComplete`: **the Łoś–Vaught test**. A satisfiable theory whose models all
  have an infinite sort, and that is categorical in an infinite cardinal at least the sizes of the
  sorts and of the symbols, is complete.

## Implementation notes

Where Mathlib quantifies over the models `Theory.ModelType T`, the statements here quantify over
the realizations `FormulaSet.Realization T`, which are the models of `T` in the universe of the
language (`Theory.realizationEquivModelType` in `Bundled.lean`).

## References

This file was originally based on `Mathlib/ModelTheory/Satisfiability.lean`, by Aaron Anderson.
-/

@[expose] public section

universe u v w w' z

namespace ManySorted.Language

open Arity Structure Cardinal

variable {S : Type z} {L : Language.{u, v} S}

namespace Theory

variable {T T' : L.Theory} {φ ψ : L.Sentence}

/-! ### Consequence for sentences -/

theorem models_sentence_iff :
    T ⊨ᵇ φ ↔ ∀ (M : S → Type (max z u v)) [L.Structure M] [∀ s, Nonempty (M s)] [M ⊨ T],
      M ⊨ φ :=
  ⟨fun h M _ _ _ => h M PUnit.unit, fun h M _ _ _ _ => h M⟩

theorem models_sentence_of_mem (h : φ ∈ T) : T ⊨ᵇ φ :=
  fun _ _ _ _ _ => realize_sentence_of_mem h

theorem models_iff_not_isSatisfiable : T ⊨ᵇ φ ↔ ¬(T ∪ {φ.not}).IsSatisfiable :=
  modelsFormula_iff_models.trans FormulaSet.models_iff_not_isSatisfiable

theorem isSatisfiable_iff_not_models_bot : T.IsSatisfiable ↔ ¬T ⊨ᵇ (⊥ : L.Sentence) :=
  ⟨fun ⟨r⟩ h => h r.carrier PUnit.unit,
    fun h => by_contra fun hT => h fun M _ _ _ _ => hT (Model.isSatisfiable M)⟩

/-- A consequence of a theory each of whose sentences is a consequence of `T` is a consequence of
`T`. -/
theorem models_of_models_theory {σ : Arity S} {φ : L.Formula σ} (h : ∀ ψ ∈ T', T ⊨ᵇ ψ)
    (hφ : T' ⊨ᵇ φ) : T ⊨ᵇ φ :=
  fun M _ _ _ xs => have : M ⊨ T' := ⟨fun ψ hψ => h ψ hψ M PUnit.unit⟩; hφ M xs

/-! ### The closure under consequence -/

variable (T) in
/-- The sentences that are consequences of `T`. -/
def closure : L.Theory :=
  {φ | T ⊨ᵇ φ}

@[simp]
theorem mem_closure_iff : φ ∈ T.closure ↔ T ⊨ᵇ φ :=
  Iff.rfl

theorem subset_closure : T ⊆ T.closure :=
  fun _ => models_sentence_of_mem

theorem top_mem_closure : (⊤ : L.Sentence) ∈ T.closure :=
  fun _ _ _ _ _ => Formula.realize_top.2 trivial

theorem bot_mem_closure_iff_not_isSatisfiable : (⊥ : L.Sentence) ∈ T.closure ↔ ¬T.IsSatisfiable :=
  by rw [mem_closure_iff, isSatisfiable_iff_not_models_bot, not_not]

theorem inf_mem_closure_iff : φ ⊓ ψ ∈ T.closure ↔ φ ∈ T.closure ∧ ψ ∈ T.closure :=
  ⟨fun h => ⟨fun M _ _ _ xs => (Formula.realize_inf.1 (h M xs)).1,
      fun M _ _ _ xs => (Formula.realize_inf.1 (h M xs)).2⟩,
    fun ⟨h₁, h₂⟩ M _ _ _ xs => Formula.realize_inf.2 ⟨h₁ M xs, h₂ M xs⟩⟩

theorem sup_mem_closure_of_left (h : φ ∈ T.closure) : φ ⊔ ψ ∈ T.closure :=
  fun M _ _ _ xs => Formula.realize_sup.2 (Or.inl (h M xs))

theorem sup_mem_closure_of_right (h : ψ ∈ T.closure) : φ ⊔ ψ ∈ T.closure :=
  fun M _ _ _ xs => Formula.realize_sup.2 (Or.inr (h M xs))

/-- The closure is closed under modus ponens. -/
theorem mem_closure_of_imp_mem_closure (hφ : φ ∈ T.closure) (h : (φ ⟹ ψ) ∈ T.closure) :
    ψ ∈ T.closure :=
  fun M _ _ _ xs => h M xs (hφ M xs)

theorem closure_mono (h : T ⊆ T') : T.closure ⊆ T'.closure :=
  fun _ hφ => hφ.mono h

@[simp]
theorem closure_closure : T.closure.closure = T.closure :=
  Set.Subset.antisymm (fun _ hφ => models_of_models_theory (fun _ hψ => hψ) hφ) subset_closure

/-! ### Complete theories -/

variable (T) in
/-- A theory is complete when it is satisfiable and every sentence or its negation is a
consequence of it. -/
def IsComplete : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, T ⊨ᵇ φ ∨ T ⊨ᵇ φ.not

namespace IsComplete

theorem models_not_iff (h : T.IsComplete) (φ : L.Sentence) : T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ := by
  obtain ⟨r⟩ := h.1
  exact ⟨fun hn hφ => hn r.carrier PUnit.unit (hφ r.carrier PUnit.unit),
    (h.2 φ).resolve_left⟩

theorem realize_sentence_iff (h : T.IsComplete) (φ : L.Sentence) (M : S → Type w)
    [L.Structure M] [∀ s, Nonempty (M s)] [M ⊨ T] : M ⊨ φ ↔ T ⊨ᵇ φ :=
  (h.2 φ).elim (fun hφ => iff_of_true (hφ.realize_sentence M) hφ)
    fun hφ => iff_of_false (hφ.realize_sentence M) ((h.models_not_iff φ).1 hφ)

/-- A complete theory is the complete theory of each of its models, up to consequence. -/
theorem eq_complete_theory (h : T.IsComplete) (M : S → Type w) [L.Structure M]
    [∀ s, Nonempty (M s)] [M ⊨ T] : T.closure = L.completeTheory M :=
  Set.ext fun φ => (h.realize_sentence_iff φ M).symm

/-- The models of a complete theory are elementarily equivalent. -/
theorem models_elementarily_equivalent (h : T.IsComplete) (M : S → Type w) (N : S → Type w')
    [L.Structure M] [L.Structure N] [∀ s, Nonempty (M s)] [∀ s, Nonempty (N s)] [M ⊨ T]
    [N ⊨ T] : L.ElementarilyEquivalent M N :=
  (h.eq_complete_theory M).symm.trans (h.eq_complete_theory N)

end IsComplete

/-- A theory is complete exactly when it is satisfiable and its models are elementarily
equivalent. -/
theorem isComplete_iff_models_elementarily_equivalent :
    T.IsComplete ↔
      T.IsSatisfiable ∧
        ∀ r r' : FormulaSet.Realization T, L.ElementarilyEquivalent r.carrier r'.carrier := by
  refine ⟨fun h => ⟨h.1, fun r r' => h.models_elementarily_equivalent r.carrier r'.carrier⟩,
    fun ⟨hS, h⟩ => ⟨hS, fun φ => ?_⟩⟩
  obtain ⟨r⟩ := hS
  by_cases hφ : r.carrier ⊨ φ
  · exact Or.inl fun M _ _ _ _ =>
      ((h r ⟨M, PUnit.unit, fun _ hψ => realize_sentence_of_mem hψ⟩).realize_sentence φ).1 hφ
  · exact Or.inr fun M _ _ _ _ => fun hM =>
      hφ (((h r ⟨M, PUnit.unit, fun _ hψ => realize_sentence_of_mem hψ⟩).realize_sentence φ).2 hM)

/-! ### Maximal theories -/

variable (T) in
/-- A theory is maximal when it is satisfiable and contains every sentence or its negation.
Maximal theories are complete. -/
def IsMaximal : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, φ ∈ T ∨ φ.not ∈ T

theorem IsMaximal.isComplete (h : T.IsMaximal) : T.IsComplete :=
  h.imp_right (forall_imp fun _ => Or.imp models_sentence_of_mem models_sentence_of_mem)

theorem IsMaximal.mem_or_not_mem (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ∨ φ.not ∈ T :=
  h.2 φ

theorem IsMaximal.mem_of_models (h : T.IsMaximal) (hφ : T ⊨ᵇ φ) : φ ∈ T := by
  refine (h.mem_or_not_mem φ).resolve_right fun hn => ?_
  rw [models_iff_not_isSatisfiable, Set.union_singleton, Set.insert_eq_of_mem hn] at hφ
  exact hφ h.1

theorem IsMaximal.mem_iff_models (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ↔ T ⊨ᵇ φ :=
  ⟨models_sentence_of_mem, h.mem_of_models⟩

end Theory

namespace completeTheory

variable (L) (M : S → Type w) [L.Structure M]

theorem isSatisfiable [∀ s, Nonempty (M s)] : (L.completeTheory M).IsSatisfiable :=
  Theory.Model.isSatisfiable' M

theorem mem_or_not_mem (φ : L.Sentence) :
    φ ∈ L.completeTheory M ∨ φ.not ∈ L.completeTheory M :=
  em (M ⊨ φ)

theorem isMaximal [∀ s, Nonempty (M s)] : (L.completeTheory M).IsMaximal :=
  ⟨isSatisfiable L M, mem_or_not_mem L M⟩

theorem isComplete [∀ s, Nonempty (M s)] : (L.completeTheory M).IsComplete :=
  (isMaximal L M).isComplete

end completeTheory

/-! ### Categoricity and the Łoś–Vaught test -/

namespace Theory

variable (κ : Cardinal.{w}) (T : L.Theory)

/-- A theory is `κ`-categorical when any two of its models of size `κ`, in the universe of `κ`, are
isomorphic. The size of a structure `M` is the size of `Σ s, M s`. -/
def Categorical : Prop :=
  ∀ (M N : S → Type w) [L.Structure M] [L.Structure N] [∀ s, Nonempty (M s)]
    [∀ s, Nonempty (N s)] [M ⊨ T] [N ⊨ T],
    #(Σ s, M s) = lift.{z} κ → #(Σ s, N s) = lift.{z} κ → Nonempty (M ≃[L] N)

variable {κ T}

/-- **The Łoś–Vaught test**: a satisfiable theory whose models all have an infinite sort, and that
is categorical in an infinite cardinal at least the sizes of the sorts and of the symbols, is
complete. -/
theorem Categorical.isComplete (h : Categorical κ T) (h1 : ℵ₀ ≤ κ)
    (h2 : lift.{w} (lift.{max u v} #S + L.card) ≤ lift.{max z u v} κ) (hS : T.IsSatisfiable)
    (hT : ∀ r : FormulaSet.Realization T, ∃ t, Infinite (r.carrier t)) : T.IsComplete := by
  refine ⟨hS, fun φ => or_iff_not_imp_left.2 fun hF => ?_⟩
  rw [models_iff_not_isSatisfiable, not_not] at hF
  rw [models_iff_not_isSatisfiable]
  rintro ⟨rT⟩
  obtain ⟨rF⟩ := hF
  -- `φ` fails in `rF` and holds in `rT`
  have hφF : rF.carrier ⊨ φ.not :=
    realize_sentence_of_mem (T := T ∪ {φ.not}) (Set.mem_union_right _ rfl)
  have hφT : rT.carrier ⊨ φ.not.not :=
    realize_sentence_of_mem (T := T ∪ {φ.not.not}) (Set.mem_union_right _ rfl)
  obtain ⟨tF, htF⟩ := hT (rF.restrict Set.subset_union_left)
  obtain ⟨tT, htT⟩ := hT (rT.restrict Set.subset_union_left)
  have : Infinite (rF.carrier tF) := htF
  have : Infinite (rT.carrier tT) := htT
  have : rF.carrier ⊨ T := rF.model.mono Set.subset_union_left
  have : rT.carrier ⊨ T := rT.model.mono Set.subset_union_left
  -- models of size `κ` elementarily equivalent to them are isomorphic
  obtain ⟨NF, _, _, hF, hκF⟩ := exists_elementarilyEquivalent_card_eq L rF.carrier (t := tF) κ h1 h2
  obtain ⟨NT, _, _, hT, hκT⟩ := exists_elementarilyEquivalent_card_eq L rT.carrier (t := tT) κ h1 h2
  have : NF ⊨ T := hF.theory_model
  have : NT ⊨ T := hT.theory_model
  obtain ⟨e⟩ := h NF NT hκF hκT
  exact hφT ((hT.realize_sentence _).2 ((e.realize_sentence _).1 ((hF.realize_sentence _).1 hφF)))

end Theory

end ManySorted.Language
