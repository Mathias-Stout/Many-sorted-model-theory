/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout, Jonas van der Schaaf
-/
module

public import MultisortedLogic.Ultraproducts
public import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Satisfiability, compactness and consequence

A set `P` of formulas in a context `σ` is satisfiable when a tuple in some structure with nonempty
sorts realizes it. Satisfiability and consequence quantify over the realizations of `P`, which
bundle the structure and the tuple, as Mathlib's notions quantify over `Theory.ModelType`.

A theory is a set of formulas in the empty context: `L.Theory` is `L.FormulaSet ⦃⦄`. Everything
here applies to theories through dot notation. A realization of a theory `T` is a model of `T`
(`FormulaSet.Realization.model`), `T.IsSatisfiable` says that `T` has a model, and compactness for
theories is `isSatisfiable_iff_isFinitelySatisfiable` for `σ = ⦃⦄`.

## Main definitions

* `FormulaSet.Realization P`: a structure with nonempty sorts, in the universe of the language,
  with a tuple realizing `P`.
* `FormulaSet.IsSatisfiable P`: `P` has a realization.
* `FormulaSet.IsFinitelySatisfiable P`: every finite subset of `P` has a realization.
* `FormulaSet.Models P φ`: `φ` holds of the tuple of every realization of `P`.

## Main results

* `FormulaSet.isSatisfiable_iff_isFinitelySatisfiable`: the compactness theorem, through Łoś's
  theorem.
* `FormulaSet.models_iff_not_isSatisfiable` and `FormulaSet.models_iff_finset_models`: consequence
  as unsatisfiability, and compactness for consequence.
* `Theory.modelsFormula_iff_models_lift`: `T ⊨ᵇ φ` is consequence from the sentences of `T`,
  lifted to the context of `φ`. With it, `Theory.models_iff_finset_models` is compactness for
  `⊨ᵇ`.

## References

This file was originally based on `Mathlib/ModelTheory/Satisfiability.lean`, by Aaron Anderson.
-/

@[expose] public section

universe u v w z

namespace ManySorted.Language

open Arity Structure Filter

variable {S : Type z} {L : Language.{u, v} S} {σ : Arity S}

namespace FormulaSet

/-! ### Realizations and satisfiability -/

variable (P : L.FormulaSet σ)

/-- A realization of `P`: a structure with nonempty sorts, in the universe `max z u v` of the
language, with a tuple realizing `P`. A realization of a theory is a model of it. -/
structure Realization where
  /-- The carriers. -/
  carrier : S → Type (max z u v)
  /-- The structure on the carriers. -/
  [str : L.Structure carrier]
  /-- The sorts are nonempty. -/
  [nonempty : ∀ s, Nonempty (carrier s)]
  /-- The tuple. -/
  xs : carrier [^] σ
  /-- The tuple realizes `P`. -/
  realize : P.Realize xs

attribute [instance] Realization.str Realization.nonempty

/-- `P` is satisfiable: it has a realization. -/
def IsSatisfiable : Prop :=
  Nonempty P.Realization

/-- Every finite subset of `P` is satisfiable. -/
def IsFinitelySatisfiable : Prop :=
  ∀ P₀ : Finset (L.Formula σ), (P₀ : L.FormulaSet σ) ⊆ P → IsSatisfiable (P₀ : L.FormulaSet σ)

/-- `φ` is a consequence of `P`: it holds of the tuple of every realization of `P`. -/
def Models (φ : L.Formula σ) : Prop :=
  ∀ r : P.Realization, φ.Realize r.xs

variable {P} {Q : L.FormulaSet σ}

/-- A realization of `Q` as a realization of `P ⊆ Q`. -/
def Realization.restrict (h : P ⊆ Q) (r : Q.Realization) : P.Realization :=
  ⟨r.carrier, r.xs, r.realize.mono h⟩

theorem IsSatisfiable.mono (h : Q.IsSatisfiable) (hPQ : P ⊆ Q) : P.IsSatisfiable :=
  h.map (Realization.restrict hPQ)

theorem IsSatisfiable.isFinitelySatisfiable (h : P.IsSatisfiable) : P.IsFinitelySatisfiable :=
  fun _ hP₀ => h.mono hP₀

/-! ### Compactness -/

/-- **The compactness theorem**: a set of formulas is satisfiable if all its finite subsets are.
It is realized in an ultraproduct of realizations of its finite subsets. -/
theorem IsFinitelySatisfiable.isSatisfiable (h : P.IsFinitelySatisfiable) : P.IsSatisfiable := by
  classical
  let r (q : Finset P) : Realization (q.map (Function.Embedding.subtype _) : L.FormulaSet σ) :=
    (h _ fun _ hφ => by
      obtain ⟨⟨_, hφP⟩, -, rfl⟩ := Finset.mem_map.1 hφ
      exact hφP).some
  let U := Ultrafilter.of (atTop : Filter (Finset P))
  refine ⟨⟨Ultraproduct U fun q => (r q).carrier,
    Interpret.mkQuot (Ultraproduct.eventuallyEqSetoid U _) (Interpret.ofPi fun q => (r q).xs),
    fun φ hφ => ?_⟩⟩
  rw [Ultraproduct.realize_formula]
  refine Eventually.filter_mono (Ultrafilter.of_le _)
    (eventually_atTop.2 ⟨{⟨φ, hφ⟩}, fun q hq => ?_⟩)
  rw [Interpret.eval_ofPi]
  exact (r q).realize φ (Finset.mem_map_of_mem _ (Finset.singleton_subset_iff.1 hq))

/-- **The compactness theorem**. -/
theorem isSatisfiable_iff_isFinitelySatisfiable : P.IsSatisfiable ↔ P.IsFinitelySatisfiable :=
  ⟨IsSatisfiable.isFinitelySatisfiable, IsFinitelySatisfiable.isSatisfiable⟩

theorem exists_finset_not_isSatisfiable (h : ¬P.IsSatisfiable) :
    ∃ P₀ : Finset (L.Formula σ), ↑P₀ ⊆ P ∧ ¬IsSatisfiable (P₀ : L.FormulaSet σ) := by
  by_contra hne
  push Not at hne
  exact h (IsFinitelySatisfiable.isSatisfiable hne)

/-- Satisfiability of a directed union, by compactness. -/
theorem isSatisfiable_iUnion {ι : Type*} [Nonempty ι] {P : ι → L.FormulaSet σ}
    (hdir : Directed (· ⊆ ·) P) (h : ∀ i, (P i).IsSatisfiable) : IsSatisfiable (⋃ i, P i) :=
  IsFinitelySatisfiable.isSatisfiable fun P₀ hP₀ => by
    obtain ⟨i, hi⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion hP₀
    exact (h i).mono hi

/-! ### Consequence -/

variable {φ : L.Formula σ}

/-- A consequence of `P` holds of every tuple realizing `P`, in every structure with nonempty sorts
in the universe of the language. -/
theorem Models.realize (h : P.Models φ) {N : S → Type (max z u v)} [L.Structure N]
    [∀ s, Nonempty (N s)] {xs : N [^] σ} (hxs : P.Realize xs) : φ.Realize xs :=
  h ⟨N, xs, hxs⟩

theorem Models.mono (h : P.Models φ) (hPQ : P ⊆ Q) : Q.Models φ :=
  fun r => h (r.restrict hPQ)

theorem models_of_mem (hφ : φ ∈ P) : P.Models φ :=
  fun r => r.realize φ hφ

/-- `φ` is a consequence of `P` iff `P` together with `¬φ` is not satisfiable. -/
theorem models_iff_not_isSatisfiable : P.Models φ ↔ ¬IsSatisfiable (P ∪ {φ.not}) := by
  refine ⟨fun h ⟨r⟩ => r.realize φ.not (Or.inr rfl) (h (r.restrict Set.subset_union_left)),
    fun h r => by_contra fun hn => h ⟨⟨r.carrier, r.xs, fun ψ hψ => ?_⟩⟩⟩
  rcases hψ with hψ | rfl
  · exact r.realize ψ hψ
  · exact hn

/-- **Compactness for consequence**: a consequence of `P` is a consequence of a finite subset of
`P`. -/
theorem models_iff_finset_models :
    P.Models φ ↔ ∃ P₀ : Finset (L.Formula σ), ↑P₀ ⊆ P ∧ Models (P₀ : L.FormulaSet σ) φ := by
  classical
  refine ⟨fun h => ?_, fun ⟨P₀, hP₀, h⟩ => h.mono hP₀⟩
  obtain ⟨F, hF, hFu⟩ := exists_finset_not_isSatisfiable (models_iff_not_isSatisfiable.1 h)
  refine ⟨F.filter (· ∈ P), fun ψ hψ => (Finset.mem_filter.1 hψ).2,
    models_iff_not_isSatisfiable.2 fun hsat => hFu (hsat.mono fun ψ hψ => ?_)⟩
  rcases hF hψ with hψP | hψφ
  · exact Or.inl (Finset.mem_filter.2 ⟨hψ, hψP⟩)
  · exact Or.inr hψφ

/-! ### Theories -/

/-- A realization of a theory is a model of it. -/
instance Realization.model {T : L.Theory} (r : Realization T) : r.carrier ⊨ T :=
  ⟨fun φ hφ => r.realize φ hφ⟩

end FormulaSet

namespace Theory

variable {T : L.Theory}

/-- A model of `T` with nonempty sorts, in the universe of the language, shows that `T` is
satisfiable. -/
theorem Model.isSatisfiable (M : S → Type (max z u v)) [L.Structure M] [∀ s, Nonempty (M s)]
    [M ⊨ T] : T.IsSatisfiable :=
  ⟨⟨M, PUnit.unit, fun _ hφ => realize_sentence_of_mem hφ⟩⟩

/-- A tuple in a model of `T` realizes the sentences of `T`, lifted to its context. -/
theorem realize_lift_image {M : S → Type w} [L.Structure M] [M ⊨ T] (xs : M [^] σ) :
    FormulaSet.Realize (Sentence.lift '' T) xs := by
  rintro _ ⟨θ, hθ, rfl⟩
  exact (Sentence.realize_lift θ xs).2 (realize_sentence_of_mem hθ)

/-- A structure with a tuple realizing the sentences of `T` is a model of `T`. -/
theorem model_of_realize_lift_image {M : S → Type w} [L.Structure M] {xs : M [^] σ}
    (h : FormulaSet.Realize (Sentence.lift '' T) xs) : M ⊨ T :=
  ⟨fun θ hθ => (Sentence.realize_lift θ xs).1 (h _ ⟨θ, hθ, rfl⟩)⟩

theorem ModelsFormula.mono {T₀ : L.Theory} {φ : L.Formula σ} (h : T₀ ⊨ᵇ φ) (hT : T₀ ⊆ T) :
    T ⊨ᵇ φ :=
  fun N _ _ hN xs => have := hN.mono hT; h N xs

/-- `T ⊨ᵇ φ` is consequence from the sentences of `T`, lifted to the context of `φ`. -/
theorem modelsFormula_iff_models_lift {φ : L.Formula σ} :
    T ⊨ᵇ φ ↔ FormulaSet.Models (Sentence.lift '' T) φ :=
  ⟨fun h r => have := model_of_realize_lift_image r.realize; h r.carrier r.xs,
    fun h _ _ _ _ xs => h.realize (realize_lift_image xs)⟩

/-- For a sentence, `T ⊨ᵇ φ` is consequence from `T` as a set of formulas in the empty context. -/
theorem modelsFormula_iff_models {φ : L.Sentence} : T ⊨ᵇ φ ↔ T.Models φ :=
  ⟨fun h r => h r.carrier r.xs,
    fun h _ _ _ _ _ => h.realize fun _ hψ => realize_sentence_of_mem hψ⟩

/-- **Compactness for `⊨ᵇ`**: a consequence of `T` is a consequence of a finite subset of `T`. -/
theorem models_iff_finset_models {φ : L.Formula σ} :
    T ⊨ᵇ φ ↔ ∃ T₀ : Finset L.Sentence, ↑T₀ ⊆ T ∧ (T₀ : L.Theory) ⊨ᵇ φ := by
  classical
  refine ⟨fun h => ?_, fun ⟨T₀, hT₀, h⟩ => h.mono hT₀⟩
  obtain ⟨P₀, hP₀, h₀⟩ :=
    FormulaSet.models_iff_finset_models.1 (modelsFormula_iff_models_lift.1 h)
  obtain ⟨T₀, hT₀, rfl⟩ := Finset.subset_set_image_iff.1 hP₀
  refine ⟨T₀, hT₀, modelsFormula_iff_models_lift.2 ?_⟩
  rwa [Finset.coe_image] at h₀

end Theory

end ManySorted.Language
