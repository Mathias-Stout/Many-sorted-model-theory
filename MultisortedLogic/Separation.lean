/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.DeltaMaps
public import MultisortedLogic.QuantifierElimination
public import MultisortedLogic.Satisfiability

/-!
# Separation, and the tuple-extension criteria for quantifier elimination

Separation says when a formula is equivalent to a formula of a given fragment. Applied to the
formulas quantifier-free relative to a set of sorts, it gives the tuple-extension criteria for
quantifier elimination. Both quantify over the realizations of a set of formulas, which bundle a
structure with a tuple.

## Main definitions

* `FormulaSet.Equivalent P φ ψ`: `φ` and `ψ` agree on every realization of `P`.
* `Theory.Realization T σ`: a model of `T` with a tuple in context `σ`.

## Main results

* `FormulaSet.exists_equivalent_iff_forall_realization` (**separation**): `φ` is equivalent modulo
  `P` to a formula of a fragment `Δ` iff it passes from one realization of `P` to another whenever
  the `Δ`-type of the first is contained in that of the second.
* `Theory.exists_semanticallyEquivalent_iff_forall_realization`: separation modulo a theory.
* `Theory.hasQERelTo_of_pointed_extension`: the tuple-extension criterion. Its hypothesis asks for
  a counterpart next to some tuple with the same complete type.
* `Theory.hasQERelTo_of_tuple_extension`: the same, with the counterpart in an elementary extension.
-/

@[expose] public section

universe u v z

namespace ManySorted.Language

open Arity Structure FormulaClass

variable {S : Type z} {L : Language.{u, v} S} {σ : Arity S}

/-! ### Equivalence modulo a set of formulas -/

namespace FormulaSet

variable {Δ P : L.FormulaSet σ}

/-- `φ` and `ψ` are equivalent modulo `P`: they agree on the tuple of every realization of `P`. -/
def Equivalent (P : L.FormulaSet σ) (φ ψ : L.Formula σ) : Prop :=
  P.Models (φ.iff ψ)

theorem equivalent_iff {φ ψ : L.Formula σ} :
    P.Equivalent φ ψ ↔ ∀ r : P.Realization, (φ.Realize r.xs ↔ ψ.Realize r.xs) :=
  forall_congr' fun _ => Formula.realize_iff

theorem Equivalent.realize_iff {φ ψ : L.Formula σ} (h : P.Equivalent φ ψ) (r : P.Realization) :
    φ.Realize r.xs ↔ ψ.Realize r.xs :=
  equivalent_iff.1 h r

/-! ### Separation -/

/-- **Separation** modulo a set of formulas `P`. Let `Δ` be closed under finite conjunctions and
disjunctions. A formula `φ` is equivalent modulo `P` to a formula of `Δ` iff `φ` passes from the
tuple of a realization `r` of `P` to that of a realization `r'` whenever the `Δ`-type of the first
is contained in the `Δ`-type of the second. -/
theorem exists_equivalent_iff_forall_realization (hΔ : IsFragment Δ) (φ : L.Formula σ) :
    (∃ ψ ∈ Δ, P.Equivalent φ ψ) ↔ ∀ r r' : P.Realization,
      Formula.typeOf Δ r.xs ⊆ Formula.typeOf Δ r'.xs → φ.Realize r.xs → φ.Realize r'.xs := by
  classical
  refine ⟨fun ⟨ψ, hψΔ, hψ⟩ r r' hsub hφ => (hψ.realize_iff r').2
    (Formula.realize_of_typeOf_subset hsub hψΔ ((hψ.realize_iff r).1 hφ)), fun H => ?_⟩
  by_contra hne
  push Not at hne
  let A : L.FormulaSet σ := {ψ | ψ ∈ Δ ∧ P.Models (φ.imp ψ)}
  -- A realization of `P` and all of `A`, but not of `φ`.
  have h₁ : IsSatisfiable (P ∪ A ∪ {φ.not}) := by
    by_contra hunsat
    obtain ⟨F, hF, hFu⟩ := exists_finset_not_isSatisfiable hunsat
    let A₀ := F.filter (· ∈ A)
    apply hne (Formula.iInf A₀ id) (hΔ.iInf_mem A₀ id fun χ hχ => (Finset.mem_filter.1 hχ).2.1)
    refine equivalent_iff.2 fun r => ⟨fun hφ => ?_, fun hψ => ?_⟩
    · rw [Formula.realize_iInf]
      exact fun χ hχ => (Finset.mem_filter.1 hχ).2.2 r hφ
    · by_contra hnφ
      refine hFu ⟨⟨r.carrier, r.xs, fun χ hχ => ?_⟩⟩
      rcases hF hχ with (hP | hA) | rfl
      · exact r.realize χ hP
      · exact (Formula.realize_iInf _ _).1 hψ χ (Finset.mem_filter.2 ⟨hχ, hA⟩)
      · exact hnφ
  obtain ⟨r'⟩ := h₁
  let AN : L.FormulaSet σ := {χ | χ ∈ Δ ∧ ¬χ.Realize r'.xs}
  -- A realization of `P` and `φ`, and of no formula of `Δ` that `r'` fails.
  have h₂ : IsSatisfiable (P ∪ {φ} ∪ Formula.not '' AN) := by
    by_contra hunsat
    obtain ⟨F, hF, hFu⟩ := exists_finset_not_isSatisfiable hunsat
    obtain ⟨B₀, hB₀, hB₀F⟩ := Finset.subset_set_image_iff.1
      (fun χ hχ => (Finset.mem_filter.1 hχ).2 :
        ↑(F.filter (· ∈ Formula.not '' AN)) ⊆ Formula.not '' AN)
    have hψA : P.Models (φ.imp (Formula.iSup B₀ id)) := by
      intro r hφ
      rw [Formula.realize_iSup]
      by_contra hn
      push Not at hn
      refine hFu ⟨⟨r.carrier, r.xs, fun χ hχ => ?_⟩⟩
      by_cases hχN : χ ∈ Formula.not '' AN
      · have hmem : χ ∈ B₀.image Formula.not := by
          rw [hB₀F]
          exact Finset.mem_filter.2 ⟨hχ, hχN⟩
        obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hmem
        exact hn θ hθ
      · rcases hF hχ with (hP | rfl) | hχN'
        · exact r.realize χ hP
        · exact hφ
        · exact absurd hχN' hχN
    obtain ⟨χ, hχB, hχy⟩ := (Formula.realize_iSup _ _).1
      (r'.realize _ (Or.inl (Or.inr ⟨hΔ.iSup_mem B₀ id fun χ hχ => (hB₀ hχ).1, hψA⟩)))
    exact (hB₀ hχB).2 hχy
  obtain ⟨r⟩ := h₂
  refine r'.realize φ.not (Or.inr rfl) (H (r.restrict fun _ h => Or.inl (Or.inl h))
    (r'.restrict fun _ h => Or.inl (Or.inl h)) (fun χ hχ => ⟨hχ.1, ?_⟩)
    (r.realize φ (Or.inl (Or.inr rfl))))
  by_contra hχy
  exact r.realize _ (Or.inr ⟨χ, ⟨hχ.1, hχy⟩, rfl⟩) hχ.2

/-- **Separation** for a set of formulas `Γ` at once: every formula of `Γ` is equivalent modulo `P`
to a formula of `Δ` iff, between realizations of `P`, containment of `Δ`-types implies containment
of `Γ`-types. -/
theorem forall_exists_equivalent_iff_forall_realization (hΔ : IsFragment Δ)
    (Γ : L.FormulaSet σ) :
    (∀ φ ∈ Γ, ∃ ψ ∈ Δ, P.Equivalent φ ψ) ↔ ∀ r r' : P.Realization,
      Formula.typeOf Δ r.xs ⊆ Formula.typeOf Δ r'.xs →
        Formula.typeOf Γ r.xs ⊆ Formula.typeOf Γ r'.xs :=
  ⟨fun h r r' hsub φ hφ =>
    ⟨hφ.1, (exists_equivalent_iff_forall_realization hΔ φ).1 (h φ hφ.1) r r' hsub hφ.2⟩,
    fun h φ hφΓ => (exists_equivalent_iff_forall_realization hΔ φ).2
      fun r r' hsub hφ => (h r r' hsub ⟨hφΓ, hφ⟩).2⟩

/-- **Separation** for a negation-closed class: containment of types may be replaced by equality
of types. -/
theorem exists_equivalent_iff_forall_realization_typeOf_eq (D : L.FormulaClass) [NegClosed D]
    (hD : IsFragment (D σ)) (φ : L.Formula σ) :
    (∃ ψ ∈ D σ, P.Equivalent φ ψ) ↔ ∀ r r' : P.Realization,
      Formula.typeOf (D σ) r.xs = Formula.typeOf (D σ) r'.xs →
        φ.Realize r.xs → φ.Realize r'.xs := by
  simp only [exists_equivalent_iff_forall_realization hD, Formula.typeOf_subset_iff_eq D]

end FormulaSet

/-! ### Theories -/

namespace Theory

variable {T : L.Theory}

variable (T σ) in
/-- A realization of `T` in context `σ`: a model of `T` with nonempty sorts, in the universe of the
language, with a tuple of shape `σ`. It is a realization of the sentences of `T` lifted to `σ`. -/
abbrev Realization :=
  FormulaSet.Realization (Sentence.lift '' T : L.FormulaSet σ)

instance Realization.model (r : T.Realization σ) : r.carrier ⊨ T :=
  model_of_realize_lift_image r.realize

/-- A tuple in a model of `T`, as a realization of `T`. -/
def Realization.ofModel (M : S → Type (max z u v)) [L.Structure M] [∀ s, Nonempty (M s)]
    [M ⊨ T] (xs : M [^] σ) : T.Realization σ :=
  ⟨M, xs, realize_lift_image xs⟩

@[simp]
theorem Realization.ofModel_xs (M : S → Type (max z u v)) [L.Structure M] [∀ s, Nonempty (M s)]
    [M ⊨ T] (xs : M [^] σ) : (Realization.ofModel (T := T) M xs).xs = xs :=
  rfl

/-- Equivalence modulo a theory is equivalence modulo its sentences, lifted to the context. -/
theorem semanticallyEquivalent_iff_equivalent {φ ψ : L.Formula σ} :
    T.SemanticallyEquivalent φ ψ ↔ FormulaSet.Equivalent (Sentence.lift '' T) φ ψ :=
  modelsFormula_iff_models_lift

/-- **Separation** modulo a theory. Let `Δ` be closed under finite conjunctions and disjunctions.
A formula `φ` is `T`-equivalent to a formula of `Δ` iff `φ` passes from the tuple of a realization
of `T` to that of another whenever the `Δ`-type of the first is contained in that of the
second. -/
theorem exists_semanticallyEquivalent_iff_forall_realization {Δ : L.FormulaSet σ}
    (hΔ : IsFragment Δ) (φ : L.Formula σ) :
    (∃ ψ ∈ Δ, T.SemanticallyEquivalent φ ψ) ↔ ∀ r r' : T.Realization σ,
      Formula.typeOf Δ r.xs ⊆ Formula.typeOf Δ r'.xs → φ.Realize r.xs → φ.Realize r'.xs := by
  simp only [semanticallyEquivalent_iff_equivalent]
  exact FormulaSet.exists_equivalent_iff_forall_realization hΔ φ

/-! ### The tuple-extension criteria -/

variable {R : Set S}

/-- **Tuple-extension criterion.** `T` has quantifier elimination relative to `R` if, whenever the
tuples of two realizations `r`, `r'` of `T` have the same type in the formulas quantifier-free
relative to `R`, every new element `b` of a sort outside `R` next to the tuple of `r` has a
counterpart `c` next to some tuple `y` with the same complete type as the tuple of `r'`. -/
theorem hasQERelTo_of_pointed_extension
    (h : ∀ (σ : Arity S) (r r' : T.Realization σ),
      Formula.typeOf (qfRelTo L R σ) r.xs = Formula.typeOf (qfRelTo L R σ) r'.xs →
      ∀ s ∉ R, ∀ b : r.carrier s, ∃ (N : S → Type (max z u v)) (_ : L.Structure N)
        (y : N [^] σ) (c : N s),
          Formula.typeOf (all L σ) y = Formula.typeOf (all L σ) r'.xs ∧
          Formula.typeOf (qfRelTo L R (σ ⨯ ⦃s⦄)) ((r.xs, b) : r.carrier [^] (σ ⨯ ⦃s⦄)) =
            Formula.typeOf (qfRelTo L R (σ ⨯ ⦃s⦄)) ((y, c) : N [^] (σ ⨯ ⦃s⦄))) :
    T.HasQERelTo R := by
  refine hasQERelTo_of_sortElim fun s hs σ φ hφ =>
    (exists_semanticallyEquivalent_iff_forall_realization (Formula.isFragment_qfRelTo R) _).2 ?_
  intro r r' hsub hex
  obtain ⟨b, hb⟩ := Formula.realize_ex.1 hex
  obtain ⟨N, _, y, c, hy, hc⟩ := h σ r r' ((Formula.typeOf_subset_iff_eq _).1 hsub) s hs b
  exact (Formula.realize_iff_of_typeOf_eq hy (Set.mem_univ _)).1
    (Formula.realize_ex.2 ⟨c, (Formula.realize_iff_of_typeOf_eq hc hφ).1 hb⟩)

/-- **Tuple-extension criterion, with elementary extensions**: as
`hasQERelTo_of_pointed_extension`, with the counterpart `c` in an elementary extension of the model
of `r'`, next to the image of its tuple. -/
theorem hasQERelTo_of_tuple_extension
    (h : ∀ (σ : Arity S) (r r' : T.Realization σ),
      Formula.typeOf (qfRelTo L R σ) r.xs = Formula.typeOf (qfRelTo L R σ) r'.xs →
      ∀ s ∉ R, ∀ b : r.carrier s, ∃ (N : S → Type (max z u v)) (_ : L.Structure N)
        (j : r'.carrier ↪ₑ[L] N) (c : N s),
          Formula.typeOf (qfRelTo L R (σ ⨯ ⦃s⦄)) ((r.xs, b) : r.carrier [^] (σ ⨯ ⦃s⦄)) =
            Formula.typeOf (qfRelTo L R (σ ⨯ ⦃s⦄)) ((r'.xs.map j, c) : N [^] (σ ⨯ ⦃s⦄))) :
    T.HasQERelTo R :=
  hasQERelTo_of_pointed_extension fun σ r r' htp s hs b =>
    let ⟨N, _, j, c, hc⟩ := h σ r r' htp s hs b
    ⟨N, inferInstance, r'.xs.map j, c, j.typeOf_map r'.xs, hc⟩

end Theory

end ManySorted.Language
