/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.DeltaMaps
public import MultisortedLogic.Satisfiability

/-!
# Realizing types

Two forms of the statement that a finitely satisfiable type is realized, both by compactness.

## Main results

* `Formula.exists_realize_of_finite`: a set of formulas over a tuple `y`, finitely realized next to
  `y`, is realized in some structure next to a tuple with the same complete type as `y`.
* `exists_elementaryEmbedding_realize`: a set of formulas with parameters from `N`, finitely
  realized in `N`, is realized in an elementary extension of `N`.
-/

@[expose] public section

universe u v z

namespace ManySorted.Language

open Arity Structure FormulaClass

variable {S : Type z} {L : Language.{u, v} S}

/-- **Realizing a type over a tuple**: a set of formulas in context `σ ⨯ τ`, each finite subset of
which is realized in `N` next to `y`, is realized in some structure next to a tuple `y'` with the
same complete type as `y`. -/
theorem Formula.exists_realize_of_finite {N : S → Type (max u v z)} [L.Structure N]
    [∀ s, Nonempty (N s)] {σ τ : Arity S} (y : N [^] σ) (P : Set (L.Formula (σ ⨯ τ)))
    (h : ∀ P₀ : Finset (L.Formula (σ ⨯ τ)), ↑P₀ ⊆ P →
      ∃ z : N [^] τ, ∀ φ ∈ P₀, φ.Realize ((y, z) : N [^] (σ ⨯ τ))) :
    ∃ (N' : S → Type (max u v z)) (_ : L.Structure N') (y' : N' [^] σ) (z : N' [^] τ),
      Formula.typeOf (FormulaClass.all L σ) y' = Formula.typeOf (FormulaClass.all L σ) y ∧
        ∀ φ ∈ P, φ.Realize ((y', z) : N' [^] (σ ⨯ τ)) := by
  classical
  have hleft : ∀ {P : S → Type (max u v z)} [L.Structure P] (y : P [^] σ) (z : P [^] τ)
      (φ : L.Formula σ), (φ.relabel fun _ => .left).Realize ((y, z) : P [^] (σ ⨯ τ)) ↔
        φ.Realize y :=
    fun _ _ φ => by simp
  obtain ⟨⟨N', ⟨y', z⟩, hQ⟩⟩ := FormulaSet.IsFinitelySatisfiable.isSatisfiable
    (P := (fun φ : L.Formula σ => φ.relabel fun _ => .left) '' {φ : L.Formula σ | φ.Realize y} ∪ P)
    fun Q₀ hQ₀ => by
      obtain ⟨z, hz⟩ := h (Q₀.filter (· ∈ P)) fun φ hφ => (Finset.mem_filter.1 hφ).2
      refine ⟨⟨N, (y, z), fun φ hφ => ?_⟩⟩
      rcases hQ₀ hφ with ⟨χ, hχ, rfl⟩ | hφP
      · exact (hleft y z χ).2 hχ
      · exact hz φ (Finset.mem_filter.2 ⟨hφ, hφP⟩)
  have hy : ∀ φ : L.Formula σ, φ.Realize y → φ.Realize y' := fun φ hφ =>
    (hleft y' z φ).1 (hQ _ (Or.inl ⟨φ, hφ, rfl⟩))
  exact ⟨N', inferInstance, y', z,
    ((Formula.typeOf_subset_iff_eq _).1 fun φ hφ => ⟨hφ.1, hy φ hφ.2⟩).symm,
    fun φ hφ => hQ φ (Or.inr hφ)⟩

/-- **Realizing types in elementary extensions**: a set of formulas in context `σ` with parameters
from `N`, each finite subset of which is realized in `N`, is realized in an elementary extension
of `N`, with the embedding as the values of the parameters. -/
theorem exists_elementaryEmbedding_realize {N : S → Type (max u v z)} [L.Structure N]
    [∀ s, Nonempty (N s)] {σ : Arity S} (p : L[[N]].FormulaSet σ)
    (h : ∀ p₀ : Finset (L[[N]].Formula σ), ↑p₀ ⊆ p →
      ∃ xs : N [^] σ, FormulaSet.RealizeWith (↑p₀ : L[[N]].FormulaSet σ) (fun _ => id) xs) :
    ∃ (P : S → Type (max u v z)) (_ : L.Structure P) (_ : ∀ s, Nonempty (P s)) (j : N ↪ₑ[L] P)
      (xs : P [^] σ), p.RealizeWith j xs := by
  classical
  obtain ⟨r⟩ := FormulaSet.IsFinitelySatisfiable.isSatisfiable
    (P := Sentence.lift '' (elementaryDiagram L N : L[[N]].FormulaSet ⦃⦄) ∪ p) fun p₀ hp₀ => by
      obtain ⟨xs, hxs⟩ := h (p₀.filter (· ∈ p)) fun ψ hψ => (Finset.mem_filter.1 hψ).2
      refine ⟨@FormulaSet.Realization.mk _ _ _ _ N (withConstantsStructure fun _ => id)
        inferInstance xs fun ψ hψ => ?_⟩
      rcases hp₀ hψ with ⟨χ, hχ, rfl⟩ | hψp
      · exact (Formula.realizeWith_lift _ χ xs).2
          ((ElementaryEmbedding.refl L N).realize_elementaryDiagram χ hχ)
      · exact hxs ψ (Finset.mem_filter.2 ⟨hψ, hψp⟩)
  let : L.Structure r.carrier := (L.lhomWithConstants N).reduct r.carrier
  have hreal := r.realize
  rw [← withConstantsStructure_reduct r.str] at hreal
  set v := constants (L := L) (M := r.carrier) (α := N)
  have hreal : FormulaSet.RealizeWith
      (Sentence.lift '' (elementaryDiagram L N : L[[N]].FormulaSet ⦃⦄) ∪ p) v r.xs := hreal
  exact ⟨r.carrier, inferInstance, inferInstance, .ofElementaryDiagram fun χ hχ =>
    (Formula.realizeWith_lift v χ r.xs).1 (hreal _ (Or.inl ⟨χ, hχ, rfl⟩)), r.xs,
    fun ψ hψ => hreal ψ (Or.inr hψ)⟩

end ManySorted.Language
