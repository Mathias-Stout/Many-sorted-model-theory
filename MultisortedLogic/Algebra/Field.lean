/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Algebra.Ring
public import Mathlib.Algebra.Field.Basic

/-!
# Field axioms

The axioms of fields and ordered fields as sentences in a ring language.

## Main definitions

* `FieldAxiom`, `OFieldAxiom`: the axioms, with `toSentence`, `toProp`,
  `realize_toSentence_iff_toProp` and `models_ax` as for the group axioms.
* `FieldTheory L s`: the theory of fields, with `models_FieldTheory`.

## References

This file was originally based on `Mathlib/ModelTheory/Algebra/Field/Basic.lean`, by Chris Hughes.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

universe u v w z

variable {S : Type z} (L : Language.{u, v} S) {M : S → Type w} [L.Structure M] (s : S)

/-- Axiom names for a field on sort `s`. -/
inductive FieldAxiom : Type
  | cring (ax : CommRingAxiom)
  | existsInv
  | existsPairNe

namespace FieldAxiom

/-- The sentence expressing a field axiom. -/
@[simp]
def toSentence [RingL L s] : FieldAxiom → L.Sentence
  | cring ax => ax.toSentence L s
  | existsInv => ∀' s (∼(#0 =' 0) ⟹ ∃' s (#1 *ₗ #0 =' 1))
  | existsPairNe => ∃' s (∃' s ∼(#1 =' #0))

/-- The mathematical content of a field axiom. -/
@[simp]
def toProp (K : Type*) [Add K] [Mul K] [Neg K] [Zero K] [One K] : FieldAxiom → Prop
  | cring ax => ax.toProp K
  | existsInv => ∀ x : K, x ≠ 0 → ∃ y : K, x * y = 1
  | existsPairNe => ∃ x y : K, x ≠ y

variable {L s} [RingL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)]
    [One (M s)] [CompatibleRingL L M s] (ax : FieldAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact CommRingAxiom.realize_toSentence_iff_toProp _
  all_goals simp

theorem models_ax [Field (M s)] [CompatibleRingL L M s] (ax : FieldAxiom) :
    M ⊨ ax.toSentence L s := by
  cases ax
  · exact CommRingAxiom.models_ax _
  all_goals rw [realize_toSentence_iff_toProp]
  · exact fun x hx => ⟨x⁻¹, mul_inv_cancel₀ hx⟩
  · exact ⟨0, 1, zero_ne_one⟩

end FieldAxiom

/-- Axiom names for an ordered field on sort `s`: a field with a total order, in which addition is
monotone and products of nonnegative elements are nonnegative. -/
inductive OFieldAxiom : Type
  | field (ax : FieldAxiom)
  | torder (ax : TOrderAxiom)
  | addLeAddRight
  | mulNonneg

namespace OFieldAxiom

/-- The sentence expressing an ordered-field axiom. -/
@[simp]
def toSentence [ORingL L s] : OFieldAxiom → L.Sentence
  | field ax => ax.toSentence L s
  | torder ax => ax.toSentence L s
  | addLeAddRight => ∀' s (∀' s (∀' s ((#2 ≤ₗ #1) ⟹ (#2 +ₗ #0 ≤ₗ #1 +ₗ #0))))
  | mulNonneg => ∀' s (∀' s ((0 ≤ₗ #1) ⟹ (0 ≤ₗ #0) ⟹ (0 ≤ₗ #1 *ₗ #0)))

/-- The mathematical content of an ordered-field axiom. -/
@[simp]
def toProp (K : Type*) [Add K] [Mul K] [Neg K] [Zero K] [One K] [LE K] : OFieldAxiom → Prop
  | field ax => ax.toProp K
  | torder ax => ax.toProp K
  | addLeAddRight => ∀ a b c : K, a ≤ b → a + c ≤ b + c
  | mulNonneg => ∀ a b : K, 0 ≤ a → 0 ≤ b → 0 ≤ a * b

variable {L s} [ORingL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)]
    [One (M s)] [LE (M s)] [CompatibleORingL L M s] (ax : OFieldAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact FieldAxiom.realize_toSentence_iff_toProp _
  · exact TOrderAxiom.realize_toSentence_iff_toProp _
  all_goals simp

theorem models_ax [Field (M s)] [LinearOrder (M s)] [IsOrderedRing (M s)]
    [CompatibleORingL L M s] (ax : OFieldAxiom) : M ⊨ ax.toSentence L s := by
  cases ax
  · exact FieldAxiom.models_ax _
  · exact TOrderAxiom.models_ax _
  all_goals rw [realize_toSentence_iff_toProp]
  · exact fun _ _ c h => add_le_add_left h c
  · exact fun _ _ => mul_nonneg

end OFieldAxiom

/-- The theory of fields on sort `s`. -/
def FieldTheory [RingL L s] : L.Theory :=
  Set.range (FieldAxiom.toSentence L s)

/-- A field is a model of `FieldTheory`. -/
theorem models_FieldTheory [RingL L s] [Field (M s)] [CompatibleRingL L M s] :
    M ⊨ FieldTheory L s :=
  (Theory.model_iff _).2 <| by
    rintro _ ⟨ax, rfl⟩
    exact FieldAxiom.models_ax ax

end ManySorted.Language
