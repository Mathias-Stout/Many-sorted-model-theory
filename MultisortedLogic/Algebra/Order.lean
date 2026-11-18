/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Algebra.Basic

/-!
# Order axioms

The axioms of partial and total orders on a sort `s`, as sentences in a language with an order.

## Main definitions

* `POrderAxiom`, `TOrderAxiom`: the axioms. For each, `toSentence` is the axiom as a sentence and
  `toProp` its content as a proposition about a type; they correspond by
  `realize_toSentence_iff_toProp`, and `models_ax` says that partial (linear) orders satisfy them.

## References

This file was originally based on `Mathlib/ModelTheory/Order.lean`, by Aaron Anderson.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

universe u v w z

variable {S : Type z} (L : Language.{u, v} S) {M : S → Type w} [L.Structure M] (s : S)

/-- Axiom names for a partial order on sort `s`. -/
inductive POrderAxiom : Type
  | leRefl
  | leTrans
  | leAntisymm

namespace POrderAxiom

/-- The sentence expressing a partial-order axiom. -/
@[simp]
def toSentence [OrderL L s] : POrderAxiom → L.Sentence
  | leRefl => ∀' s (#0 ≤ₗ #0)
  | leTrans => ∀' s (∀' s (∀' s ((#2 ≤ₗ #1) ⟹ (#1 ≤ₗ #0) ⟹ (#2 ≤ₗ #0))))
  | leAntisymm => ∀' s (∀' s ((#1 ≤ₗ #0) ⟹ (#0 ≤ₗ #1) ⟹ (#1 =' #0)))

/-- The mathematical content of a partial-order axiom. -/
@[simp]
def toProp (O : Type*) [LE O] : POrderAxiom → Prop
  | leRefl => ∀ x : O, x ≤ x
  | leTrans => ∀ x y z : O, x ≤ y → y ≤ z → x ≤ z
  | leAntisymm => ∀ x y : O, x ≤ y → y ≤ x → x = y

variable {L s} [OrderL L s]

theorem realize_toSentence_iff_toProp [LE (M s)] [CompatibleOrderL L M s] (ax : POrderAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax <;> simp

theorem models_ax [PartialOrder (M s)] [CompatibleOrderL L M s] (ax : POrderAxiom) :
    M ⊨ ax.toSentence L s := by
  rw [realize_toSentence_iff_toProp]
  cases ax
  · exact le_refl
  · exact fun _ _ _ => le_trans
  · exact fun _ _ => le_antisymm

end POrderAxiom

/-- Axiom names for a total order on sort `s`. -/
inductive TOrderAxiom : Type
  | porder (ax : POrderAxiom)
  | leTotal

namespace TOrderAxiom

/-- The sentence expressing a total-order axiom. -/
@[simp]
def toSentence [OrderL L s] : TOrderAxiom → L.Sentence
  | porder ax => ax.toSentence L s
  | leTotal => ∀' s (∀' s ((#1 ≤ₗ #0) ⊔ (#0 ≤ₗ #1)))

/-- The mathematical content of a total-order axiom. -/
@[simp]
def toProp (O : Type*) [LE O] : TOrderAxiom → Prop
  | porder ax => ax.toProp O
  | leTotal => ∀ x y : O, x ≤ y ∨ y ≤ x

variable {L s} [OrderL L s]

theorem realize_toSentence_iff_toProp [LE (M s)] [CompatibleOrderL L M s] (ax : TOrderAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact POrderAxiom.realize_toSentence_iff_toProp _
  · simp

theorem models_ax [LinearOrder (M s)] [CompatibleOrderL L M s] (ax : TOrderAxiom) :
    M ⊨ ax.toSentence L s := by
  cases ax
  · exact POrderAxiom.models_ax _
  · rw [realize_toSentence_iff_toProp]
    exact le_total

end TOrderAxiom

end ManySorted.Language
