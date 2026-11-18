/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.ElementaryMaps
public import MultisortedLogic.Substructures

/-!
# Elementary substructures

A substructure is elementary when every formula holds of a tuple from it in the substructure iff
it holds of the tuple in the whole structure.

## Main definitions

* `Substructure.IsElementary`.
* `ElementarySubstructure L M`, with the inclusion `ElementarySubstructure.subtype` as an
  elementary embedding.

## Main results

* `Substructure.isElementary_of_exists`: the Tarski–Vaught test.
* `ElementarySubstructure.theory_model_iff`: an elementary substructure is a model of the same
  theories as `M`.

## Implementation notes

Mathlib's part on sets meeting the definable sets is not included.

## References

This file was originally based on `Mathlib/ModelTheory/ElementarySubstructures.lean`, by Aaron
Anderson.
-/

@[expose] public section

universe u v w z

namespace ManySorted.Language

open Arity Structure

variable {S : Type z} {L : Language.{u, v} S} {M : S → Type w} [L.Structure M]

/-- A substructure is elementary when every formula holds of a tuple from it in the substructure
iff it holds of the tuple in `M`. -/
def Substructure.IsElementary (A : L.Substructure M) : Prop :=
  ∀ ⦃σ : Arity S⦄ (φ : L.Formula σ) (x : (fun s => ↥(A s)) [^] σ),
    φ.Realize (x.map fun _ a => a.1) ↔ φ.Realize x

variable (L M) in
/-- An elementary substructure of `M`. -/
structure ElementarySubstructure where
  /-- The underlying substructure. -/
  toSubstructure : L.Substructure M
  isElementary' : toSubstructure.IsElementary

namespace ElementarySubstructure

instance : DFunLike (L.ElementarySubstructure M) S fun s => Set (M s) where
  coe A := A.toSubstructure
  coe_injective A B h := by
    obtain ⟨A, _⟩ := A
    obtain ⟨B, _⟩ := B
    obtain rfl : A = B := DFunLike.coe_injective h
    rfl

instance : CoeOut (L.ElementarySubstructure M) (L.Substructure M) :=
  ⟨toSubstructure⟩

variable {A B : L.ElementarySubstructure M} {s : S}

@[simp]
theorem coe_toSubstructure (A : L.ElementarySubstructure M) : ⇑(A : L.Substructure M) = ⇑A :=
  rfl

@[simp]
theorem mem_toSubstructure {x : M s} : x ∈ (A : L.Substructure M) s ↔ x ∈ A s :=
  Iff.rfl

/-- Two elementary substructures are equal if they have the same elements. -/
@[ext]
theorem ext (h : ∀ s (x : M s), x ∈ A s ↔ x ∈ B s) : A = B :=
  DFunLike.coe_injective (funext fun s => Set.ext (h s))

instance : PartialOrder (L.ElementarySubstructure M) :=
  PartialOrder.lift _ DFunLike.coe_injective

/-- The structure induced on an elementary substructure. -/
instance inducedStructure (A : L.ElementarySubstructure M) : L.Structure fun s => ↥(A s) :=
  Substructure.inducedStructure (A := A.toSubstructure)

@[simp]
theorem isElementary (A : L.ElementarySubstructure M) : (A : L.Substructure M).IsElementary :=
  A.isElementary'

/-- The inclusion of an elementary substructure, as an elementary embedding. -/
def subtype (A : L.ElementarySubstructure M) : (fun s => ↥(A s)) ↪ₑ[L] M where
  toFun _ a := a.1
  map_formula' φ xs := A.isElementary' φ xs

@[simp]
theorem subtype_apply (x : A s) : A.subtype s x = x :=
  rfl

@[simp]
theorem coe_subtype (A : L.ElementarySubstructure M) : ⇑A.subtype = fun _ => Subtype.val :=
  rfl

theorem subtype_injective (A : L.ElementarySubstructure M) (s : S) :
    Function.Injective (A.subtype s) :=
  Subtype.coe_injective

/-- The top substructure is elementary. -/
instance : Top (L.ElementarySubstructure M) :=
  ⟨⟨⊤, fun _ φ x => (Substructure.realize_formula_top φ x).symm⟩⟩

instance : Inhabited (L.ElementarySubstructure M) :=
  ⟨⊤⟩

theorem mem_top (x : M s) : x ∈ (⊤ : L.ElementarySubstructure M) s :=
  Set.mem_univ x

@[simp]
theorem coe_top : ⇑(⊤ : L.ElementarySubstructure M) = fun _ => Set.univ :=
  rfl

theorem realize_sentence (A : L.ElementarySubstructure M) (φ : L.Sentence) :
    (fun s => ↥(A s)) ⊨ φ ↔ M ⊨ φ :=
  A.subtype.map_sentence φ

@[simp]
theorem theory_model_iff (A : L.ElementarySubstructure M) (T : L.Theory) :
    (fun s => ↥(A s)) ⊨ T ↔ M ⊨ T :=
  A.subtype.theory_model_iff T

instance theory_model {T : L.Theory} [h : M ⊨ T] {A : L.ElementarySubstructure M} :
    (fun s => ↥(A s)) ⊨ T :=
  (theory_model_iff A T).2 h

/-- The sorts of an elementary substructure of a structure with nonempty sorts are nonempty. -/
instance nonempty [∀ s, Nonempty (M s)] (A : L.ElementarySubstructure M) (s : S) :
    Nonempty (A s) := by
  obtain ⟨y, -⟩ := Formula.realize_ex.1 ((A.subtype.map_formula
    ((⊤ : L.Formula (⦃⦄ ⨯ ⦃s⦄)).ex ⦃s⦄) PUnit.unit).1
      (Formula.realize_ex.2 ⟨Classical.arbitrary (M s), Formula.realize_top.2 trivial⟩))
  exact ⟨y⟩

theorem elementarilyEquivalent (A : L.ElementarySubstructure M) :
    L.ElementarilyEquivalent (fun s => ↥(A s)) M :=
  A.subtype.elementarilyEquivalent

end ElementarySubstructure

namespace Substructure

/-- **The Tarski–Vaught test** for substructures: a substructure is elementary if every formula with
one variable over it that has a witness in `M` has one in the substructure. -/
theorem isElementary_of_exists (A : L.Substructure M)
    (htv : ∀ {σ : Arity S} {s : S} (φ : L.Formula (σ ⨯ ⦃s⦄)) (x : (fun s => ↥(A s)) [^] σ)
      (b : M s), φ.Realize (((x.map fun _ a => a.1), b) : M [^] (σ ⨯ ⦃s⦄)) →
        ∃ a : A s, φ.Realize (((x.map fun _ a => a.1), a.1) : M [^] (σ ⨯ ⦃s⦄))) :
    A.IsElementary :=
  fun _ φ x => A.subtype.isElementary_of_exists htv φ x

/-- A substructure that passes the Tarski–Vaught test, as an elementary substructure. -/
def toElementarySubstructure (A : L.Substructure M)
    (htv : ∀ {σ : Arity S} {s : S} (φ : L.Formula (σ ⨯ ⦃s⦄)) (x : (fun s => ↥(A s)) [^] σ)
      (b : M s), φ.Realize (((x.map fun _ a => a.1), b) : M [^] (σ ⨯ ⦃s⦄)) →
        ∃ a : A s, φ.Realize (((x.map fun _ a => a.1), a.1) : M [^] (σ ⨯ ⦃s⦄))) :
    L.ElementarySubstructure M :=
  ⟨A, A.isElementary_of_exists htv⟩

@[simp]
theorem coe_toElementarySubstructure (A : L.Substructure M)
    (htv : ∀ {σ : Arity S} {s : S} (φ : L.Formula (σ ⨯ ⦃s⦄)) (x : (fun s => ↥(A s)) [^] σ)
      (b : M s), φ.Realize (((x.map fun _ a => a.1), b) : M [^] (σ ⨯ ⦃s⦄)) →
        ∃ a : A s, φ.Realize (((x.map fun _ a => a.1), a.1) : M [^] (σ ⨯ ⦃s⦄))) :
    ⇑(A.toElementarySubstructure htv) = ⇑A :=
  rfl

end Substructure

end ManySorted.Language
