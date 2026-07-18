/-
Based on the corresponding Mathlib file by Aaron Anderson.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Quotient
import MultisortedLogic.Semantics

/-!
# Quotients of First-Order Structures

This file defines prestructures and quotients of first-order structures.

## Main Definitions

- If `s` is a setoid (equivalence relation) on `M`, a `MSFirstOrder.Language.Prestructure s`
  is the data for a first-order structure on `M` that will still be a structure when modded out
  by `s`.
- The structure `MSFirstOrder.Language.quotientStructure s` is the resulting structure on
  `Quotient S`.
-/


namespace MSFirstOrder

namespace Language

variable {Sorts : Type*} (L : Language Sorts) {M : Fam Sorts} {σ : Signature Sorts}

open Structure
open Signature Interpret
open Fam

/-- A prestructure is a first-order structure with a `Setoid` equivalence relation on it,
  such that quotienting by that equivalence relation is still a structure. -/
class Prestructure (S : MSSetoid M) where
  /-- The underlying first-order structure -/
  toStructure : L.Structure M
  fun_equiv {t : Sorts} :
      ∀ {σ : Signature Sorts} {f : L.Functions σ t} (x y : M[^]σ),
        x ≈ y →
          @funMap Sorts L M toStructure σ t f x ≈
            @funMap Sorts L M toStructure σ t f y
  rel_equiv :
      ∀ {σ : Signature Sorts} {r : L.Relations σ} (x y : M[^]σ),
        x ≈ y →
          (@RelMap Sorts L M toStructure σ r x ↔
            @RelMap Sorts L M toStructure σ r y)

variable {L} {S : MSSetoid M}
variable [ps : L.Prestructure S]

noncomputable
instance quotientStructure : L.Structure (MSQuotient S) where
  funMap {σ : Signature Sorts} t f x := by
    letI : MSSetoid M := S
    exact
      Quotient.map
        (fun y : M[^]σ => @funMap Sorts L M ps.toStructure σ t f y)
        (fun x y hxy => ps.fun_equiv (f := f) x y hxy)
        (Interpret.choice (R := S) x)

  RelMap {σ : Signature Sorts} r x := by
    letI : MSSetoid M := S
    exact
      Quotient.lift
        (fun y : M[^]σ => @RelMap Sorts L M ps.toStructure σ r y)
        (fun x y hxy => propext <| ps.rel_equiv (r := r) x y hxy)
        (Interpret.choice (R := S) x)

theorem funMap_eq {t} (f : L.Functions σ t) (x : MSQuotient S [^] σ) :
    funMap f x = Quotient.map
        (fun y : M[^]σ => @funMap Sorts L M ps.toStructure σ t f y)
        (fun x y hxy => ps.fun_equiv (f := f) x y hxy)
        (Interpret.choice (R := S) x) := by rfl

theorem relMap_eq (r : L.Relations σ) (x : MSQuotient S [^] σ) :
  RelMap r x ↔ Quotient.lift
        (fun y : M[^]σ => @RelMap Sorts L M ps.toStructure σ r y)
        (fun x y hxy => propext (ps.rel_equiv (r := r) x y hxy))
        (Interpret.choice (R := S) x) := by rfl

variable (S)

theorem funMap_quotient_mk' {σ t} (f : L.Functions σ t) (x : M [^] σ) :
    (funMap f (Interpret.toQuot (R := S) x)) =
      ⟦@funMap Sorts L M ps.toStructure σ t f x⟧ := by
  letI : MSSetoid M := S
  rw [funMap_eq]
  simp [Interpret.choice_toQuot]
  rfl

theorem relMap_quotient_mk' {σ : Signature Sorts} (r : L.Relations σ) (x : M [^] σ) :
    (RelMap r (Interpret.toQuot (R := S) x)) ↔ @RelMap Sorts L M ps.toStructure σ r x := by
  simp only [RelMap, Interpret.choice_toQuot, Quotient.lift_mk]

theorem Term.realize_quotient_mk' {β : Fam Sorts} (t : L.Term β σ) (x : β →ₛ M) :
    (t.realize (MSQuotient.mk S ∘ₛ x)) =
      Interpret.toQuot (R := S) (@Term.realize _ _ M ps.toStructure _ _ x t) := by
  letI : MSSetoid M := S
  induction t with
  | var => rfl
  | func _ _ ih =>
      simp only [realize_func, ih, funMap_quotient_mk']
      rfl
  | prod _ _ ih₁ ih₂ =>
      simp only [realize_prod, ih₁, ih₂, Interpret.toQuot]
      simpa only using
        (Interpret.map_prod (f := MSQuotient.mk S) (x₁ :=
            @Term.realize Sorts L M ps.toStructure β _ x _) (x₂ :=
            @Term.realize Sorts L M ps.toStructure β _ x _)).symm
  | nil =>
      simp only [reduce_nil, PUnit.default_eq_unit, Interpret.toQuot]

end Language

end MSFirstOrder
