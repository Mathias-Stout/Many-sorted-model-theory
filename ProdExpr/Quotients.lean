/-
Based on the corresponding Mathlib file by Aaron Anderson.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Quotient
import ProdExpr.Semantics

/-!
# Quotients of First-Order MSStructures

This file defines prestructures and quotients of first-order structures.

## Main Definitions

- If `s` is a setoid (equivalence relation) on `M`, a `MSFirstOrder.MSLanguage.MSPrestructure s`
  is the data for a first-order structure on `M` that will still be a structure when modded out
  by `s`.
- The structure `MSFirstOrder.MSLanguage.quotientMSStructure s` is the resulting structure on
  `Quotient S`.
-/


namespace MSFirstOrder

namespace MSLanguage

variable {Sorts : Type*} (L : MSLanguage Sorts) {M : Fam Sorts} {σ : Signature Sorts}

open MSStructure
open Signature Interpret
open Fam

/-- A prestructure is a first-order structure with a `Setoid` equivalence relation on it,
  such that quotienting by that equivalence relation is still a structure. -/
class MSPrestructure (S : MSSetoid M) where
  /-- The underlying first-order structure -/
  toMSStructure : L.MSStructure M
  fun_equiv {t : Sorts} :
      ∀ {σ : Signature Sorts} {f : L.Functions σ t} (x y : M[^]σ),
        x ≈ y →
          @funMap Sorts L M toMSStructure σ t f x ≈
            @funMap Sorts L M toMSStructure σ t f y
  rel_equiv :
      ∀ {σ : Signature Sorts} {r : L.Relations σ} (x y : M[^]σ),
        x ≈ y →
          @RelMap Sorts L M toMSStructure σ r x =
            @RelMap Sorts L M toMSStructure σ r y

variable {L} {S : MSSetoid M}
variable [ps : L.MSPrestructure S]

noncomputable
instance quotientMSStructure : L.MSStructure (MSQuotient S) where
  funMap {σ : Signature Sorts} t f x := by
    letI : MSSetoid M := S
    exact
      Quotient.map
        (fun y : M[^]σ => @funMap Sorts L M ps.toMSStructure σ t f y)
        (fun x y hxy => ps.fun_equiv (f := f) x y hxy)
        (Interpret.choice (R := S) x)

  RelMap {σ : Signature Sorts} r x := by
    letI : MSSetoid M := S
    exact
      Quotient.lift
        (fun y : M[^]σ => @RelMap Sorts L M ps.toMSStructure σ r y)
        (fun x y hxy => ps.rel_equiv (r := r) x y hxy)
        (Interpret.choice (R := S) x)

theorem funMap_eq {t} (f : L.Functions σ t) (x : MSQuotient S [^] σ) :
    funMap f x = Quotient.map
        (fun y : M[^]σ => @funMap Sorts L M ps.toMSStructure σ t f y)
        (fun x y hxy => ps.fun_equiv (f := f) x y hxy)
        (Interpret.choice (R := S) x) := by rfl

theorem relMap_eq (r : L.Relations σ) (x : MSQuotient S [^] σ) :
  RelMap r x ↔ Quotient.lift
        (fun y : M[^]σ => @RelMap Sorts L M ps.toMSStructure σ r y)
        (fun x y hxy => ps.rel_equiv (r := r) x y hxy)
        (Interpret.choice (R := S) x) := by rfl

variable (S)

theorem funMap_quotient_mk' {σ t} (f : L.Functions σ t) (x : M [^] σ) :
    (funMap f (Interpret.toQuot (R := S) x)) =
      ⟦@funMap Sorts L M ps.toMSStructure σ t f x⟧ := by
  letI : MSSetoid M := S
  rw [funMap_eq]
  simp [Interpret.choice_toQuot]
  rfl

theorem relMap_quotient_mk' {σ : Signature Sorts} (r : L.Relations σ) (x : M [^] σ) :
    (RelMap r (Interpret.toQuot (R := S) x)) ↔ @RelMap Sorts L M ps.toMSStructure σ r x := by
  letI : MSSetoid M := S
  rw [relMap_eq]
  simp only [Interpret.choice_toQuot]
  rfl

theorem Term.realize_quotient_mk' {β : Fam Sorts} (t : L.Term β σ) (x : β →ₛ M) :
    (t.realize (MSQuotient.mk S ∘ₛ x)) =
      Interpret.toQuot (R := S) (@Term.realize Sorts L M ps.toMSStructure β σ x t) := by
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
            @Term.realize Sorts L M ps.toMSStructure β _ x _) (x₂ :=
            @Term.realize Sorts L M ps.toMSStructure β _ x _)).symm
  | nil =>
      simp only [reduce_nil, PUnit.default_eq_unit, Interpret.toQuot]

end MSLanguage

end MSFirstOrder
