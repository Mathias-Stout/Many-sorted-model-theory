/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout, Jonas van der Schaaf
-/
module

public import MultisortedLogic.Quotients
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Ultraproducts and Łoś's theorem

The ultraproduct of a family of structures `M i` along an ultrafilter `U` has carriers
`fun s => Quotient (eventuallyEqSetoid U M s)`, the quotient of the product family by eventual
equality. It is the quotient structure of `Quotients.lean`: function symbols act coordinatewise
on the product, relations hold at `U`-almost every index, and eventual equality is a congruence.

## Main definitions

* `Language.Ultraproduct.Pre U M`: the product family, carrying the structure the ultraproduct is
  a quotient of.
* `Language.Ultraproduct U M`: the ultraproduct.

## Main results

* `Ultraproduct.realize_formula` (Łoś): a formula holds of a tuple of classes iff it holds of the
  representatives at `U`-almost every index.

The compactness theorem, proved with it, is in `Satisfiability.lean`.

## References

This file was originally based on `Mathlib/ModelTheory/Ultraproducts.lean`, by Aaron Anderson.
-/

@[expose] public section

universe u v w w' z

namespace ManySorted

open Arity Filter

variable {S : Type z} {I : Type w'} {M : I → S → Type w}

namespace Language.Ultraproduct

/-- The product of the family `M`, as the carrier of the structure that the ultraproduct along
`U` is a quotient of. We make this alias to distinguish the structure we want to put on the
product before quotienting from the natural product structure. -/
def Pre (_U : Ultrafilter I) (M : I → S → Type w) : S → Type (max w' w) :=
  fun s => ∀ i, M i s

end Language.Ultraproduct

open Language.Ultraproduct (Pre)

namespace Arity.Interpret

variable {U : Ultrafilter I}

/-- Assemble a family of tuples into a tuple of families. -/
def ofPi : ∀ {σ : Arity S}, (∀ i, M i [^] σ) → Pre U M [^] σ
  | .nil, _ => PUnit.unit
  | .of _, x => x
  | .prod _ _, x => (ofPi fun i => (x i).1, ofPi fun i => (x i).2)

/-- The `i`-th coordinate of a tuple of families. -/
def eval {σ : Arity S} (i : I) (x : Pre U M [^] σ) : M i [^] σ :=
  x.map fun _ a => a i

@[simp]
theorem eval_ofPi : ∀ {σ : Arity S} (x : ∀ i, M i [^] σ) (i : I), (ofPi (U := U) x).eval i = x i
  | .nil, _, _ => rfl
  | .of _, _, _ => rfl
  | .prod _ _, x, i => congrArg₂ Prod.mk (eval_ofPi (fun i => (x i).1) i)
      (eval_ofPi (fun i => (x i).2) i)

@[simp]
theorem ofPi_fst {σ τ : Arity S} (x : ∀ i, M i [^] (σ ⨯ τ)) :
    (ofPi (U := U) x).1 = ofPi fun i => (x i).1 := rfl

@[simp]
theorem ofPi_snd {σ τ : Arity S} (x : ∀ i, M i [^] (σ ⨯ τ)) :
    (ofPi (U := U) x).2 = ofPi fun i => (x i).2 := rfl

@[simp]
theorem get_ofPi : ∀ {σ : Arity S} (x : ∀ i, M i [^] σ) (s : S) (j : σ.Idx s),
    (ofPi (U := U) x).get s j = fun i => (x i).get s j
  | _, _, _, .var => rfl
  | _, x, _, .left j => get_ofPi (fun i => (x i).1) _ j
  | _, x, _, .right j => get_ofPi (fun i => (x i).2) _ j

@[simp]
theorem get_eval {σ : Arity S} (x : Pre U M [^] σ) (i : I) (s : S) (j : σ.Idx s) :
    (x.eval i).get s j = x.get s j i :=
  get_map _ x s j

@[simp]
theorem eval_mk {σ τ : Arity S} (x : Pre U M [^] σ) (y : Pre U M [^] τ) (i : I) :
    eval (σ := σ ⨯ τ) i (x, y) = (x.eval i, y.eval i) := rfl

@[simp]
theorem eval_fst {σ τ : Arity S} (x : Pre U M [^] (σ ⨯ τ)) (i : I) :
    (x.eval i).1 = x.1.eval i := rfl

@[simp]
theorem eval_snd {σ τ : Arity S} (x : Pre U M [^] (σ ⨯ τ)) (i : I) :
    (x.eval i).2 = x.2.eval i := rfl

end Arity.Interpret

namespace Language

open Structure

variable {L : Language.{u, v} S}

namespace Ultraproduct

/-- Eventual equality along `U`, on the product of the carriers of sort `s`. -/
def eventuallyEqSetoid (U : Ultrafilter I) (M : I → S → Type w) (s : S) :
    Setoid (Pre U M s) := U.productSetoid fun i => M i s

/-- Two tuples of families are entrywise eventually equal iff they are eventually equal. -/
theorem interpretSetoid_iff {U : Ultrafilter I} {σ : Arity S} {x y : Pre U M [^] σ} :
    (Interpret.setoid (eventuallyEqSetoid U M) σ).r x y ↔
      ∀ᶠ i in (U : Filter I), x.eval i = y.eval i := by
  induction σ with
  | nil => exact ⟨fun _ => .of_forall fun _ => rfl, fun _ s i => nomatch i⟩
  | of s => exact ⟨fun h => h s .var, fun h t i => by cases i; exact h⟩
  | prod σ τ ih₁ ih₂ =>
    have : (Interpret.setoid (eventuallyEqSetoid U M) (σ ⨯ τ)).r x y ↔
        (Interpret.setoid (eventuallyEqSetoid U M) σ).r x.1 y.1 ∧
          (Interpret.setoid (eventuallyEqSetoid U M) τ).r x.2 y.2 :=
      ⟨fun h => ⟨fun s i => h s (.left i), fun s i => h s (.right i)⟩,
        fun h s i => by
          cases i with
          | left i => exact h.1 s i
          | right i => exact h.2 s i⟩
    rw [this, ih₁, ih₂, ← eventually_and]
    exact eventually_congr (.of_forall fun _ =>
      ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩)

variable (U : Ultrafilter I) [∀ i, L.Structure (M i)]

/-- Functions act coordinatewise; relations hold `U`-almost everywhere. This last part makes this
structure different from the natural product structure. -/
instance : L.Structure (Pre U M) where
  funMap f x := fun i => funMap f (x.eval i)
  RelMap r x := ∀ᶠ i in (U : Filter I), RelMap r (x.eval i)

instance : L.Congruence (eventuallyEqSetoid U M) where
  funMap_rel {_ _} f {_ _} h := show ∀ᶠ i in (U : Filter I), _ = _ from
    (interpretSetoid_iff.1 h).mono fun _ hi => congrArg (funMap f) hi
  relMap_iff {_} R {_ _} h :=
    eventually_congr <| (interpretSetoid_iff.1 h).mono fun _ hi => by rw [hi]

end Ultraproduct

open Ultraproduct (eventuallyEqSetoid)

/-- The ultraproduct of the family `M` along the ultrafilter `U`. -/
abbrev Ultraproduct (U : Ultrafilter I) (M : I → S → Type w) : S → Type (max w' w) :=
  fun s => Quotient (eventuallyEqSetoid U M s)

namespace Ultraproduct

variable (U : Ultrafilter I) [∀ i, L.Structure (M i)]

@[simp]
theorem funMap_pre {σ : Arity S} {t : S} (f : L.Functions σ t) (x : Pre U M [^] σ) :
    funMap (M := Pre U M) f x = fun i => funMap f (x.eval i) :=
  rfl

@[simp]
theorem relMap_pre {σ : Arity S} (R : L.Relations σ) (x : Pre U M [^] σ) :
    RelMap (M := Pre U M) R x ↔ ∀ᶠ i in (U : Filter I), RelMap R (x.eval i) :=
  Iff.rfl

theorem funMap_mkQuot {σ : Arity S} {t : S} (f : L.Functions σ t) (x : Pre U M [^] σ) :
    funMap (M := Ultraproduct U M) f (Interpret.mkQuot _ x) =
      Quotient.mk _ fun i => funMap f (x.eval i) :=
  Language.funMap_mkQuot f x

theorem relMap_mkQuot {σ : Arity S} (R : L.Relations σ) (x : Pre U M [^] σ) :
    RelMap (M := Ultraproduct U M) R (Interpret.mkQuot _ x) ↔
      ∀ᶠ i in (U : Filter I), RelMap R (x.eval i) :=
  Language.relMap_mkQuot R x

theorem realize_term {Γ τ : Arity S} (t : L.Term Γ τ) (xs : Pre U M [^] Γ) :
    t.realize (M := Ultraproduct U M) (Interpret.mkQuot _ xs) =
      Interpret.mkQuot (eventuallyEqSetoid U M)
        (Interpret.ofPi fun i => t.realize (xs.eval i)) := by
  induction t with
  | var k =>
    simp only [Term.realize_var, Interpret.get_map, Interpret.get_eval]
    rfl
  | func f ts ih =>
    rw [Term.realize_func, ih, funMap_mkQuot]
    simp only [Interpret.eval_ofPi]
    rfl
  | nil => rfl
  | prod t₁ t₂ ih₁ ih₂ => rw [Term.realize_prod, ih₁, ih₂]; rfl

/-- **Łoś's theorem**: a formula holds of a tuple of classes in the ultraproduct iff it holds of
the representatives in `U`-almost every factor. -/
theorem realize_formula [∀ i s, Nonempty (M i s)] :
    ∀ {σ : Arity S} (φ : L.Formula σ) (xs : Pre U M [^] σ),
      φ.Realize (M := Ultraproduct U M) (Interpret.mkQuot _ xs) ↔
        ∀ᶠ i in (U : Filter I), φ.Realize (xs.eval i)
  | _, .falsum, _ => by simp only [Formula.realize_falsum, eventually_const]
  | _, .equal t₁ t₂, xs => by
    rw [Formula.realize_equal, realize_term, realize_term, Interpret.mkQuot_eq_iff,
      interpretSetoid_iff]
    simp only [Interpret.eval_ofPi, Formula.realize_equal]
  | _, .rel R ts, xs => by
    rw [Formula.realize_rel, realize_term, relMap_mkQuot]
    simp only [Interpret.eval_ofPi, Formula.realize_rel]
  | _, .imp φ ψ, xs => by
    rw [Formula.realize_imp, realize_formula φ xs, realize_formula ψ xs,
      ← Ultrafilter.eventually_imp]
    rfl
  | _, .all τ φ, xs => by
    classical
    simp only [Formula.realize_all]
    constructor
    · intro h
      by_contra hn
      rw [← Ultrafilter.eventually_not] at hn
      let zs : ∀ i, M i [^] τ := fun i =>
        if hex : ∃ y, ¬φ.Realize (xs.eval i, y) then hex.choose
        else Classical.arbitrary _
      have hz := (realize_formula φ (xs, Interpret.ofPi zs)).1 (h _)
      obtain ⟨i, hi, hni⟩ := (hz.and hn).exists
      simp only [Interpret.eval_mk, Interpret.eval_ofPi] at hi
      push Not at hni
      obtain ⟨y, hy⟩ := hni
      have hex : ∃ y, ¬φ.Realize (xs.eval i, y) := ⟨y, hy⟩
      have hzi : zs i = hex.choose := by simp [zs, hex]
      exact hex.choose_spec (hzi ▸ hi)
    · intro h ys
      obtain ⟨zs, rfl⟩ := Interpret.map_surjective (fun _ _ => Quotient.mk_surjective) ys
      exact (realize_formula φ (xs, zs)).2 (h.mono fun _ hi => hi _)

instance [∀ i s, Nonempty (M i s)] (s : S) : Nonempty (Ultraproduct U M s) :=
  ⟨Quotient.mk _ fun _ => Classical.arbitrary _⟩

end Ultraproduct

end Language

end ManySorted
