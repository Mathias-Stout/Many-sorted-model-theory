/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Semantics

/-!
# Quotients of structures

The quotient of an `L`-structure `M` by a family of setoids `r s` on its carriers that is
compatible with the function and relation symbols. Its carriers are `fun s => Quotient (r s)`.

## Main definitions

* `Arity.Interpret.setoid`: the entrywise relation on tuples induced by a family of setoids.
* `Arity.Interpret.mkQuot`: the tuple of classes of the entries of a tuple.
* `Language.Congruence`: compatibility of a family of setoids with an `L`-structure.
* `Language.quotientStructure`: the `L`-structure on the quotient by a congruence.
* `Language.Congruence.mkHom`: the quotient map, as a homomorphism.

## Implementation notes

* Mathlib's one-sorted `Quotients.lean` bundles the setoid with a second structure on `M` into a
  class `Prestructure`. Here compatibility is a `Prop`-valued mixin `Congruence` on top of
  `[L.Structure M]`.
* A tuple of classes becomes the class of a tuple by recursion on the arity
  (`Interpret.quotChoice`), so the quotient structure needs no choice.

## References

This file was originally based on `Mathlib/ModelTheory/Quotients.lean`, by Aaron Anderson.
-/

@[expose] public section

universe u v w z

namespace ManySorted

open Arity

variable {S : Type z} {M : S → Type w}

namespace Arity.Interpret

/-- The entrywise relation on tuples induced by a family of setoids. -/
def setoid (rs : ∀ s, Setoid (M s)) (σ : Arity S) : Setoid (M [^] σ) where
  r x y := ∀ s i, (rs s).r (x.get s i) (y.get s i)
  iseqv :=
    ⟨fun _ s _ => (rs s).iseqv.refl _, fun h s i => (rs s).iseqv.symm (h s i),
      fun h h' s i => (rs s).iseqv.trans (h s i) (h' s i)⟩

/-- The tuple of classes of the entries of a tuple. -/
abbrev mkQuot (r : ∀ s, Setoid (M s)) {σ : Arity S} (x : M [^] σ) :
    (fun s => Quotient (r s)) [^] σ :=
  x.map fun s => Quotient.mk (r s)

/-- The class of a tuple, computed from the classes of its entries by recursion on the arity. -/
def quotChoice (r : ∀ s, Setoid (M s)) :
    ∀ {σ : Arity S}, (fun s => Quotient (r s)) [^] σ → Quotient (setoid r σ)
  | nil, _ => Quotient.mk _ PUnit.unit
  | of s, q => Quotient.map (sa := r s) (sb := setoid r ⦃s⦄) id
      (by intro a b h t i; cases i; exact h) q
  | prod σ τ, q =>
      Quotient.map₂ (sa := setoid r σ) (sb := setoid r τ) (sc := setoid r (σ ⨯ τ)) Prod.mk
        (by
          intro a₁ a₂ ha b₁ b₂ hb t i
          cases i with
          | left i => exact ha t i
          | right i => exact hb t i)
        (quotChoice r q.1) (quotChoice r q.2)

@[simp]
theorem quotChoice_mkQuot (r : ∀ s, Setoid (M s)) :
    ∀ {σ : Arity S} (x : M [^] σ), quotChoice r (mkQuot r x) = Quotient.mk (setoid r σ) x
  | nil, _ => rfl
  | of _, _ => rfl
  | prod _ _, x => by
      change Quotient.map₂ _ _ (quotChoice r (mkQuot r x.1)) (quotChoice r (mkQuot r x.2)) = _
      rw [quotChoice_mkQuot r x.1, quotChoice_mkQuot r x.2]
      rfl

theorem mkQuot_eq_iff (r : ∀ s, Setoid (M s)) {σ : Arity S} {x y : M [^] σ} :
    mkQuot r x = mkQuot r y ↔ (setoid r σ).r x y := by
  constructor
  · intro h s i
    have := congrArg (fun z => get z s i) h
    simp only [get_map] at this
    exact Quotient.exact this
  · intro h
    exact ext fun s i => by
      simp only [get_map]
      exact Quotient.sound (h s i)

end Arity.Interpret

namespace Language

open Structure

variable {L : Language.{u, v} S}

variable (L) in
/-- A family of setoids on the carriers of an `L`-structure that is compatible with its function
and relation symbols. -/
class Congruence [L.Structure M] (r : ∀ s, Setoid (M s)) : Prop where
  funMap_rel : ∀ {σ t} (f : L.Functions σ t) {x y : M [^] σ},
    (Interpret.setoid r σ).r x y → (r t).r (funMap f x) (funMap f y)
  relMap_iff : ∀ {σ} (R : L.Relations σ) {x y : M [^] σ},
    (Interpret.setoid r σ).r x y → (RelMap R x ↔ RelMap R y)

variable [L.Structure M] {r : ∀ s, Setoid (M s)} [L.Congruence r]

/-- The quotient of a structure by a congruence. -/
instance quotientStructure : L.Structure (fun s => Quotient (r s)) where
  funMap {_ t} f q :=
    Quotient.lift (fun x => Quotient.mk (r t) (funMap f x))
      (fun _ _ h => Quotient.sound (Congruence.funMap_rel f h)) (Interpret.quotChoice r q)
  RelMap R q :=
    Quotient.lift (RelMap R) (fun _ _ h => propext (Congruence.relMap_iff R h))
      (Interpret.quotChoice r q)

@[simp]
theorem funMap_mkQuot {σ : Arity S} {t : S} (f : L.Functions σ t) (x : M [^] σ) :
    funMap f (Interpret.mkQuot r x) = Quotient.mk (r t) (funMap f x) := by
  simp only [funMap, Interpret.quotChoice_mkQuot]
  rfl

@[simp]
theorem relMap_mkQuot {σ : Arity S} (R : L.Relations σ) (x : M [^] σ) :
    RelMap R (Interpret.mkQuot r x) ↔ RelMap R x := by
  simp only [RelMap, Interpret.quotChoice_mkQuot]
  rfl

variable (L r) in
/-- The quotient map, as a homomorphism of `L`-structures. -/
def Congruence.mkHom : M →[L] fun s => Quotient (r s) where
  toFun s := Quotient.mk (r s)
  map_fun' f x := (funMap_mkQuot f x).symm
  map_rel' R x h := (relMap_mkQuot R x).2 h

@[simp]
theorem Congruence.mkHom_apply (s : S) (a : M s) :
    Congruence.mkHom L r s a = Quotient.mk (r s) a := rfl

@[simp]
theorem Term.realize_mkQuot {Γ σ : Arity S} (t : L.Term Γ σ) (xs : M [^] Γ) :
    t.realize (Interpret.mkQuot r xs) = Interpret.mkQuot r (t.realize xs) :=
  HomClass.realize_term (Congruence.mkHom L r) xs t

end Language

end ManySorted
