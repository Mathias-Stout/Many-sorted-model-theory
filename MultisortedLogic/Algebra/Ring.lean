/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Algebra.Group
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Ring axioms

The language of rings on a sort `s`, and the axioms of rings, commutative rings and ordered rings
as sentences in a ring language.

## Main definitions

* `Language.ring s`: the language of rings on the sort `s`.
* `RingAxiom`, `CommRingAxiom`, `ORingAxiom`: the axioms, with `toSentence`, `toProp`,
  `realize_toSentence_iff_toProp` and `models_ax` as for the group axioms.
* `natCastT`, `intCastT`: the integers as closed terms of a ring language.
* `RingTheory L s`: the theory of rings, with `models_RingTheory`.

## References

This file was originally based on `Mathlib/ModelTheory/Algebra/Ring/Basic.lean`, by Chris Hughes.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

universe u v w z

variable {S : Type z} (L : Language.{u, v} S) {M : S → Type w} [L.Structure M] (s : S)

/-! ### The language of rings -/

/-- The function symbols of the language of rings on the sort `s`. -/
inductive ringFunc (s : S) : Arity S → S → Type
  | add : ringFunc s (⦃s⦄ ⨯ ⦃s⦄) s
  | mul : ringFunc s (⦃s⦄ ⨯ ⦃s⦄) s
  | neg : ringFunc s ⦃s⦄ s
  | zero : ringFunc s ⦃⦄ s
  | one : ringFunc s ⦃⦄ s

/-- The language of rings on the sort `s`: `+`, `*`, `-`, `0`, `1` and no relation symbols. -/
protected abbrev ring : Language.{0, 0} S where
  Functions := ringFunc s
  Relations _ := Empty

instance : RingL (Language.ring s) s where
  addFunc := .add
  mulFunc := .mul
  negFunc := .neg
  zeroConst := .zero
  oneConst := .one

/-! ### Ring axioms -/

/-- Axiom names for a (unital, not necessarily commutative) ring on sort `s`. -/
inductive RingAxiom : Type
  | add (ax : ACommGroupAxiom)
  | mul (ax : MMonoidAxiom)
  | leftDistrib
  | rightDistrib

namespace RingAxiom

/-- The sentence expressing a ring axiom. -/
@[simp]
def toSentence [RingL L s] : RingAxiom → L.Sentence
  | add ax => ax.toSentence L s
  | mul ax => ax.toSentence L s
  | leftDistrib => ∀' s (∀' s (∀' s (#2 *ₗ (#1 +ₗ #0) =' #2 *ₗ #1 +ₗ #2 *ₗ #0)))
  | rightDistrib => ∀' s (∀' s (∀' s ((#2 +ₗ #1) *ₗ #0 =' #2 *ₗ #0 +ₗ #1 *ₗ #0)))

/-- The mathematical content of a ring axiom. -/
@[simp]
def toProp (R : Type*) [Add R] [Mul R] [Neg R] [Zero R] [One R] : RingAxiom → Prop
  | add ax => ax.toProp R
  | mul ax => ax.toProp R
  | leftDistrib => ∀ x y z : R, x * (y + z) = x * y + x * z
  | rightDistrib => ∀ x y z : R, (x + y) * z = x * z + y * z

variable {L s} [RingL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)]
    [One (M s)] [CompatibleRingL L M s] (ax : RingAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact ACommGroupAxiom.realize_toSentence_iff_toProp _
  · exact MMonoidAxiom.realize_toSentence_iff_toProp _
  all_goals simp

theorem models_ax [Ring (M s)] [CompatibleRingL L M s] (ax : RingAxiom) :
    M ⊨ ax.toSentence L s := by
  cases ax
  · exact ACommGroupAxiom.models_ax _
  · exact MMonoidAxiom.models_ax _
  all_goals rw [realize_toSentence_iff_toProp]
  · exact left_distrib
  · exact right_distrib

end RingAxiom

/-- Axiom names for a commutative ring on sort `s`. -/
inductive CommRingAxiom : Type
  | ring (ax : RingAxiom)
  | mulComm

namespace CommRingAxiom

/-- The sentence expressing a commutative-ring axiom. -/
@[simp]
def toSentence [RingL L s] : CommRingAxiom → L.Sentence
  | ring ax => ax.toSentence L s
  | mulComm => ∀' s (∀' s (#1 *ₗ #0 =' #0 *ₗ #1))

/-- The mathematical content of a commutative-ring axiom. -/
@[simp]
def toProp (R : Type*) [Add R] [Mul R] [Neg R] [Zero R] [One R] : CommRingAxiom → Prop
  | ring ax => ax.toProp R
  | mulComm => ∀ x y : R, x * y = y * x

variable {L s} [RingL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)]
    [One (M s)] [CompatibleRingL L M s] (ax : CommRingAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact RingAxiom.realize_toSentence_iff_toProp _
  · simp

theorem models_ax [CommRing (M s)] [CompatibleRingL L M s] (ax : CommRingAxiom) :
    M ⊨ ax.toSentence L s := by
  cases ax
  · exact RingAxiom.models_ax _
  · rw [realize_toSentence_iff_toProp]
    exact mul_comm

end CommRingAxiom

/-- Axiom names for an ordered ring on sort `s`: a ring with a total order, in which addition is
monotone and products of nonnegative elements are nonnegative. -/
inductive ORingAxiom : Type
  | ring (ax : RingAxiom)
  | torder (ax : TOrderAxiom)
  | addLeAddRight
  | mulNonneg

namespace ORingAxiom

/-- The sentence expressing an ordered-ring axiom. -/
@[simp]
def toSentence [ORingL L s] : ORingAxiom → L.Sentence
  | ring ax => ax.toSentence L s
  | torder ax => ax.toSentence L s
  | addLeAddRight => ∀' s (∀' s (∀' s ((#2 ≤ₗ #1) ⟹ (#2 +ₗ #0 ≤ₗ #1 +ₗ #0))))
  | mulNonneg => ∀' s (∀' s ((0 ≤ₗ #1) ⟹ (0 ≤ₗ #0) ⟹ (0 ≤ₗ #1 *ₗ #0)))

/-- The mathematical content of an ordered-ring axiom. -/
@[simp]
def toProp (R : Type*) [Add R] [Mul R] [Neg R] [Zero R] [One R] [LE R] : ORingAxiom → Prop
  | ring ax => ax.toProp R
  | torder ax => ax.toProp R
  | addLeAddRight => ∀ a b c : R, a ≤ b → a + c ≤ b + c
  | mulNonneg => ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b

variable {L s} [ORingL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)]
    [One (M s)] [LE (M s)] [CompatibleORingL L M s] (ax : ORingAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact RingAxiom.realize_toSentence_iff_toProp _
  · exact TOrderAxiom.realize_toSentence_iff_toProp _
  all_goals simp

theorem models_ax [Ring (M s)] [LinearOrder (M s)] [IsOrderedRing (M s)]
    [CompatibleORingL L M s] (ax : ORingAxiom) : M ⊨ ax.toSentence L s := by
  cases ax
  · exact RingAxiom.models_ax _
  · exact TOrderAxiom.models_ax _
  all_goals rw [realize_toSentence_iff_toProp]
  · exact fun _ _ c h => add_le_add_left h c
  · exact fun _ _ => mul_nonneg

end ORingAxiom

/-! ### Integer constants as terms

Every integer is the value of a closed term in any ring language, built from `0`, `1`, `+` and
`-`. This is what lets an arbitrary `ℤ`-polynomial be realized by a term. -/

section IntCast

variable {L s} [RingL L s] {Γ : Arity S}

/-- The term `0 + 1 + ⋯ + 1` (`n` ones). -/
def natCastT : ℕ → L.Term Γ ⦃s⦄
  | 0 => 0
  | n + 1 => natCastT n +ₗ 1

/-- The term whose value is the image of `k : ℤ` in any ring. -/
def intCastT : ℤ → L.Term Γ ⦃s⦄
  | .ofNat n => natCastT n
  | .negSucc n => -ₗ natCastT (n + 1)

variable [Ring (M s)] [CompatibleRingL L M s]

@[simp]
theorem realize_natCastT (n : ℕ) (xs : M [^] Γ) :
    (natCastT (L := L) (s := s) n).realize xs = (n : M s) := by
  induction n with
  | zero => simp [natCastT]
  | succ n ih => simp [natCastT, ih]

@[simp]
theorem realize_intCastT (k : ℤ) (xs : M [^] Γ) :
    (intCastT (L := L) (s := s) k).realize xs = (k : M s) := by
  cases k with
  | ofNat n => simp [intCastT]
  | negSucc n => simp [intCastT, Int.negSucc_eq]

end IntCast

/-- The theory of rings on sort `s`. -/
def RingTheory [RingL L s] : L.Theory :=
  Set.range (RingAxiom.toSentence L s)

/-- A ring is a model of `RingTheory`. -/
theorem models_RingTheory [RingL L s] [Ring (M s)] [CompatibleRingL L M s] :
    M ⊨ RingTheory L s :=
  (Theory.model_iff _).2 <| by
    rintro _ ⟨ax, rfl⟩
    exact RingAxiom.models_ax ax

end ManySorted.Language
