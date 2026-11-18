/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Algebra.Order
public import Mathlib.Algebra.Order.AddGroupWithTop

/-!
# Group axioms

The axioms of additive and multiplicative monoids and groups on a sort `s`, and of ordered and
extended ordered abelian groups, as sentences in the operator languages of
`MultisortedLogic.Algebra.Basic`.

## Main definitions

* `AMonoidAxiom`, `AGroupAxiom`, `ACommGroupAxiom`: additive monoids, groups and abelian groups.
* `MMonoidAxiom`, `MGroupAxiom`: multiplicative monoids and groups.
* `OCommGroupAxiom`: linearly ordered abelian groups.
* `EOCommGroupAxiom`: linearly ordered abelian groups with a top element `∞`, modeled on
  `LinearOrderedAddCommGroupWithTop`.
* `AGroupTheory L s`: the theory of additive groups, with `models_AGroupTheory`.

For each family of axioms, `toSentence` is the axiom as a sentence and `toProp` its content as a
proposition about a type; they correspond by `realize_toSentence_iff_toProp`, and `models_ax` says
that the corresponding Mathlib structure satisfies them.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

universe u v w z

variable {S : Type z} (L : Language.{u, v} S) {M : S → Type w} [L.Structure M] (s : S)

/-! ### Additive axioms -/

/-- Axiom names for an additive monoid on sort `s`. -/
inductive AMonoidAxiom : Type
  | addAssoc
  | zeroAdd
  | addZero

namespace AMonoidAxiom

/-- The sentence expressing an additive-monoid axiom. -/
@[simp]
def toSentence [AddL L s] [ZeroL L s] : AMonoidAxiom → L.Sentence
  | addAssoc => ∀' s (∀' s (∀' s ((#2 +ₗ #1) +ₗ #0 =' #2 +ₗ (#1 +ₗ #0))))
  | zeroAdd => ∀' s (0 +ₗ #0 =' #0)
  | addZero => ∀' s (#0 +ₗ 0 =' #0)

/-- The mathematical content of an additive-monoid axiom. -/
@[simp]
def toProp (R : Type*) [Add R] [Zero R] : AMonoidAxiom → Prop
  | addAssoc => ∀ x y z : R, x + y + z = x + (y + z)
  | zeroAdd => ∀ x : R, 0 + x = x
  | addZero => ∀ x : R, x + 0 = x

variable {L s} [AMonoidL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Zero (M s)] [CompatibleAMonoidL L M s]
    (ax : AMonoidAxiom) : M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax <;> simp

theorem models_ax [AddMonoid (M s)] [CompatibleAMonoidL L M s] (ax : AMonoidAxiom) :
    M ⊨ ax.toSentence L s := by
  rw [realize_toSentence_iff_toProp]
  cases ax
  · exact add_assoc
  · exact zero_add
  · exact add_zero

end AMonoidAxiom

/-- Axiom names for an additive group on sort `s`. -/
inductive AGroupAxiom : Type
  | aMonoid (ax : AMonoidAxiom)
  | negAddCancel

namespace AGroupAxiom

/-- The sentence expressing an additive-group axiom. -/
@[simp]
def toSentence [AddL L s] [ZeroL L s] [NegL L s] : AGroupAxiom → L.Sentence
  | aMonoid ax => ax.toSentence L s
  | negAddCancel => ∀' s (-ₗ#0 +ₗ #0 =' 0)

/-- The mathematical content of an additive-group axiom. -/
@[simp]
def toProp (R : Type*) [Add R] [Neg R] [Zero R] : AGroupAxiom → Prop
  | aMonoid ax => ax.toProp R
  | negAddCancel => ∀ x : R, -x + x = 0

variable {L s} [AGroupL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Neg (M s)] [Zero (M s)]
    [CompatibleAGroupL L M s] (ax : AGroupAxiom) : M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact AMonoidAxiom.realize_toSentence_iff_toProp _
  · simp

theorem models_ax [AddGroup (M s)] [CompatibleAGroupL L M s] (ax : AGroupAxiom) :
    M ⊨ ax.toSentence L s := by
  cases ax
  · exact AMonoidAxiom.models_ax _
  · rw [realize_toSentence_iff_toProp]
    exact neg_add_cancel

end AGroupAxiom

/-- Axiom names for an additive commutative group on sort `s`. -/
inductive ACommGroupAxiom : Type
  | aGroup (ax : AGroupAxiom)
  | addComm

namespace ACommGroupAxiom

/-- The sentence expressing an additive-commutative-group axiom. -/
@[simp]
def toSentence [AddL L s] [ZeroL L s] [NegL L s] : ACommGroupAxiom → L.Sentence
  | aGroup ax => ax.toSentence L s
  | addComm => ∀' s (∀' s (#1 +ₗ #0 =' #0 +ₗ #1))

/-- The mathematical content of an additive-commutative-group axiom. -/
@[simp]
def toProp (R : Type*) [Add R] [Neg R] [Zero R] : ACommGroupAxiom → Prop
  | aGroup ax => ax.toProp R
  | addComm => ∀ x y : R, x + y = y + x

variable {L s} [AGroupL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Neg (M s)] [Zero (M s)]
    [CompatibleAGroupL L M s] (ax : ACommGroupAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact AGroupAxiom.realize_toSentence_iff_toProp _
  · simp

theorem models_ax [AddCommGroup (M s)] [CompatibleAGroupL L M s] (ax : ACommGroupAxiom) :
    M ⊨ ax.toSentence L s := by
  cases ax
  · exact AGroupAxiom.models_ax _
  · rw [realize_toSentence_iff_toProp]
    exact add_comm

end ACommGroupAxiom

/-! ### Multiplicative axioms -/

/-- Axiom names for a multiplicative monoid on sort `s`. -/
inductive MMonoidAxiom : Type
  | mulAssoc
  | oneMul
  | mulOne

namespace MMonoidAxiom

/-- The sentence expressing a multiplicative-monoid axiom. -/
@[simp]
def toSentence [MulL L s] [OneL L s] : MMonoidAxiom → L.Sentence
  | mulAssoc => ∀' s (∀' s (∀' s ((#2 *ₗ #1) *ₗ #0 =' #2 *ₗ (#1 *ₗ #0))))
  | oneMul => ∀' s (1 *ₗ #0 =' #0)
  | mulOne => ∀' s (#0 *ₗ 1 =' #0)

/-- The mathematical content of a multiplicative-monoid axiom. -/
@[simp]
def toProp (G : Type*) [Mul G] [One G] : MMonoidAxiom → Prop
  | mulAssoc => ∀ x y z : G, x * y * z = x * (y * z)
  | oneMul => ∀ x : G, 1 * x = x
  | mulOne => ∀ x : G, x * 1 = x

variable {L s} [MMonoidL L s]

theorem realize_toSentence_iff_toProp [Mul (M s)] [One (M s)] [CompatibleMMonoidL L M s]
    (ax : MMonoidAxiom) : M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax <;> simp

theorem models_ax [Monoid (M s)] [CompatibleMMonoidL L M s] (ax : MMonoidAxiom) :
    M ⊨ ax.toSentence L s := by
  rw [realize_toSentence_iff_toProp]
  cases ax
  · exact mul_assoc
  · exact one_mul
  · exact mul_one

end MMonoidAxiom

/-- Axiom names for a multiplicative group on sort `s`. -/
inductive MGroupAxiom : Type
  | monoid (ax : MMonoidAxiom)
  | mulLeftInv

namespace MGroupAxiom

/-- The sentence expressing a multiplicative-group axiom. -/
@[simp]
def toSentence [MulL L s] [OneL L s] : MGroupAxiom → L.Sentence
  | monoid ax => ax.toSentence L s
  | mulLeftInv => ∀' s (∃' s (#0 *ₗ #1 =' 1))

/-- The mathematical content of a multiplicative-group axiom. -/
@[simp]
def toProp (G : Type*) [Mul G] [One G] : MGroupAxiom → Prop
  | monoid ax => ax.toProp G
  | mulLeftInv => ∀ x : G, ∃ y : G, y * x = 1

variable {L s} [MMonoidL L s]

theorem realize_toSentence_iff_toProp [Mul (M s)] [One (M s)] [CompatibleMMonoidL L M s]
    (ax : MGroupAxiom) : M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact MMonoidAxiom.realize_toSentence_iff_toProp _
  · simp

theorem models_ax [Group (M s)] [CompatibleMMonoidL L M s] (ax : MGroupAxiom) :
    M ⊨ ax.toSentence L s := by
  cases ax
  · exact MMonoidAxiom.models_ax _
  · rw [realize_toSentence_iff_toProp]
    exact fun x => ⟨x⁻¹, inv_mul_cancel x⟩

end MGroupAxiom

/-! ### Ordered additive axioms -/

/-- Axiom names for an ordered additive commutative group on sort `s`. -/
inductive OCommGroupAxiom : Type
  | abelian (ax : ACommGroupAxiom)
  | torder (ax : TOrderAxiom)
  | addLeAddRight

namespace OCommGroupAxiom

/-- The sentence expressing an ordered-additive-commutative-group axiom. -/
@[simp]
def toSentence [OAGroupL L s] : OCommGroupAxiom → L.Sentence
  | abelian ax => ax.toSentence L s
  | torder ax => ax.toSentence L s
  | addLeAddRight => ∀' s (∀' s (∀' s ((#2 ≤ₗ #1) ⟹ (#2 +ₗ #0 ≤ₗ #1 +ₗ #0))))

/-- The mathematical content of an ordered-additive-commutative-group axiom. -/
@[simp]
def toProp (R : Type*) [Add R] [Neg R] [Zero R] [LE R] : OCommGroupAxiom → Prop
  | abelian ax => ax.toProp R
  | torder ax => ax.toProp R
  | addLeAddRight => ∀ a b c : R, a ≤ b → a + c ≤ b + c

variable {L s} [OAGroupL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Neg (M s)] [Zero (M s)] [LE (M s)]
    [CompatibleOAGroupL L M s] (ax : OCommGroupAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  · exact ACommGroupAxiom.realize_toSentence_iff_toProp _
  · exact TOrderAxiom.realize_toSentence_iff_toProp _
  · simp

theorem models_ax [AddCommGroup (M s)] [LinearOrder (M s)] [IsOrderedAddMonoid (M s)]
    [CompatibleOAGroupL L M s] (ax : OCommGroupAxiom) : M ⊨ ax.toSentence L s := by
  cases ax
  · exact ACommGroupAxiom.models_ax _
  · exact TOrderAxiom.models_ax _
  · rw [realize_toSentence_iff_toProp]
    exact fun _ _ c h => add_le_add_left h c

end OCommGroupAxiom

/-- Axiom names for an extended ordered additive commutative group on sort `s`, modeled on
`LinearOrderedAddCommGroupWithTop`: the inverse law only holds away from `⊤`, and `⊤` is
absorbing. -/
inductive EOCommGroupAxiom : Type
  | addAssoc
  | zeroAdd
  | addZero
  | addComm
  | torder (ax : TOrderAxiom)
  | addLeAddRight
  | negAddCancelOfNeTop
  | leTop
  | topAdd
  | addTop
  | negTop

namespace EOCommGroupAxiom

/-- The sentence expressing an extended-ordered-additive-commutative-group axiom. -/
@[simp]
def toSentence [EOAGroupL L s] : EOCommGroupAxiom → L.Sentence
  | addAssoc => ∀' s (∀' s (∀' s ((#2 +ₗ #1) +ₗ #0 =' #2 +ₗ (#1 +ₗ #0))))
  | zeroAdd => ∀' s (0 +ₗ #0 =' #0)
  | addZero => ∀' s (#0 +ₗ 0 =' #0)
  | addComm => ∀' s (∀' s (#1 +ₗ #0 =' #0 +ₗ #1))
  | torder ax => ax.toSentence L s
  | addLeAddRight => ∀' s (∀' s (∀' s ((#2 ≤ₗ #1) ⟹ (#2 +ₗ #0 ≤ₗ #1 +ₗ #0))))
  | negAddCancelOfNeTop => ∀' s ((#0 =' `∞) ⊔ (-ₗ#0 +ₗ #0 =' 0))
  | leTop => ∀' s (#0 ≤ₗ `∞)
  | topAdd => ∀' s (`∞ +ₗ #0 =' `∞)
  | addTop => ∀' s (#0 +ₗ `∞ =' `∞)
  | negTop => -ₗ(`∞ : L.Term _ ⦃s⦄) =' `∞

/-- The mathematical content of an extended-ordered-additive-commutative-group axiom. -/
@[simp]
def toProp (R : Type*) [Add R] [Neg R] [Zero R] [LE R] [Top R] :
    EOCommGroupAxiom → Prop
  | addAssoc => ∀ x y z : R, x + y + z = x + (y + z)
  | zeroAdd => ∀ x : R, 0 + x = x
  | addZero => ∀ x : R, x + 0 = x
  | addComm => ∀ x y : R, x + y = y + x
  | torder ax => ax.toProp R
  | addLeAddRight => ∀ a b c : R, a ≤ b → a + c ≤ b + c
  | negAddCancelOfNeTop => ∀ x : R, x = ⊤ ∨ -x + x = 0
  | leTop => ∀ x : R, x ≤ ⊤
  | topAdd => ∀ x : R, ⊤ + x = ⊤
  | addTop => ∀ x : R, x + ⊤ = ⊤
  | negTop => -(⊤ : R) = ⊤

variable {L s} [EOAGroupL L s]

theorem realize_toSentence_iff_toProp [Add (M s)] [Neg (M s)] [Zero (M s)] [LE (M s)] [Top (M s)]
    [CompatibleOAGroupL L M s] [CompatibleTopL L M s] (ax : EOCommGroupAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax
  case torder ax => exact TOrderAxiom.realize_toSentence_iff_toProp ax
  all_goals simp

theorem models_ax [LinearOrderedAddCommGroupWithTop (M s)] [CompatibleOAGroupL L M s]
    [CompatibleTopL L M s] (ax : EOCommGroupAxiom) : M ⊨ ax.toSentence L s := by
  cases ax
  case torder ax => exact TOrderAxiom.models_ax ax
  all_goals rw [realize_toSentence_iff_toProp]
  · exact add_assoc
  · exact zero_add
  · exact add_zero
  · exact add_comm
  · exact fun _ _ c h => add_le_add_left h c
  · intro x
    by_cases hx : x = ⊤
    · exact .inl hx
    · rw [add_comm]
      exact .inr (LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hx)
  · exact fun _ => le_top
  · exact top_add
  · exact add_top
  · exact LinearOrderedAddCommGroupWithTop.neg_top

end EOCommGroupAxiom

/-- The theory of additive groups on sort `s`. -/
def AGroupTheory [AGroupL L s] : L.Theory :=
  Set.range (AGroupAxiom.toSentence L s)

/-- An additive group is a model of `AGroupTheory`. -/
theorem models_AGroupTheory [AGroupL L s] [AddGroup (M s)] [CompatibleAGroupL L M s] :
    M ⊨ AGroupTheory L s :=
  (Theory.model_iff _).2 <| by
    rintro _ ⟨ax, rfl⟩
    exact AGroupAxiom.models_ax ax

end ManySorted.Language
