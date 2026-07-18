import MultisortedLogic.Examples.Basic
import MultisortedLogic.Examples.Order

namespace MSFirstOrder
namespace Language
open Signature BoundedFormula deBruijnVar

universe u v w z u' v' w' z'

variable {Sorts : Type z} (L : Language Sorts) (M : Fam.{w} Sorts) (s : Sorts)

/- additive monoid axioms -/

inductive AMonoidAxiom : Type _
  | addAssoc
  | zeroAdd
  | addZero

namespace AMonoidAxiom

@[simp]
def toSentence [AddL L s] [ZeroL L s] : AMonoidAxiom → L.Sentence
  | addAssoc =>
      ∀' s (∀' s (∀' s (((#2 +ₗ #1) +ₗ #0) =' (#2 +ₗ (#1 +ₗ #0)))))
  | zeroAdd =>
      ∀' s ((0 +ₗ #0) =' (#0))
  | addZero =>
      ∀' s ((#0 +ₗ 0) =' (#0))

@[simp]
def toProp (R : Type _) [Add R] [Zero R] : AMonoidAxiom → Prop
  | addAssoc =>
      ∀ x y z : R, (x + y) + z = x + (y + z)
  | zeroAdd =>
      ∀ x : R, (0 : R) + x = x
  | addZero =>
      ∀ x : R, x + (0 : R) = x

variable {L} {M} {s} [AMonoidL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Add (M s)] [Zero (M s)] [CompatibleAMonoidL L M s]
    (ax : AMonoidAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  cases ax <;> simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll] <;> rfl

theorem models_ax [AddMonoid (M s)] [CompatibleAMonoidL L M s]
    (ax : AMonoidAxiom) : M ⊨ ax.toSentence L s := by
  rw [realize_toSentence_iff_toProp]
  cases ax <;> rw [toProp]
  · exact add_assoc
  · exact zero_add
  · exact add_zero

end AMonoidAxiom

/- additive group axioms -/
inductive AGroupAxiom : Type _
  | aMonoid (am : AMonoidAxiom)
  | addLeftInv

namespace AGroupAxiom

@[simp]
def toSentence [AddL L s] [ZeroL L s] [NegL L s] : AGroupAxiom → L.Sentence
  | aMonoid ax => ax.toSentence L s
  | addLeftInv =>
      ∀' s (
        (( NegL.negT #0 +ₗ #0)
          =' 0)
          )

@[simp]
def toProp (R : Type _) [Add R] [Neg R] [Zero R] : AGroupAxiom → Prop
  | aMonoid ax => ax.toProp R
  | addLeftInv =>
      ∀ x : R, (-x) + x = (0 : R)

variable {L} {M} {s} [AGroupL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp
    (ax : AGroupAxiom) [Add (M s)] [Neg (M s)] [Zero (M s)] [CompatibleAGroupL L M s] :
    (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  match ax with
  | aMonoid ax' =>
    rw [toSentence]
    apply AMonoidAxiom.realize_toSentence_iff_toProp
  | addLeftInv => simp [Sentence.Realize, Formula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl

lemma models_agroup_axioms [AddGroup (M s)] [CompatibleAGroupL L M s]
    (ax : AGroupAxiom) : M ⊨ ax.toSentence L s := by
  match ax with
  | aMonoid am => exact am.models_ax
  | addLeftInv =>
    rw [realize_toSentence_iff_toProp]
    exact neg_add_cancel

end AGroupAxiom

/-
additive abelian group axioms
-/
inductive ACommGroupAxiom : Type _
  | agroup (ga : AGroupAxiom)
  | addComm

namespace ACommGroupAxiom

@[simp]
def toSentence [AddL L s] [ZeroL L s] [NegL L s] :
    ACommGroupAxiom → L.Sentence
  | .agroup ga =>
      AGroupAxiom.toSentence (Sorts := Sorts) (L := L) s ga
  | .addComm =>
      ∀' s (∀' s ((#1 +ₗ #0) =' (#0 +ₗ #1)))

@[simp]
def toProp (R : Type _) [Add R] [Neg R] [Zero R] :
    ACommGroupAxiom → Prop
  | .agroup ga =>
      AGroupAxiom.toProp R ga
  | .addComm =>
      ∀ x y : R, x + y = y + x

variable {L} {M} {s} [AGroupL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Add (M s)] [Zero (M s)] [Neg (M s)] [CompatibleAGroupL L M s]
    (ax : ACommGroupAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  match ax with
  | agroup ax' =>
    rw [ACommGroupAxiom.toSentence]
    apply AGroupAxiom.realize_toSentence_iff_toProp
  | addComm =>
    cases ax <;> simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll] <;> rfl

variable [AddCommGroup (M s)] [CompatibleAGroupL L M s]

lemma models_acomm_group_axioms (ax : ACommGroupAxiom) :
  M ⊨ ax.toSentence L s := by
  cases ax with
  | agroup ga =>
      exact ga.models_agroup_axioms
  | addComm =>
      rw [realize_toSentence_iff_toProp]
      exact add_comm

end ACommGroupAxiom

inductive MMonoidAxiom : Type _
  | mulAssoc
  | oneMul
  | mulOne

namespace MMonoidAxiom

@[simp]
def toSentence [MulL L s] [OneL L s] :
    MMonoidAxiom → L.Sentence
  | mulAssoc =>
      ∀' s (∀' s (∀' s (((#2 *ₗ  #1) *ₗ  #0) =' (#2 *ₗ  (#1 *ₗ  #0)))))
  | oneMul =>
      ∀' s ((1 *ₗ  #0) =' (#0))
  | mulOne =>
      ∀' s ((#0 *ₗ  1) =' (#0))

@[simp]
def toProp (G : Type _)
    [Mul G] [One G] :
    MMonoidAxiom → Prop
  | mulAssoc =>
      ∀ x y z : G, (x * y) * z = x * (y * z)
  | oneMul =>
      ∀ x : G, 1 * x = x
  | mulOne =>
      ∀ x : G, x * 1 = x

variable {L} {M} {s} [MMonoidL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Mul (M s)] [One (M s)] [CompatibleMMonoidL L M s]
    (ax : MMonoidAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  cases ax <;> simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll] <;> rfl

variable [Monoid (M s)] [CompatibleMMonoidL L M s]

lemma models_monoid_axioms (ax : MMonoidAxiom) :
  M ⊨ ax.toSentence L s := by
  rw [realize_toSentence_iff_toProp]
  cases ax <;> rw [toProp]
  · exact mul_assoc
  · exact one_mul
  · exact mul_one

end MMonoidAxiom

inductive MGroupAxiom : Type _
  | monoid (ma : MMonoidAxiom)
  | mulLeftInv

namespace MGroupAxiom

@[simp]
def toSentence [MulL L s] [OneL L s] : MGroupAxiom → L.Sentence
  | monoid ma => ma.toSentence L s
  | mulLeftInv =>
      ∀' s ( ∃' s (
        ( #0 *ₗ  #1) =' 1
      ))

@[simp]
def toProp (G : Type _) [Mul G] [One G] :
    MGroupAxiom → Prop
  | monoid ma => MMonoidAxiom.toProp ma (G:= G)
  | mulLeftInv =>
      ∀ x : G, ∃ y : G, y * x = 1

variable {L} {M} {s} [MGroupL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Mul (M s)] [One (M s)] [CompatibleMMonoidL L M s]
    (ax : MGroupAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  match ax with
  | monoid ax' =>
    rw [MGroupAxiom.toSentence]
    apply MMonoidAxiom.realize_toSentence_iff_toProp
  | mulLeftInv =>
    cases ax <;> simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll, BoundedFormula.Quantifiable.mkEx] <;> rfl

lemma models_mgroup_axioms [Group (M s)] [CompatibleMMonoidL L M s] (ax : MGroupAxiom) :
  M ⊨ ax.toSentence L s := by
  cases ax with
  | monoid ma =>
      exact MMonoidAxiom.models_monoid_axioms ma
  | mulLeftInv =>
      rw [realize_toSentence_iff_toProp, toProp]
      exact fun x ↦ MulAction.exists_smul_eq (M s) x 1

end MGroupAxiom

/-- Axioms for an ordered additive abelian group on sort `s`:
    additive abelian group axioms + total order axioms + compatibility with addition. -/
inductive OCommGroupAxiom : Type _
  | abelian (aa : ACommGroupAxiom)
  | torder  (ta : TOrderAxiom)
  | addLeAddLeft

namespace OCommGroupAxiom

@[simp]
def toSentence [AddL L s] [ZeroL L s] [NegL L s] [OrderL L s] : OCommGroupAxiom → L.Sentence
  | .abelian aa =>
      ACommGroupAxiom.toSentence (Sorts := Sorts) (L := L) s aa
  | .torder ta =>
      TOrderAxiom.toSentence (Sorts := Sorts) (L := L) s ta
  | .addLeAddLeft =>
      ∀' s (∀' s (∀' s (
        (#2 ≤ₗ #1) ⟹
        (#2 +ₗ #0 ≤ₗ #1 +ₗ #0)
      )))

@[simp]
def toProp (R : Type _)
    [Add R] [Neg R] [Zero R] [LE R] :
    OCommGroupAxiom → Prop
  | .abelian aa =>
      ACommGroupAxiom.toProp (R := R) aa
  | .torder ta =>
      TOrderAxiom.toProp (O := R) ta
  | .addLeAddLeft =>
      ∀ a b c : R, a ≤ b → a + c ≤ b + c

variable {L} {M} {s} [OAGroupL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp
    [Add (M s)] [Zero (M s)] [Neg (M s)] [LE (M s)]
    [CompatibleOAGroupL L M s]
    (ax : OCommGroupAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  match ax with
  | abelian ax' =>
    rw [toSentence, toProp]
    apply ax'.realize_toSentence_iff_toProp
  | torder ax' =>
    rw [OCommGroupAxiom.toSentence]
    apply TOrderAxiom.realize_toSentence_iff_toProp
  | addLeAddLeft =>
    cases ax <;> simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll] <;> rfl

lemma models_oagroup_axioms
    [AddCommGroup (M s)] [LinearOrder (M s)] [IsOrderedAddMonoid (M s)]
    [CompatibleOAGroupL L M s] (ax : OCommGroupAxiom) : M ⊨ ax.toSentence L s := by
  cases ax with
  | abelian aa =>
      exact aa.models_acomm_group_axioms
  | torder ta =>
      exact ta.models_torder_axioms
  | addLeAddLeft =>
      rw [realize_toSentence_iff_toProp, toProp]
      exact fun _ _ _ h => add_le_add_left h _

end OCommGroupAxiom

/-- Axioms for an extended ordered additive abelian group on sort `s`:
    This is designed for structures like `LinearOrderedAddCommGroupWithTop` where:
    - The monoid and commutativity axioms hold
    - The order axioms hold
    - The inverse axiom only holds for non-top elements: `x ≠ ⊤ → (-x) + x = 0`
    - `⊤` is absorbing: `⊤ + x = x + ⊤ = ⊤` and `-⊤ = ⊤` -/
inductive EOCommGroupAxiom : Type _
  -- Monoid axioms
  | addAssoc
  | zeroAdd
  | addZero
  -- Commutativity
  | addComm
  -- Total order axioms
  | torder (ta : TOrderAxiom)
  -- Order-addition compatibility
  | addLeAddLeft
  -- Modified inverse axiom: only for non-infinity elements
  | addLeftInvNonTop  -- x = ⊤ ∨ (-x) + x = 0
  -- Infinity axioms
  | leInfty           -- x ≤ ⊤
  | inftyAdd          -- ⊤ + x = ⊤
  | addInfty          -- x + ⊤ = ⊤
  | negInfty          -- -⊤ = ⊤


namespace EOCommGroupAxiom

@[simp]
def toSentence [EOAGroupL L s] :
    EOCommGroupAxiom → L.Sentence
  | .addAssoc =>
      ∀' s (∀' s (∀' s (((#2 +ₗ #1) +ₗ #0) =' (#2 +ₗ (#1 +ₗ #0)))))
  | .zeroAdd =>
      ∀' s ((0 +ₗ #0) =' #0)
  | .addZero =>
      ∀' s ((#0 +ₗ 0) =' #0)
  | .addComm =>
      ∀' s (∀' s ((#1 +ₗ #0) =' (#0 +ₗ #1)))
  | .torder ta =>
      TOrderAxiom.toSentence (Sorts := Sorts) (L := L) s ta
  | .addLeAddLeft =>
      ∀' s (∀' s (∀' s (
        (#2 ≤ₗ #1) ⟹ (#2 +ₗ #0 ≤ₗ #1 +ₗ #0)
      )))
  | .addLeftInvNonTop =>
      -- ∀ x, x = ⊤ ∨ (-x) + x = 0
      ∀' s ((#0 =' `∞) ⊔ ((-ₗ#0 +ₗ #0) =' 0))
  | .leInfty =>
      ∀' s (#0 ≤ₗ `∞)
  | .inftyAdd =>
      ∀' s ((`∞ +ₗ #0) =' `∞)
  | .addInfty =>
      ∀' s ((#0 +ₗ `∞) =' `∞)
  | .negInfty =>
      (-ₗ(`∞ : L.Term _ ⦃s⦄)) =' `∞

@[simp]
def toProp (R : Type _)
    [Add R] [Neg R] [Zero R] [LE R] [Top R] :
    EOCommGroupAxiom → Prop
  | .addAssoc =>
      ∀ x y z : R, (x + y) + z = x + (y + z)
  | .zeroAdd =>
      ∀ x : R, 0 + x = x
  | .addZero =>
      ∀ x : R, x + 0 = x
  | .addComm =>
      ∀ x y : R, x + y = y + x
  | .torder ta =>
      TOrderAxiom.toProp (O := R) ta
  | .addLeAddLeft =>
      ∀ a b c : R, a ≤ b → a + c ≤ b + c
  | .addLeftInvNonTop =>
      ∀ x : R, x = ⊤ ∨ (-x) + x = 0
  | .leInfty =>
      ∀ x : R, x ≤ ⊤
  | .inftyAdd =>
      ∀ x : R, ⊤ + x = ⊤
  | .addInfty =>
      ∀ x : R, x + ⊤ = ⊤
  | .negInfty =>
      -(⊤ : R) = ⊤


variable {L} {M} {s} [EOAGroupL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Add (M s)] [Neg (M s)] [Zero (M s)] [LE (M s)] [Top (M s)]
    [CompatibleOAGroupL L M s] [CompatibleTopL L M s]
    (ax : EOCommGroupAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  match ax with
  | torder ta =>
    rw [EOCommGroupAxiom.toSentence]
    apply TOrderAxiom.realize_toSentence_iff_toProp
  | addAssoc => simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl
  | zeroAdd => simp [Sentence.Realize, Formula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl
  | addZero => simp [Sentence.Realize, Formula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl
  | addComm => simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl
  | addLeAddLeft => simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl
  | addLeftInvNonTop =>
    simp only [toSentence, toProp]
    simp only [Sentence.Realize, Formula.Realize]
    simp [BoundedFormula.Quantifiable.mkAll, or_iff_not_imp_left]
    rfl
  | leInfty => simp [Sentence.Realize, Formula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl
  | inftyAdd => simp [Sentence.Realize, Formula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl
  | addInfty => simp [Sentence.Realize, Formula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl
  | negInfty => simp [Sentence.Realize, Formula.Realize]

/-- A linearly ordered additive commutative group with top satisfies the extended ordered
    commutative group axioms. -/
lemma models_eocommgroup_axioms
    [LinearOrderedAddCommGroupWithTop (M s)]
    [CompatibleOAGroupL L M s] [CompatibleTopL L M s]
    (ax : EOCommGroupAxiom) : M ⊨ ax.toSentence L s := by
  cases ax with
  | addAssoc =>
    rw [realize_toSentence_iff_toProp]
    exact fun _ _ _ => add_assoc _ _ _
  | zeroAdd =>
    rw [realize_toSentence_iff_toProp]
    exact zero_add
  | addZero =>
    rw [realize_toSentence_iff_toProp]
    exact add_zero
  | addComm =>
    rw [realize_toSentence_iff_toProp]
    exact add_comm
  | torder ta =>
    exact ta.models_torder_axioms
  | addLeAddLeft =>
    rw [realize_toSentence_iff_toProp]
    exact fun _ _ _ h => add_le_add_left h _
  | addLeftInvNonTop =>
    rw [realize_toSentence_iff_toProp]
    intro x
    by_cases hx : x = ⊤
    · left; exact hx
    · right
      rw [add_comm]
      exact LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hx
  | leInfty =>
    rw [realize_toSentence_iff_toProp]
    exact fun _ => le_top
  | inftyAdd =>
    rw [realize_toSentence_iff_toProp]
    exact top_add
  | addInfty =>
    rw [realize_toSentence_iff_toProp]
    exact add_top
  | negInfty =>
    rw [realize_toSentence_iff_toProp]
    exact LinearOrderedAddCommGroupWithTop.neg_top

end EOCommGroupAxiom

end Language
end MSFirstOrder
