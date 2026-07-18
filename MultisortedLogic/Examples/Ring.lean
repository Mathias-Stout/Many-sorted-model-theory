import MultisortedLogic.Examples.Group

namespace MSFirstOrder
namespace Language
open Signature BoundedFormula deBruijnVar


universe u v w z u' v' w' z'

/- ring axioms -/

inductive RingAxiom : Type _
  | add  (aa : ACommGroupAxiom)   -- additive commutative group
  | mul  (ma : MMonoidAxiom)      -- multiplicative monoid
  | leftDistrib
  | rightDistrib

variable {Sorts : Type z} (L : Language Sorts) (M : Fam.{w} Sorts) (s : Sorts)

namespace RingAxiom

@[simp]
def toSentence [RingL L s] :
    RingAxiom → L.Sentence
  | add aa => aa.toSentence L s
  | mul ma => ma.toSentence L s
  | leftDistrib =>
      ∀' s (∀' s (∀' s (
        (#2 *ₗ  (#1 +ₗ #0))
          =' ((#2 *ₗ  #1) +ₗ (#2 *ₗ  #0))
      )))
  | rightDistrib =>
      ∀' s (∀' s (∀' s (
        ((#2 +ₗ #1) *ₗ  #0)
          =' ((#2 *ₗ  #0) +ₗ (#1 *ₗ  #0))
      )))

@[simp]
def toProp (R : Type _)
    [Add R] [Mul R] [Neg R] [Zero R] [One R] :
    RingAxiom → Prop
  | add aa => aa.toProp R
  | mul ma => ma.toProp R
  | leftDistrib =>
      ∀ x y z : R, x * (y + z) = (x * y) + (x * z)
  | rightDistrib =>
      ∀ x y z : R, (x + y) * z = (x * z) + (y * z)

variable {L M s} [RingL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)]
    [CompatibleRingL L M s] (ax : RingAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  cases ax with
  | add aa =>
    rw [toProp, toSentence]
    exact aa.realize_toSentence_iff_toProp
  | mul ma =>
    rw [toProp, toSentence]
    exact ma.realize_toSentence_iff_toProp
  | _ => simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl

lemma models_ring_axioms (ax : RingAxiom) [Ring (M s)] [CompatibleRingL L M s] :
    M ⊨ ax.toSentence L s := by
  cases ax with
  | add aa => exact aa.models_acomm_group_axioms
  | mul ma => exact ma.models_monoid_axioms
  | leftDistrib =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact left_distrib
  | rightDistrib =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact right_distrib

end RingAxiom

inductive CommRingAxiom : Type _
  | ring (ra : RingAxiom)
  | mulComm

namespace CommRingAxiom

@[simp]
def toSentence [RingL L s] :
    CommRingAxiom → L.Sentence
  | .ring ra =>
      RingAxiom.toSentence (Sorts := Sorts) (L := L) s ra
  | .mulComm =>
      ∀' s (∀' s ((#1 *ₗ #0) =' (#0 *ₗ #1)))

@[simp]
def toProp (R : Type _)
    [Add R] [Mul R] [Neg R] [Zero R] [One R] :
    CommRingAxiom → Prop
  | .ring ra => RingAxiom.toProp R ra
  | .mulComm => ∀ (x y : R), (x * y = y * x)

variable {L} {M} {s} [RingL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)]
    [CompatibleRingL L M s] (ax : CommRingAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  match ax with
  | ring ra =>
    rw [toProp, toSentence]
    exact ra.realize_toSentence_iff_toProp
  | mulComm =>
    cases ax <;> simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll] <;> rfl

lemma models_commring_axioms (ax : CommRingAxiom) [CommRing (M s)] [CompatibleRingL L M s] :
    M ⊨ ax.toSentence L s := by
  cases ax with
  | ring ra => exact RingAxiom.models_ring_axioms ra
  | mulComm =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact mul_comm

end CommRingAxiom


/-- Axioms for an ordered ring on sort `s`:
    ring axioms + total order axioms + compatibility with + and *. -/
inductive ORingAxiom : Type _
  | ring    (ra : RingAxiom)
  | torder  (ta : TOrderAxiom)
  | addLeAddLeft
  | mulNonneg

namespace ORingAxiom

@[simp]
def toSentence [ORingL L s] : ORingAxiom → L.Sentence
  | ring ra =>
      RingAxiom.toSentence (Sorts := Sorts) (L := L) s ra
  | torder ta =>
      TOrderAxiom.toSentence (Sorts := Sorts) (L := L) s ta
  | addLeAddLeft =>
      ∀' s (∀' s (∀' s (
        (#2 ≤ₗ #1) ⟹
        (#2 +ₗ #0 ≤ₗ #1 +ₗ #0)
      )))
  | mulNonneg =>
      ∀' s (∀' s (
        (0 ≤ₗ #1) ⟹
        (0 ≤ₗ #0) ⟹
        (0 ≤ₗ (#1 *ₗ #0))
      ))

@[simp]
def toProp (R : Type _)
    [Add R] [Mul R] [Neg R] [Zero R] [One R] [LE R] :
    ORingAxiom → Prop
  | ring ra =>
      RingAxiom.toProp (R := R) ra
  | torder ta =>
      TOrderAxiom.toProp (O := R) ta
  | addLeAddLeft =>
      ∀ a b c : R, a ≤ b → a + c ≤ b + c
  | mulNonneg =>
      ∀ a b : R, (0 : R) ≤ a → (0 : R) ≤ b → (0 : R) ≤ (a * b)

variable {L} {M} {s} [ORingL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp
    [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)] [LE (M s)]
    [CompatibleORingL L M s] (ax : ORingAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  match ax with
  | ring ra =>
    rw [toProp, toSentence]
    exact ra.realize_toSentence_iff_toProp
  | torder ta =>
    rw [toProp, toSentence]
    exact ta.realize_toSentence_iff_toProp
  | addLeAddLeft => simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl
  | mulNonneg => simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll]; rfl


end ORingAxiom

end Language

end MSFirstOrder
