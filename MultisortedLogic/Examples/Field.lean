import MultisortedLogic.Examples.Ring

namespace MSFirstOrder
namespace Language
open Signature BoundedFormula deBruijnVar

universe u v w z u' v' w' z'

/- field axioms -/

inductive FieldAxiom : Type _
  | cring (ca : CommRingAxiom)
  | existsInv
  | existsPairNe

variable {Sorts : Type z} (L : Language Sorts) (M : Fam.{w} Sorts) (s : Sorts)

namespace FieldAxiom

@[simp]
def toSentence [RingL L s] :
    FieldAxiom → L.Sentence
  | .cring ca => ca.toSentence L s
  | .existsInv =>
      ∀' s (∼(#0 =' 0) ⟹ ∃' s ((#1*ₗ #0) =' 1))
  | .existsPairNe =>
      ∃' s (∃' s (∼(#1 =' #0)))

@[simp]
def toProp (K : Type _) [Add K] [Mul K] [Neg K] [Zero K] [One K] :
    FieldAxiom → Prop
  | .cring ca => ca.toProp K
  | .existsInv =>
      ∀ x : K, x ≠ 0 → ∃ y : K, x * y = 1
  | .existsPairNe =>
      ∃ x y : K, x ≠ y

variable {L M s} [RingL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)]
    [CompatibleRingL L M s] (ax : FieldAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  cases ax with
  | cring ca =>
    rw [toProp, toSentence]
    exact ca.realize_toSentence_iff_toProp
  | existsInv =>
    rw [toProp, toSentence]
    simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll, BoundedFormula.Quantifiable.mkEx]; rfl
  | existsPairNe =>
    rw [toProp, toSentence]
    simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll, BoundedFormula.Quantifiable.mkEx]; rfl

lemma models_field_axioms (ax : FieldAxiom) [Field (M s)] [CompatibleRingL L M s] :
    M ⊨ ax.toSentence L s := by
  cases ax with
  | cring ca => exact ca.models_commring_axioms
  | existsInv =>
    rw [realize_toSentence_iff_toProp, toProp]
    intro x hx
    exact ⟨x⁻¹, mul_inv_cancel₀ hx⟩
  | existsPairNe =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact ⟨0, 1, zero_ne_one⟩

end FieldAxiom

/-- Axioms for an ordered field on sort `s`:
    field axioms + total order axioms + compatibility with + and *. -/
inductive OFieldAxiom : Type _
  | field   (fa : FieldAxiom)
  | torder  (ta : TOrderAxiom)
  | addLeAddLeft
  | mulNonneg

namespace OFieldAxiom

@[simp]
def toSentence [ORingL L s] : OFieldAxiom → L.Sentence
  | field fa =>
      FieldAxiom.toSentence (Sorts := Sorts) L s fa
  | torder ta =>
      TOrderAxiom.toSentence (Sorts := Sorts) L s ta
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
def toProp (K : Type _)
    [Add K] [Mul K] [Neg K] [Zero K] [One K] [LE K] :
    OFieldAxiom → Prop
  | field fa => FieldAxiom.toProp K fa
  | torder ta => TOrderAxiom.toProp (O := K) ta
  | addLeAddLeft =>
      ∀ a b c : K, a ≤ b → a + c ≤ b + c
  | mulNonneg =>
      ∀ a b : K, (0 : K) ≤ a → (0 : K) ≤ b → (0 : K) ≤ (a * b)

variable {L} {M} {s} [ORingL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp
    [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)] [LE (M s)]
    [CompatibleORingL L M s] (ax : OFieldAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  match ax with
  | field fa =>
    rw [toProp, toSentence]
    exact fa.realize_toSentence_iff_toProp
  | torder ta =>
    rw [toProp, toSentence]
    exact ta.realize_toSentence_iff_toProp
  | addLeAddLeft => simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll, BoundedFormula.Quantifiable.mkEx]; rfl
  | mulNonneg => simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll, BoundedFormula.Quantifiable.mkEx]; rfl

lemma models_ofield_axioms
    [Field (M s)] [LinearOrder (M s)] [IsStrictOrderedRing (M s)]
    [CompatibleORingL L M s] (ax : OFieldAxiom) : M ⊨ ax.toSentence L s := by
  cases ax with
  | field fa => exact fa.models_field_axioms
  | torder ta => exact ta.models_torder_axioms
  | addLeAddLeft =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact fun _ _ _ h => add_le_add_left h _
  | mulNonneg =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact fun _ _ ha hb => mul_nonneg ha hb

end OFieldAxiom

section theories

variable {Sorts : Type z} (L : Language Sorts) (s : Sorts)

/-- The (additive) group theory on sort `s`: all `AGroupAxiom` sentences. -/
def AGroupTheory [AGroupL L s] : Set L.Sentence :=
  Set.range (AGroupAxiom.toSentence L s)

/-- The ring theory on sort `s`: all `RingAxiom` sentences. -/
def RingTheory [RingL L s] : Set L.Sentence :=
  Set.range (RingAxiom.toSentence L s)

/-- The field theory on sort `s`: all `FieldAxiom` sentences. -/
def FieldTheory [RingL L s] : Set L.Sentence :=
  Set.range (FieldAxiom.toSentence L s)

end theories

end Language
end MSFirstOrder
