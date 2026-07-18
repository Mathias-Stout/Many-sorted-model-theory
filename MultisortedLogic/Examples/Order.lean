import MultisortedLogic.Examples.Basic

namespace MSFirstOrder
namespace Language
open Signature BoundedFormula deBruijnVar
universe u v w z u' v' w' z'


variable {Sorts : Type z} (L : Language Sorts) (M : Fam.{w} Sorts) (s : Sorts)
example : L.Sentence := ∀' s (#0 =' #0)
/-- Axioms for a partial order on sort `s` in an `OrderL` language. -/
inductive POrderAxiom : Type _
  | leRefl
  | leTrans
  | leAntisymm

namespace POrderAxiom

@[simp]
def toSentence [OrderL L s] :
    POrderAxiom → L.Sentence
  | leRefl =>
      ∀' s (#0 ≤ₗ #0)
  | leTrans =>
      ∀' s (∀' s (∀' s ((#2 ≤ₗ #1) ⟹ (#1 ≤ₗ #0) ⟹ (#2 ≤ₗ #0))))
  | leAntisymm =>
      ∀' s (∀' s ((#1 ≤ₗ #0) ⟹ (#0 ≤ₗ #1) ⟹ (#1 =' #0)))

@[simp]
def toProp (O : Type _) [LE O] :
    POrderAxiom → Prop
  | leRefl =>
      ∀ x : O, x ≤ x
  | leTrans =>
      ∀ x y z : O, x ≤ y → y ≤ z → x ≤ z
  | leAntisymm =>
      ∀ x y : O, x ≤ y → y ≤ x → x = y

variable {L} {M} {s} [OrderL L s] [L.Structure M]


theorem realize_toSentence_iff_toProp [LE (M s)] [CompatibleOrderL L M s]
    (ax : POrderAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  cases ax <;> simp only [toSentence, toProp] <;>
  simp [Sentence.Realize, Formula.Realize, Quantifiable.mkAll] <;> rfl



lemma models_porder_axioms [PartialOrder (M s)] [CompatibleOrderL L M s] (ax : POrderAxiom) :
  M ⊨ ax.toSentence L s := by
  rw [realize_toSentence_iff_toProp]
  cases ax <;> rw [toProp]
  · exact le_refl
  · exact Preorder.le_trans
  · exact PartialOrder.le_antisymm

end POrderAxiom

/-- Axioms for a total (linear) order on sort `s` in an `OrderL` language. -/
inductive TOrderAxiom : Type _
  | porder (pa : POrderAxiom)
  | leTotal

namespace TOrderAxiom

@[simp]
def toSentence
    [OrderL L s] :
    TOrderAxiom → L.Sentence
  | .porder pa =>
      POrderAxiom.toSentence (Sorts := Sorts) (L := L) s pa
  | .leTotal =>
      ∀' s (∀' s ((#1 ≤ₗ #0) ⊔ (#0 ≤ₗ #1)))

@[simp]
def toProp (O : Type _) [LE O] :
    TOrderAxiom → Prop
  | .porder pa =>
      POrderAxiom.toProp (O := O) pa
  | .leTotal =>
      ∀ x y : O, x ≤ y ∨ y ≤ x

variable {L} {M} {s} [OrderL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [LE (M s)] [CompatibleOrderL L M s]
    (ax : TOrderAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  match ax with
  | porder ax' =>
    rw [TOrderAxiom.toSentence]
    apply POrderAxiom.realize_toSentence_iff_toProp
  | leTotal =>
    simp [TOrderAxiom.toSentence, TOrderAxiom.toProp, Sentence.Realize, Formula.Realize,
        Quantifiable.mkAll, BoundedFormula.Realize]
    rfl


lemma models_torder_axioms [LinearOrder (M s)] [CompatibleOrderL L M s] (ax : TOrderAxiom) :
  M ⊨ ax.toSentence L s := by
  cases ax with
  | porder pa =>
      rw [toSentence]
      exact POrderAxiom.models_porder_axioms pa
  | leTotal =>
      rw [realize_toSentence_iff_toProp]
      simp [le_total]

end TOrderAxiom

end Language

end MSFirstOrder
