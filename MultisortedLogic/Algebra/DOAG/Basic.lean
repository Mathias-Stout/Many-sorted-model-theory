/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathias Stout
-/
module

public import MultisortedLogic.Algebra.Group
public import MultisortedLogic.Algebra.GroupTerm
public import MultisortedLogic.AlgebraicBackground.Order

/-!
# The theory of divisible ordered abelian groups

The theory of nontrivial divisible ordered abelian groups on a sort `s` of a language with an
ordered abelian group language on `s`. Quantifier elimination for the one-sorted theory `DOAG` is
in `Algebra/DOAG/QE.lean`.

## Main results

* `DOAGTheory L s`, `models_DOAGTheory`: the theory of nontrivial divisible ordered abelian groups,
  of which every nontrivial divisible ordered abelian group is a model.
* `modelDOAGAddCommGroup`, `modelLinearOrder`, `model_nontrivial`, `model_nsmul_surjective`:
  conversely, a model of `DOAGTheory` is a nontrivial divisible ordered abelian group on `s`.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

universe u v w z

variable {S : Type z}

/-! ### The theory of nontrivial divisible ordered abelian groups -/

/-- The axioms of the theory of nontrivial divisible ordered abelian groups: the axioms of ordered
abelian groups, nontriviality and, for each `n`, divisibility by `n + 1`. -/
inductive DOAGAxiom : Type
  | oag (ax : OCommGroupAxiom)
  | nontrivial
  | divisible (n : ℕ)

namespace DOAGAxiom

variable (L : Language.{u, v} S) (s : S)

/-- The sentence expressing a DOAG axiom. -/
@[simp]
def toSentence [OAGroupL L s] : DOAGAxiom → L.Sentence
  | oag ax => ax.toSentence L s
  | nontrivial => ∃' s ∼(#0 =' 0)
  | divisible n => ∀' s (∃' s (nsmulT (n + 1) #0 =' #1))

/-- The mathematical content of a DOAG axiom. -/
@[simp]
def toProp (G : Type*) [Add G] [Neg G] [Zero G] [LE G] : DOAGAxiom → Prop
  | oag ax => ax.toProp G
  | nontrivial => ∃ x : G, x ≠ 0
  | divisible n => ∀ a : G, ∃ x : G, nsmulRec (n + 1) x = a

variable {L s} {M : S → Type w} [OAGroupL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Add (M s)] [Neg (M s)] [Zero (M s)] [LE (M s)]
    [CompatibleOAGroupL L M s] (ax : DOAGAxiom) : M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax with
  | oag ax => exact OCommGroupAxiom.realize_toSentence_iff_toProp ax
  | nontrivial => simp
  | divisible n => simp [realize_nsmulT_nsmulRec]

end DOAGAxiom

/-- The theory of nontrivial divisible ordered abelian groups on sort `s`. -/
def DOAGTheory (L : Language.{u, v} S) (s : S) [OAGroupL L s] : L.Theory :=
  Set.range (DOAGAxiom.toSentence L s)

/-- A nontrivial divisible ordered abelian group is a model of `DOAGTheory`. -/
theorem models_DOAGTheory {L : Language.{u, v} S} {M : S → Type w} {s : S} [OAGroupL L s]
    [L.Structure M] [AddCommGroup (M s)] [LinearOrder (M s)] [IsOrderedAddMonoid (M s)]
    [CompatibleOAGroupL L M s] [Nontrivial (M s)] [DivisibleBy (M s) ℕ] :
    M ⊨ DOAGTheory L s := by
  refine (Theory.model_iff _).2 ?_
  rintro φ ⟨ax, rfl⟩
  rw [DOAGAxiom.realize_toSentence_iff_toProp]
  cases ax with
  | oag ax =>
    exact (OCommGroupAxiom.realize_toSentence_iff_toProp (L := L) ax).1
      (OCommGroupAxiom.models_ax ax)
  | nontrivial => exact exists_ne 0
  | divisible n =>
    intro a
    refine ⟨DivisibleBy.div a (n + 1), ?_⟩
    rw [nsmulRec_eq_nsmul]
    exact DivisibleBy.div_cancel a (Nat.succ_ne_zero n)

/-! ### Models are nontrivial divisible ordered abelian groups -/

section ModelAlgebra

variable (L : Language.{u, v} S) (M : S → Type w) (s : S) [OAGroupL L s] [L.Structure M]
  [M ⊨ DOAGTheory L s]

/-- Any ordered-abelian-group axiom holds in a model of `DOAGTheory`, phrased with the operations
and the order read off from the structure. -/
theorem model_oag_toProp (ax : OCommGroupAxiom) :
    letI := modelAdd L M s
    letI := modelNeg L M s
    letI := modelZero L M s
    letI := modelLE L M s
    ax.toProp (M s) := by
  let := modelAdd L M s
  let := modelNeg L M s
  let := modelZero L M s
  let := modelLE L M s
  have := modelOAGroupCompatible L M s
  exact (OCommGroupAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem (T := DOAGTheory L s) (Set.mem_range_self (DOAGAxiom.oag ax)))

/-- The abelian group structure on sort `s` of a model of `DOAGTheory`. -/
@[reducible] noncomputable def modelDOAGAddCommGroup : AddCommGroup (M s) :=
  letI := modelAdd L M s
  letI := modelNeg L M s
  letI := modelZero L M s
  { add := (· + ·)
    add_assoc := model_oag_toProp L M s (.abelian (.aGroup (.aMonoid .addAssoc)))
    zero := 0
    zero_add := model_oag_toProp L M s (.abelian (.aGroup (.aMonoid .zeroAdd)))
    add_zero := model_oag_toProp L M s (.abelian (.aGroup (.aMonoid .addZero)))
    nsmul := nsmulRec
    neg := Neg.neg
    zsmul := zsmulRec
    neg_add_cancel := model_oag_toProp L M s (.abelian (.aGroup .negAddCancel))
    add_comm := model_oag_toProp L M s (.abelian .addComm) }

/-- The linear order on sort `s` of a model of `DOAGTheory`. -/
@[reducible] noncomputable def modelLinearOrder : LinearOrder (M s) :=
  letI := modelAdd L M s
  letI := modelNeg L M s
  letI := modelZero L M s
  letI := modelLE L M s
  { le := (· ≤ ·)
    le_refl := model_oag_toProp L M s (.torder (.porder .leRefl))
    le_trans := model_oag_toProp L M s (.torder (.porder .leTrans))
    le_antisymm := model_oag_toProp L M s (.torder (.porder .leAntisymm))
    le_total := model_oag_toProp L M s (.torder .leTotal)
    toDecidableLE := Classical.decRel _ }

/-- The order and the addition of a model of `DOAGTheory` are compatible. -/
theorem modelIsOrderedAddMonoid :
    letI := modelDOAGAddCommGroup L M s
    letI := modelLinearOrder L M s
    IsOrderedAddMonoid (M s) := by
  let := modelDOAGAddCommGroup L M s
  let := modelLinearOrder L M s
  exact { add_le_add_left := fun a b hab c => model_oag_toProp L M s .addLeAddRight a b c hab }

/-- The structure is compatible with the derived group structure and order. -/
theorem modelDOAGDerivedCompatible :
    letI := modelDOAGAddCommGroup L M s
    letI := modelLinearOrder L M s
    CompatibleOAGroupL L M s := by
  let := modelDOAGAddCommGroup L M s
  let := modelLinearOrder L M s
  exact { funMap_add := fun _ => rfl, funMap_neg := fun _ => rfl, funMap_zero := rfl,
          realize_orderF := fun _ => Iff.rfl }

include L in
/-- The sort `s` of a model of `DOAGTheory` is nontrivial. -/
theorem model_nontrivial : Nontrivial (M s) := by
  let := modelAdd L M s
  let := modelNeg L M s
  let := modelZero L M s
  let := modelLE L M s
  have := modelOAGroupCompatible L M s
  obtain ⟨e, he⟩ :=
    (DOAGAxiom.realize_toSentence_iff_toProp (L := L) (M := M) (s := s) .nontrivial).1
      (Theory.realize_sentence_of_mem (T := DOAGTheory L s)
        (Set.mem_range_self DOAGAxiom.nontrivial))
  exact nontrivial_of_ne e 0 he

/-- A model of `DOAGTheory` is divisible: multiplication by a nonzero natural number is surjective
on the sort `s`. -/
theorem model_nsmul_surjective :
    letI := modelDOAGAddCommGroup L M s
    ∀ n : ℕ, n ≠ 0 → Function.Surjective fun a : M s => n • a := by
  let := modelDOAGAddCommGroup L M s
  let := modelLinearOrder L M s
  have := modelDOAGDerivedCompatible L M s
  intro n hn a
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨x, hx⟩ :=
    (DOAGAxiom.realize_toSentence_iff_toProp (L := L) (M := M) (s := s) (.divisible m)).1
      (Theory.realize_sentence_of_mem (T := DOAGTheory L s)
        (Set.mem_range_self (DOAGAxiom.divisible m))) a
  refine ⟨x, ?_⟩
  change (m + 1) • x = a
  rw [← nsmulRec_eq_nsmul]
  exact hx

end ModelAlgebra

end ManySorted.Language
