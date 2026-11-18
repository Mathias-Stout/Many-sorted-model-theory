/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathias Stout
-/
module

public import MultisortedLogic.Algebra.Group

/-!
# Models of the extended ordered abelian group axioms

`Algebra/Group.lean` gives the axioms `EOCommGroupAxiom` of a linearly ordered abelian group
with an absorbing top element `∞`, and shows that a `LinearOrderedAddCommGroupWithTop` satisfies
them. This file is the converse half: a model of those axioms *is* a
`LinearOrderedAddCommGroupWithTop` on the sort in question, with the operations read off from
the interpretation of the language. It follows the pattern of the model algebra in
`Algebra/ACF/Basic.lean` and `Algebra/DOAG/Basic.lean`, for the value-group sort.

The one thing the axioms do not give is `Nontrivial`: a one-point group, where `∞ = 0`,
satisfies all of them. Nontriviality is therefore a hypothesis here, and in the intended
application it comes from the ambient theory — for `ACVF` it is nontriviality of the valuation.

## Main definitions

* `Language.EOCommGroupTheory` : the axioms, as a theory.
* `Language.EOCommGroupModel.modelLinearOrderedAddCommGroupWithTop` : a model of them carries a
  linearly ordered abelian group with top on sort `s`.
* `Language.EOCommGroupModel.modelDerivedCompatible` : the language structure is compatible with
  the derived Mathlib structures, so that realization can be computed with them.
-/

@[expose] public section

namespace ManySorted.Language

universe u v w z

variable {S : Type z} (L : Language.{u, v} S) (M : S → Type w) (s : S)

/-- The theory of a linearly ordered abelian group with an absorbing `∞`, on sort `s`. -/
def EOCommGroupTheory [EOAGroupL L s] : L.Theory := Set.range (EOCommGroupAxiom.toSentence L s)

namespace EOCommGroupModel

variable [EOAGroupL L s] [L.Structure M] [M ⊨ EOCommGroupTheory L s]

/-- Every axiom holds in a model, phrased with the operations read off from the structure. -/
theorem model_toProp (ax : EOCommGroupAxiom) :
    letI := modelAdd L M s
    letI := modelNeg L M s
    letI := modelZero L M s
    letI := modelTop L M s
    letI := modelLE L M s
    ax.toProp (M s) := by
  let := modelAdd L M s
  let := modelNeg L M s
  let := modelZero L M s
  let := modelTop L M s
  let := modelLE L M s
  have := modelOAGroupCompatible L M s
  have := modelTopCompatible L M s
  exact (EOCommGroupAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem (T := EOCommGroupTheory L s) (Set.mem_range_self ax))

/-- The additive commutative monoid structure on sort `s` of a model. -/
@[reducible] noncomputable def modelAddCommMonoid : AddCommMonoid (M s) :=
  letI := modelAdd L M s
  letI := modelZero L M s
  { add := (· + ·)
    add_assoc := model_toProp L M s .addAssoc
    zero := 0
    zero_add := model_toProp L M s .zeroAdd
    add_zero := model_toProp L M s .addZero
    nsmul := nsmulRec
    add_comm := model_toProp L M s .addComm }

/-- The linear order on sort `s` of a model. -/
@[reducible] noncomputable def modelLinearOrder : LinearOrder (M s) :=
  letI := modelLE L M s
  { le := (· ≤ ·)
    le_refl := model_toProp L M s (.torder (.porder .leRefl))
    le_trans := model_toProp L M s (.torder (.porder .leTrans))
    le_antisymm := model_toProp L M s (.torder (.porder .leAntisymm))
    le_total := model_toProp L M s (.torder .leTotal)
    toDecidableLE := Classical.decRel _ }

/-- **A model of the axioms is a linearly ordered abelian group with top**, provided the sort
has more than one element. The proviso is necessary: the one-point group, in which `∞ = 0`,
satisfies every axiom. -/
@[reducible] noncomputable def modelLinearOrderedAddCommGroupWithTop
    (hnt : letI := modelZero L M s; letI := modelTop L M s; (⊤ : M s) ≠ 0) :
    LinearOrderedAddCommGroupWithTop (M s) :=
  letI := modelAddCommMonoid L M s
  letI := modelLinearOrder L M s
  letI := modelNeg L M s
  letI := modelTop L M s
  { toAddCommMonoid := modelAddCommMonoid L M s
    toLinearOrder := modelLinearOrder L M s
    add_le_add_left := fun a b hab c => model_toProp L M s .addLeAddRight a b c hab
    top := ⊤
    le_top := model_toProp L M s .leTop
    neg := Neg.neg
    sub := fun a b => a + -b
    sub_eq_add_neg := fun _ _ => rfl
    zsmul := zsmulRec
    exists_pair_ne := ⟨⊤, 0, hnt⟩
    top_add' := model_toProp L M s .topAdd
    neg_top := model_toProp L M s .negTop
    add_neg_cancel_of_ne_top := fun x hx => by
      have h := (model_toProp L M s .negAddCancelOfNeTop x).resolve_left hx
      rw [add_comm]
      exact h }

/-- The language structure is compatible with the derived Mathlib structures. -/
theorem modelDerivedCompatible
    (hnt : letI := modelZero L M s; letI := modelTop L M s; (⊤ : M s) ≠ 0) :
    letI := modelLinearOrderedAddCommGroupWithTop L M s hnt
    CompatibleOAGroupL L M s := by
  let := modelLinearOrderedAddCommGroupWithTop L M s hnt
  exact { funMap_add := fun _ => rfl, funMap_neg := fun _ => rfl, funMap_zero := rfl,
          realize_orderF := fun _ => Iff.rfl }

/-- The language structure is compatible with the derived `⊤`. -/
theorem modelDerivedCompatibleTop
    (hnt : letI := modelZero L M s; letI := modelTop L M s; (⊤ : M s) ≠ 0) :
    letI := modelLinearOrderedAddCommGroupWithTop L M s hnt
    CompatibleTopL L M s := by
  let := modelLinearOrderedAddCommGroupWithTop L M s hnt
  exact { funMap_infty := rfl }

end EOCommGroupModel

end ManySorted.Language
