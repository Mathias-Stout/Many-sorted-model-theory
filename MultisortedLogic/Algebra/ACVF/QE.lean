/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.FieldStep.Routing
public import MultisortedLogic.Algebra.ACVF.RVLift.GammaPart

/-!
# Quantifier elimination for algebraically closed valued fields

The theory `ACVFTheory` of algebraically closed fields with a nontrivial valuation eliminates
quantifiers in the three-sorted leading-term language `L_RV`. Its sorts are `K` (the field), `RV`
(the leading terms `K^× / (1 + 𝔪) ∪ {0}`) and `Γ` (the value group with `∞`). The proof follows
Proposition 2.1.10 of Silvain Rideau-Kikuchi's lecture notes *Model theory of valued fields*.

## Main results

* `ACVF_hasQERelTo_empty` : `ACVFTheory` eliminates quantifiers in `L_RV`.

Two theorems say that `ACVFTheory` is the theory of the intended structures:

* `models_ACVFTheory` : an algebraically closed field with a nontrivial valuation, viewed as an
  `L_RV`-structure, is a model of `ACVFTheory`;
* `exists_valuationSubring_equiv` : every model of `ACVFTheory` is isomorphic to such a
  structure.

## Structure of the proof

The files of `Algebra/ACVF/` are arranged by the step of the proof they serve.

* `Theory/` : the language and the theory. `Language.lean` defines `L_RV`, `Structure.lean`
  makes a valued field into an `L_RV`-structure, and `Axioms.lean` defines `ACVFTheory` and proves
  `models_ACVFTheory`. `Model.lean` reads a valued field off an abstract model, and
  `Recovery.lean` proves that the model is the leading-term structure of that valued field. This
  gives `exists_valuationSubring_equiv`, and the dictionary that the rest of the proof uses to
  pass between the model and the valued field.
* `Reduction.lean` : the model theory. By the embedding test of `EmbeddingTest.lean`, quantifier
  elimination follows from two statements about extending embeddings of substructures
  (`ACVF_hasQERelTo_empty_of_lift_step`). These are `RVLift`, steps `res(K(C)) = k(C)` and
  `v(K(C)) = Γ(C)` of Proposition 2.1.10, and `FieldStep`, its step `K(C) = K(M)`.
* `Substructure/` : the shared setting of both steps. A *field-like* substructure is a subfield of
  the field sort together with its leading terms and their values, and an embedding of one is a
  ring homomorphism that reflects leading terms and the order of values (`FieldLike.lean`,
  `FieldEmbeddingData`). `RingEmbeddingData.lean` passes such data from a subring to its fraction
  field. `AdjoinElement.lean` extends it from `F` to `F(a)`, sending `a` to `b`, when polynomials
  over `F` have their values ordered alike at `a` and at `b` (`ReflectData`).
* `RVLift/` : `RVLift_holds`. By Zorn's lemma, the field part of a substructure grows until its
  leading terms exhaust the `RV`-part (`RVPart.lean`), and then until its values exhaust the
  `Γ`-part (`GammaPart.lean`). Each step of the first iteration adds one element, chosen in
  `Routing.lean`, in the ramified or residual case (`Ramified.lean`, `Residual.lean`, with the
  shared machinery in `LiftStep.lean` and `ResidueField.lean`). No elementary extension of the
  target is needed.
* `FieldStep/` : `fieldStep_of_valuePatternExt` and `valuePatternExt_holds`. Adjoining one
  element to a field-like embedding reduces to `ReflectData` (`ReflectData.lean`). Compactness
  then realizes `ReflectData` in an elementary extension of the target, from its finite fragments
  (`Compactness.lean`). `Routing.lean` produces those fragments in Rideau-Kikuchi's three cases:
  ramified, residual and immediate.
* `ValuedField/` : the algebra of valued fields behind both steps, with no model theory. It covers
  dominant terms (`DominantTerm.lean`), leading terms of units and residues (`Residue.lean`,
  `Lift.lean`, `RootLift.lean`) and extending an embedding along an element (`Extend.lean`,
  `Comap.lean`). It then treats the three cases: ramified (`Extend.lean`), residual
  (`ResidualReflect.lean`, `ResidueTransfer.lean`) and immediate (`BallFilter.lean`,
  `BallTransfer.lean`, `ImmediateRoot.lean`).

The leading-term structure of a valued field itself is defined in `AlgebraicBackground/RV.lean`.

## References

* Silvain Rideau-Kikuchi, *Model theory of valued fields*, lecture notes, version of
  September 17, 2024. <https://www.math.ens.psl.eu/~rideau/teaching/val/vf.pdf>
-/

@[expose] public section

namespace ManySorted.Language

/-- **Quantifier elimination for `ACVF`.** The theory of algebraically closed fields with a
nontrivial valuation eliminates quantifiers in the three-sorted leading-term language `L_RV`.

By `ACVF_hasQERelTo_empty_of_lift_step`, it is enough to prove the two extension statements
`RVLift` and `FieldStep`. -/
theorem ACVF_hasQERelTo_empty : ACVFTheory.HasQERelTo (∅ : Set RVSort) :=
  ACVF_hasQERelTo_empty_of_lift_step RVLift_holds
    (fieldStep_of_valuePatternExt valuePatternExt_holds)

end ManySorted.Language
