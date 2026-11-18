/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACF.Basic
public import MultisortedLogic.Algebra.ACF.QE
public import MultisortedLogic.Algebra.ACVF.FieldStep.Compactness
public import MultisortedLogic.Algebra.ACVF.FieldStep.ReflectData
public import MultisortedLogic.Algebra.ACVF.FieldStep.Routing
public import MultisortedLogic.Algebra.ACVF.QE
public import MultisortedLogic.Algebra.ACVF.RVLift.GammaPart
public import MultisortedLogic.Algebra.ACVF.RVLift.LiftStep
public import MultisortedLogic.Algebra.ACVF.RVLift.RVPart
public import MultisortedLogic.Algebra.ACVF.RVLift.Ramified
public import MultisortedLogic.Algebra.ACVF.RVLift.Residual
public import MultisortedLogic.Algebra.ACVF.RVLift.ResidueField
public import MultisortedLogic.Algebra.ACVF.RVLift.Routing
public import MultisortedLogic.Algebra.ACVF.Reduction
public import MultisortedLogic.Algebra.ACVF.Substructure.AdjoinElement
public import MultisortedLogic.Algebra.ACVF.Substructure.FieldLike
public import MultisortedLogic.Algebra.ACVF.Substructure.RingEmbeddingData
public import MultisortedLogic.Algebra.ACVF.Theory.Axioms
public import MultisortedLogic.Algebra.ACVF.Theory.Language
public import MultisortedLogic.Algebra.ACVF.Theory.Model
public import MultisortedLogic.Algebra.ACVF.Theory.Recovery
public import MultisortedLogic.Algebra.ACVF.Theory.Structure
public import MultisortedLogic.Algebra.ACVF.ValuedField.BallFilter
public import MultisortedLogic.Algebra.ACVF.ValuedField.BallTransfer
public import MultisortedLogic.Algebra.ACVF.ValuedField.Comap
public import MultisortedLogic.Algebra.ACVF.ValuedField.DominantTerm
public import MultisortedLogic.Algebra.ACVF.ValuedField.Extend
public import MultisortedLogic.Algebra.ACVF.ValuedField.ImmediateRoot
public import MultisortedLogic.Algebra.ACVF.ValuedField.Lift
public import MultisortedLogic.Algebra.ACVF.ValuedField.ResidualReflect
public import MultisortedLogic.Algebra.ACVF.ValuedField.Residue
public import MultisortedLogic.Algebra.ACVF.ValuedField.ResidueTransfer
public import MultisortedLogic.Algebra.ACVF.ValuedField.RootLift
public import MultisortedLogic.Algebra.Basic
public import MultisortedLogic.Algebra.DOAG.AffineTransfer
public import MultisortedLogic.Algebra.DOAG.Basic
public import MultisortedLogic.Algebra.DOAG.QE
public import MultisortedLogic.Algebra.EOGroupModel
public import MultisortedLogic.Algebra.Field
public import MultisortedLogic.Algebra.Group
public import MultisortedLogic.Algebra.GroupTerm
public import MultisortedLogic.Algebra.Order
public import MultisortedLogic.Algebra.Ring
public import MultisortedLogic.AlgebraicBackground.Field
public import MultisortedLogic.AlgebraicBackground.Order
public import MultisortedLogic.AlgebraicBackground.RV
public import MultisortedLogic.Basic
public import MultisortedLogic.Bundled
public import MultisortedLogic.Complexity
public import MultisortedLogic.CompleteTheories
public import MultisortedLogic.DeltaMaps
public import MultisortedLogic.ElementaryMaps
public import MultisortedLogic.ElementarySubstructures
public import MultisortedLogic.EmbeddingTest
public import MultisortedLogic.Encoding
public import MultisortedLogic.Henkin
public import MultisortedLogic.LanguageMap
public import MultisortedLogic.LowenheimSkolem
public import MultisortedLogic.Maps
public import MultisortedLogic.Syntax
public import MultisortedLogic.Semantics
public import MultisortedLogic.Separation
public import MultisortedLogic.Named
public import MultisortedLogic.Parameters
public import MultisortedLogic.PartialMaps
public import MultisortedLogic.QuantifierElimination
public import MultisortedLogic.Quotients
public import MultisortedLogic.RealizingTypes
public import MultisortedLogic.Satisfiability
public import MultisortedLogic.Skolem
public import MultisortedLogic.Substructures
public import MultisortedLogic.Ultraproducts

/-!
# Many-sorted first-order logic

The root of the library: it imports every module, so that `lake build` builds all of them.
-/
