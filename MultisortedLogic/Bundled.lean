/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.ElementarySubstructures
public import MultisortedLogic.Satisfiability

/-!
# Bundled structures and models

## Main definitions

* `Language.StructureType L`: a family of carriers with an `L`-structure, Mathlib's
  `CategoryTheory.Bundled L.Structure`; `StructureType.equivSetoid` is isomorphism.
* `Theory.ModelType T`: a model of `T` with nonempty sorts.
* `Theory.ModelType.equivInduced`, `shrink`, `ulift`: a model transported along a family of
  equivalences, in particular to another universe.
* `Theory.ModelType.reduct`, `defaultExpansion`, `subtheoryModel`: models along maps of languages
  and inclusions of theories.
* `ElementarilyEquivalent.toModel`, `ElementarySubstructure.toModel`: structures elementarily
  equivalent to a model, bundled as models.

## Main results

* `Theory.realizationEquivModelType`: the realizations of a theory are its models in the universe of
  the language. So `T.IsSatisfiable` says that `T` has a model in that universe
  (`Theory.isSatisfiable_iff_nonempty_modelType`), as in Mathlib.

## Implementation notes

A bundled structure or model coerces to its family of carriers, so `M s` is the carrier of sort
`s`. The rest of the library states its results for unbundled structures, and quantifies over
realizations where Mathlib quantifies over `Theory.ModelType`.

## References

This file was originally based on `Mathlib/ModelTheory/Bundled.lean`, by Aaron Anderson.
-/

@[expose] public section

universe u v w w' z u' v'

namespace ManySorted.Language

open Arity Structure

variable {S : Type z} {L : Language.{u, v} S}

/-! ### Bundled structures -/

variable (L) in
/-- A bundled `L`-structure: a family of carriers with an `L`-structure. -/
structure StructureType where
  /-- The carriers. -/
  Carrier : S → Type w
  /-- The structure on the carriers. -/
  [struc : L.Structure Carrier]

namespace StructureType

attribute [coe] Carrier

attribute [instance] struc

instance : CoeFun L.StructureType fun _ => S → Type w :=
  ⟨Carrier⟩

variable (L) in
/-- Bundle a structure. -/
def of (M : S → Type w) [L.Structure M] : L.StructureType :=
  ⟨M⟩

@[simp]
theorem coe_of (M : S → Type w) [L.Structure M] : ⇑(of L M) = M :=
  rfl

variable (L) in
/-- Isomorphism of bundled structures. -/
instance equivSetoid : Setoid L.StructureType where
  r M N := Nonempty (M ≃[L] N)
  iseqv := ⟨fun M => ⟨Equiv.refl L M⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨f.comp e⟩⟩

end StructureType

section Induced

variable {M : S → Type w} {N : S → Type w'} [L.Structure M] (e : ∀ s, M s ≃ N s)

variable (L) in
/-- The `L`-structure on `N` transported from `M` along a family of equivalences, bundled. -/
def Equiv.bundledInduced : L.StructureType :=
  @StructureType.of _ L N (Equiv.inducedStructure L e)

/-- A family of equivalences, as an isomorphism onto the bundled transported structure. -/
def Equiv.bundledInducedEquiv : M ≃[L] Equiv.bundledInduced L e :=
  Equiv.inducedStructureEquiv e

end Induced

/-! ### Bundled models -/

namespace Theory

variable (T : L.Theory)

/-- A model of `T` with nonempty sorts. -/
structure ModelType where
  /-- The carriers. -/
  Carrier : S → Type w
  /-- The structure on the carriers. -/
  [struc : L.Structure Carrier]
  /-- The carriers form a model of `T`. -/
  [is_model : Carrier ⊨ T]
  /-- The sorts are nonempty. -/
  [nonempty' : ∀ s, Nonempty (Carrier s)]

attribute [instance] ModelType.struc ModelType.is_model ModelType.nonempty'

namespace ModelType

attribute [coe] Carrier

instance : CoeFun T.ModelType fun _ => S → Type w :=
  ⟨Carrier⟩

/-- Bundle a model. -/
def of (M : S → Type w) [L.Structure M] [M ⊨ T] [∀ s, Nonempty (M s)] : T.ModelType :=
  ⟨M⟩

@[simp]
theorem coe_of (M : S → Type w) [L.Structure M] [M ⊨ T] [∀ s, Nonempty (M s)] :
    ⇑(of T M) = M :=
  rfl

/-- The empty theory has a model: one point in every sort. -/
instance instInhabited : Inhabited (ModelType.{u, v, w, z} (∅ : L.Theory)) :=
  let : L.Structure fun _ => PUnit.{w + 1} := ⟨fun _ _ => PUnit.unit, fun _ _ => False⟩
  ⟨of _ fun _ => PUnit.{w + 1}⟩

variable {T}

instance of_small (M : S → Type w) [L.Structure M] [M ⊨ T] [∀ s, Nonempty (M s)]
    [h : ∀ s, Small.{w'} (M s)] (s : S) : Small.{w'} (of T M s) :=
  h s

/-- A model transported along a family of equivalences. -/
def equivInduced {M : T.ModelType} {N : S → Type w'} (e : ∀ s, M s ≃ N s) :
    ModelType.{u, v, w', z} T :=
  let := Equiv.inducedStructure L e
  { Carrier := N
    is_model := (Equiv.inducedStructureEquiv e).theory_model
    nonempty' := fun s => (M.nonempty' s).map (e s) }

/-- A model whose sorts are small in a universe `w'`, shrunk to `w'`. -/
noncomputable def shrink (M : T.ModelType) [∀ s, Small.{w'} (M s)] : ModelType.{u, v, w', z} T :=
  equivInduced fun s => equivShrink (M s)

/-- A model lifted to a larger universe. -/
def ulift (M : ModelType.{u, v, w, z} T) : ModelType.{u, v, max w w', z} T :=
  equivInduced (M := M) fun s => (@_root_.Equiv.ulift.{w', w} (M s)).symm

/-- The reduct of a model of `φ.onTheory T` is a model of `T`. -/
def reduct {L' : Language.{u', v'} S} (φ : L →ᴸ L') (M : (φ.onTheory T).ModelType) :
    T.ModelType :=
  let := φ.reduct M
  have := LHom.isExpansionOn_reduct φ (M := M)
  { Carrier := M
    is_model := (LHom.onTheory_model φ T).1 M.is_model }

/-- A model of `T`, expanded along an injective map of languages to a model of `φ.onTheory T`. -/
noncomputable def defaultExpansion {L' : Language.{u', v'} S} {φ : L →ᴸ L'} (h : φ.Injective)
    [∀ (σ t) (f : L'.Functions σ t),
      Decidable (f ∈ Set.range fun f : L.Functions σ t => φ.onFunction f)]
    [∀ (σ) (R : L'.Relations σ),
      Decidable (R ∈ Set.range fun R : L.Relations σ => φ.onRelation R)]
    (M : T.ModelType) [∀ s, Inhabited (M s)] : (φ.onTheory T).ModelType :=
  let := φ.defaultExpansion M
  have := h.isExpansionOn_default M
  { Carrier := M
    is_model := (LHom.onTheory_model φ T).2 M.is_model }

instance leftStructure {L' : Language.{u', v'} S} {T : (L.sum L').Theory} (M : T.ModelType) :
    L.Structure M :=
  (LHom.sumInl L L').reduct M

instance rightStructure {L' : Language.{u', v'} S} {T : (L.sum L').Theory} (M : T.ModelType) :
    L'.Structure M :=
  (LHom.sumInr L L').reduct M

/-- A model of `T` is a model of every subtheory of `T`. -/
def subtheoryModel (M : T.ModelType) {T' : L.Theory} (h : T' ⊆ T) : T'.ModelType :=
  { Carrier := M
    is_model := M.is_model.mono h }

instance subtheoryModel_models (M : T.ModelType) {T' : L.Theory} (h : T' ⊆ T) :
    M.subtheoryModel h ⊨ T :=
  M.is_model

end ModelType

variable {T}

/-- A model, bundled. -/
def Model.bundled {M : S → Type w} [L.Structure M] [∀ s, Nonempty (M s)] (h : M ⊨ T) :
    T.ModelType :=
  ModelType.of T M

@[simp]
theorem Model.coe_bundled {M : S → Type w} [L.Structure M] [∀ s, Nonempty (M s)] (h : M ⊨ T) :
    ⇑h.bundled = M :=
  rfl

/-! ### Models and realizations -/

variable (T) in
/-- **The realizations of a theory are its models in the universe of the language.** -/
def realizationEquivModelType : FormulaSet.Realization T ≃ ModelType.{u, v, max z u v, z} T where
  toFun r := ModelType.of T r.carrier
  invFun M := ⟨M, PUnit.unit, fun _ hφ => realize_sentence_of_mem hφ⟩
  left_inv := by rintro ⟨_, ⟨⟩, _⟩; rfl
  right_inv _ := rfl

/-- A theory is satisfiable exactly when it has a model in the universe of the language, which is
Mathlib's definition. -/
theorem isSatisfiable_iff_nonempty_modelType :
    T.IsSatisfiable ↔ Nonempty (ModelType.{u, v, max z u v, z} T) :=
  (realizationEquivModelType T).nonempty_congr

/-- A consequence of `T` is a sentence that holds in every model of `T` in the universe of the
language, as in Mathlib. -/
theorem models_sentence_iff_forall_modelType {φ : L.Sentence} :
    T ⊨ᵇ φ ↔ ∀ M : ModelType.{u, v, max z u v, z} T, M ⊨ φ :=
  ⟨fun h M => h M PUnit.unit, fun h M _ _ _ _ => h (ModelType.of T M)⟩

end Theory

/-! ### Elementarily equivalent structures as models -/

variable {T : L.Theory}

/-- A structure elementarily equivalent to a model of `T`, bundled as a model of `T`. -/
def ElementarilyEquivalent.toModel {M : T.ModelType} {N : S → Type w'} [L.Structure N]
    (h : L.ElementarilyEquivalent M N) : Theory.ModelType.{u, v, w', z} T :=
  { Carrier := N
    is_model := h.theory_model
    nonempty' := fun s => (h.nonempty_iff s).1 inferInstance }

/-- An elementary substructure of a model of `T`, bundled as a model of `T`. -/
def ElementarySubstructure.toModel {M : T.ModelType} (A : L.ElementarySubstructure M) :
    T.ModelType :=
  A.elementarilyEquivalent.symm.toModel

instance ElementarySubstructure.toModel.instSmall {M : T.ModelType}
    (A : L.ElementarySubstructure M) [h : ∀ s, Small.{w'} (A s)] (s : S) :
    Small.{w'} (A.toModel s) :=
  h s

end ManySorted.Language
