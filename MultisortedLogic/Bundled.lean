/-
Based on the corresponding Mathlib file by Aaron Anderson
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MultisortedLogic.Skolem

/-!
# Bundled Many-Sorted Structures and Models

This is the many-sorted analogue of Mathlib's `ModelTheory/Bundled.lean`, using a custom
bundle type (`StructureType`) instead of `CategoryTheory.Bundled`.
-/

universe u v z w w' x

namespace MSFirstOrder

namespace Language

open  Structure Cardinal


variable {Sorts : Type z} {L : Language.{u, v, z} Sorts} {L' : Language Sorts}

section structure_type

variable (L : Language.{u, v, z} Sorts)

/-- A bundled many-sorted `L`-structure with every sort nonempty. -/
structure StructureType where
  Carrier : Fam.{w} Sorts
  [struc : L.Structure Carrier]
  [nonempty' : ∀ {s : Sorts}, Nonempty (Carrier s)]

-- As in Mathlib's bundled file, bump priorities so these instances win when needed.
attribute [instance 2000] StructureType.struc StructureType.nonempty'

end structure_type

namespace StructureType

attribute [coe] StructureType.Carrier

instance instCoeTC (L : Language Sorts) : CoeTC (StructureType L) (Fam Sorts) :=
  ⟨StructureType.Carrier⟩

instance instStructure (L : Language Sorts) (M : StructureType L) :
    L.Structure (M : Fam Sorts) :=
  M.struc

instance instNonemptySort (L : Language Sorts) (M : StructureType L) {s : Sorts} :
    Nonempty ((M : Fam Sorts) s) :=
  M.nonempty'

/-- Bundle an existing structure and per-sort nonemptiness. -/
def of (L : Language Sorts) (M : Fam Sorts) [L.Structure M] [∀ s, Nonempty (M s)] :
    StructureType L :=
  ⟨M⟩

@[simp]
theorem coe_of (L : Language Sorts) (M : Fam Sorts) [L.Structure M] [∀ s, Nonempty (M s)] :
    ((of L M : StructureType L) : Fam Sorts) = M :=
  rfl

/-- Isomorphism relation on bundled many-sorted structures. -/
instance equivSetoid (L : Language Sorts) : Setoid (StructureType L) where
  r M N := Nonempty ((M : Fam Sorts) ≃[L] (N : Fam Sorts))
  iseqv :=
    ⟨fun M => ⟨Language.Equiv.refl L (M : Fam Sorts)⟩,
      fun {_ _} => Nonempty.map Language.Equiv.symm,
      fun {_ _ _} => Nonempty.map2 fun MN NP => Language.Equiv.comp NP MN⟩

end StructureType

namespace Fam.MSEquiv

variable {M : Fam.{w} Sorts} {N : Fam.{w'} Sorts}

/-- A many-sorted family equivalence induces a bundled structure on the codomain. -/
def bundledInduced (L : Language.{u, v, z} Sorts) [L.Structure M] [∀ s, Nonempty (M s)]
    (g : M ≃ₛ N) :
    StructureType.{u, v, z, w'} L where
  Carrier := N
  struc := Language.Equiv.inducedStructure (L := L) g
  nonempty' := by
    intro s
    rcases (‹∀ s, Nonempty (M s)› s) with ⟨m⟩
    exact ⟨g s m⟩

/-- The induced bundled structure is isomorphic to the source structure. -/
@[simp]
def bundledInducedEquiv (L : Language.{u, v, z} Sorts) [L.Structure M] [∀ s, Nonempty (M s)]
    (g : M ≃ₛ N) :
    M ≃[L] ((Fam.MSEquiv.bundledInduced (L := L) g : StructureType.{u, v, z, w'} L) : Fam Sorts)
    := by
  simp only [Fam.MSEquiv.bundledInduced]
  exact (Language.Equiv.inducedStructureEquiv (L := L) g)

end Fam.MSEquiv

namespace Theory

variable (T : L.Theory)

/-- The type of bundled nonempty many-sorted models of a theory. -/
structure ModelType where
  Carrier : Fam.{w} Sorts
  [struc : L.Structure Carrier]
  [is_model : T.Model Carrier]
  [nonempty' : ∀ {s : Sorts}, Nonempty (Carrier s)]

attribute [instance 2000] ModelType.struc ModelType.is_model ModelType.nonempty'

namespace ModelType

attribute [coe] ModelType.Carrier

instance instCoeTC : CoeTC T.ModelType (Fam Sorts) :=
  ⟨ModelType.Carrier⟩

instance instStructure (M : T.ModelType) : L.Structure (M : Fam Sorts) :=
  M.struc

instance instTheoryModel (M : T.ModelType) : (M : Fam Sorts) ⊨ T :=
  M.is_model

instance instNonemptySort (M : T.ModelType) {s : Sorts} : Nonempty ((M : Fam Sorts) s) :=
  M.nonempty'

section Inhabited

instance instInhabited : Inhabited ((∅ : L.Theory).ModelType) := by
  let M : Fam Sorts := ⟨fun _ => PUnit⟩
  letI : L.Structure M :=
    { funMap := fun _ _ => PUnit.unit
      RelMap := fun _ _ => False }
  letI : ∀ s, Nonempty (M s) := fun _ => ⟨PUnit.unit⟩
  exact ⟨(⟨M⟩ : (∅ : L.Theory).ModelType)⟩

end Inhabited

/-- Bundle an existing model. -/
def of (M : Fam.{w} Sorts) [L.Structure M] [M ⊨ T] [∀ s, Nonempty (M s)] : T.ModelType :=
  ⟨M⟩

@[simp]
theorem coe_of (M : Fam.{w} Sorts) [L.Structure M] [M ⊨ T] [∀ s, Nonempty (M s)] :
    ((of (T := T) M : T.ModelType) : Fam Sorts) = M :=
  rfl

instance of_small (M : Fam.{w} Sorts) [L.Structure M] [M ⊨ T] [∀ s, Nonempty (M s)]
    [h : ∀ s, Small.{w'} (M s)] (s : Sorts) :
    Small.{w'} ((((ModelType.of (T := T) M : T.ModelType) : Fam Sorts) s)) := by
  simpa [ModelType.coe_of (T := T)] using (h s)

instance instSmallSigma (M : T.ModelType) [h : ∀ s, Small.{w'} (((M : Fam Sorts) s))] :
    Small.{max z w'} (Σ s, ((M : Fam Sorts) s)) := by
  letI : ∀ s, Small.{w'} (((M : Fam Sorts) s)) := h
  letI : Small.{max z w'} Sorts := Small.mk' (Equiv.ulift.symm : Sorts ≃ ULift.{w'} Sorts)
  letI : ∀ s, Small.{max z w'} (((M : Fam Sorts) s)) := fun s =>
    show Small.{max z w'} (((M : Fam Sorts) s)) from small_lift (((M : Fam Sorts) s))
  infer_instance

/-- Transport a bundled model across a many-sorted equivalence. -/
def equivInduced {M : T.ModelType} {N : Fam.{w'} Sorts} (e : (M : Fam Sorts) ≃ₛ N) :
    T.ModelType where
  Carrier := N
  struc := Language.Equiv.inducedStructure (L := L) e
  is_model := by
    letI : L.Structure N := Language.Equiv.inducedStructure (L := L) e
    letI : (M : Fam Sorts) ⊨ T := M.is_model
    exact StrongHomClass.theory_model
      (g := Language.Equiv.inducedStructureEquiv (L := L) e) (T := T)
  nonempty' := by
    intro s
    rcases (M.nonempty' (s := s)) with ⟨m⟩
    exact ⟨e s m⟩

/-- Shrink each sort of a model into a target universe. -/
noncomputable def shrink (M : T.ModelType)
    (hsmall : ∀ s, Small.{w'} (((M : Fam Sorts) s))) : T.ModelType := by
  let N : Fam.{w'} Sorts := ⟨fun s => Shrink (((M : Fam Sorts) s))⟩
  let e : (M : Fam Sorts) ≃ₛ N := by
    refine Fam.MSEquiv.fromEquivs ?_
    intro s
    letI : Small.{w'} (((M : Fam Sorts) s)) := hsmall s
    exact equivShrink (((M : Fam Sorts) s))
  exact equivInduced (T := T) e

/-- Lift each sort of a model by `ULift`. -/
def ulift (M : T.ModelType) : T.ModelType := by
  let N : Fam.{max w w'} Sorts := ⟨fun s => ULift.{w'} (((M : Fam Sorts) s))⟩
  let e : (M : Fam Sorts) ≃ₛ N :=
    Fam.MSEquiv.fromEquivs (fun s => Equiv.ulift.symm)
  exact equivInduced (T := T) e

/-- The reduct of a model of `φ.onTheory T` is a model of `T`. -/
def reduct {L' : Language Sorts} (φ : L →ᴸ L') (M : (φ.onTheory T).ModelType) : T.ModelType
  where
  Carrier := M
  struc := φ.reduct M
  nonempty' := M.nonempty'
  is_model := by
    letI : L.Structure (M : Fam Sorts) := φ.reduct M
    exact (LHom.onTheory_model (M := (M : Fam Sorts)) φ T).1 M.is_model

/-- Expand a model of `T` to a model of `φ.onTheory T` by a default expansion, when `φ` is
  injective. -/
noncomputable def defaultExpansion {L' : Language Sorts} {φ : L →ᴸ L'} (h : φ.Injective)
    [∀ (σ t) (f : L'.Functions σ t),
      Decidable (f ∈ Set.range fun f : L.Functions σ t => φ.onFunction f)]
    [∀ (σ) (r : L'.Relations σ),
      Decidable (r ∈ Set.range fun r : L.Relations σ => φ.onRelation r)]
    (M : T.ModelType) : (φ.onTheory T).ModelType := by
  classical
  letI : ∀ s, Inhabited (((M : Fam Sorts) s)) := fun s =>
    Classical.inhabited_of_nonempty (M.nonempty' (s := s))
  letI : L'.Structure (M : Fam Sorts) := φ.defaultExpansion M
  letI : φ.IsExpansionOn (M : Fam Sorts) := h.isExpansionOn_default M
  exact
    { Carrier := M
      struc := inferInstance
      nonempty' := M.nonempty'
      is_model := (LHom.onTheory_model (M := (M : Fam Sorts)) φ T).2 M.is_model }

instance leftStructure {L' : Language Sorts} {T : (L.sum L').Theory} (M : T.ModelType) :
    L.Structure (M : Fam Sorts) :=
  (LHom.sumInl : L →ᴸ L.sum L').reduct M

instance rightStructure {L' : Language Sorts} {T : (L.sum L').Theory} (M : T.ModelType) :
    L'.Structure (M : Fam Sorts) :=
  (LHom.sumInr : L' →ᴸ L.sum L').reduct M

/-- A model of `T` is a model of any subtheory `T' ⊆ T`. -/
def subtheoryModel (M : T.ModelType) {T' : L.Theory} (h : T' ⊆ T) : T'.ModelType where
  Carrier := M
  struc := M.struc
  nonempty' := M.nonempty'
  is_model := ⟨fun _φ hφ => Theory.realize_sentence_of_mem (T := T) (M := M) (h hφ)⟩

instance subtheoryModel_models (M : T.ModelType) {T' : L.Theory} (h : T' ⊆ T) :
    ((ModelType.subtheoryModel (T := T) M h : T'.ModelType) : Fam Sorts) ⊨ T' :=
  (ModelType.subtheoryModel (T := T) M h).is_model

end ModelType

variable {T}

/-- Bundle a proof that `M` models `T`. -/
def Model.bundled {M : Fam.{w} Sorts} [LM : L.Structure M] [∀ s, Nonempty (M s)] (h : M ⊨ T) :
    T.ModelType :=
  ModelType.of (T := T) M

@[simp]
theorem coe_of {M : Fam.{w} Sorts} [L.Structure M] [∀ s, Nonempty (M s)] (h : M ⊨ T) :
    ((Theory.Model.bundled (T := T) h : T.ModelType) : Fam Sorts) = M :=
  rfl

end Theory

/-- Bundle a structure elementarily equivalent to a bundled model as a bundled model. -/
def ElementarilyEquivalent.toModel {T : L.Theory} {M : T.ModelType} {N : Fam Sorts}
    [L.Structure N] (h : (M : Fam Sorts) ≅[L] N) : T.ModelType where
  Carrier := N
  struc := inferInstance
  nonempty' := by
    intro s
    letI : Nonempty ((M : Fam Sorts) s) := M.nonempty'
    exact h.nonempty
  is_model := by
    letI : (M : Fam Sorts) ⊨ T := M.is_model
    exact h.theory_model

/-- An elementary substructure of a bundled model, bundled as a model of the same theory. -/
def ElementarySubstructure.toModel {T : L.Theory} {M : T.ModelType}
    (S : L.ElementarySubstructure M) : T.ModelType :=
  S.elementarilyEquivalent.symm.toModel (T := T)

instance ElementarySubstructure.toModel.instSmall {T : L.Theory} {M : T.ModelType}
    (S : L.ElementarySubstructure M) {s : Sorts} [h : Small.{w'} (S s)] :
    Small.{w'} ((((S.toModel (T := T) : T.ModelType) : Fam Sorts) s)) := by
  exact h

end Language
end MSFirstOrder
