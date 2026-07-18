/- The structure of this file is based on the corresponding Mathlib file Satisfiability.lean,
    which was authored by Aaron Anderson and released under Apache 2.0 license as described in the
    file LICENSE.
  -/
import MultisortedLogic.Ultraproducts
import MultisortedLogic.ElementaryMapsMS
import MultisortedLogic.Skolem



/-!
# First-Order Satisfiability
This file deals with the satisfiability of sets of formulas (model-theoretic types)
This file is currently in parallel with `Satisfiable.lean`, but is intended to eventually replace it.

## Main Definitions

- `MSFirstOrder.Language.FSet`: an `L.FSet α σ` is a set of BoundedFormulas in variables `α` and `σ`
- `MSFirstOrder.Language.StructureType`: a `StructureType L α σ` bundles the information of an
  `L`-structure `M` and variable assignments`v : α →ₛ M` and `x : M [^] σ`
- `MSFirstOrder.Language.NonemptyStructureType`: a `StructureType` bundled with the information that
  it is nonempty
- `MSFirstOrder.Language.FSet.Realizations`: For  `M : NonemptyStructureType α σ` and
  `p : L.FSet α σ`, we have `M ∈ Realizations p` iff `M` realizes `p`

## Main Results

- `MSFirstOrder.Language.FSet.isSatisfiable_iff_isFinitelySatisfiable`,
  shows that a theory is satisfiable iff it is finitely satisfiable.

-/

/- Based on the following work by, and suggestions from, Silvain Rideau-Kikuchi
  * Suggestion to work with sets of formulas/types over Sentences
  * First definitions of Realization/IsSatisfiable
  * Proof of compactness theorem in this setting, bulding on Łos' theorem -/


universe u v u' z w

namespace MSFirstOrder

namespace Language

open Language Fam Structure Theory Signature

variable {Sorts : Type z}

/-- A set of L.BoundedFormula α σ -/
abbrev FSet (L : Language.{u, v, z} Sorts) (α : Fam.{u'} Sorts)
  (σ : Signature Sorts) := Set (L.BoundedFormula α σ)

/-- A generalization of Mathlib's StructureType to sets of formulas rather than sentences.
  As opposed to Realizations/models, these can be empty. -/
structure StructureType (L : Language.{u, v, z} Sorts)
    (α : Fam.{u'} Sorts) (σ : Signature Sorts) where
  Carrier : Fam.{w} Sorts
  v : α →ₛ Carrier
  x : Carrier [^] σ
  [struc : L.Structure Carrier]

/-- A structure with the additional typeclass hypothesis that all sorts are nonempty. -/
structure NonemptyStructureType (L : Language.{u, v, z} Sorts) (α : Fam.{u'} Sorts)
    (σ : Signature Sorts) extends StructureType L α σ where
  [nonempty : ∀ s, Nonempty (Carrier s)]

instance StructureType.instCoeTC (L : Language.{u, v, z} Sorts) {α : Fam.{u'} Sorts}
    {σ : Signature Sorts} : CoeTC (StructureType L α σ) (Fam Sorts) :=
  ⟨StructureType.Carrier⟩

-- As in Mathlib's bundled file, bump priorities so these instances win when needed.
attribute [instance 2000] StructureType.struc

--TODO: question: rather have a "StructureClass" which is implemented by nonemptyStructureType?
instance instCoeStructure (L : Language.{u, v, z} Sorts) (α : Fam.{u'} Sorts)
    (σ : Signature Sorts) : Coe (NonemptyStructureType L α σ) (L.StructureType α σ) where
  coe M := ⟨M.Carrier, M.v, M.x⟩

namespace FSet

variable {Sorts : Type z} {L : Language.{u, v, z} Sorts} {α : Fam.{u'} Sorts} {β : Fam Sorts}
  {σ τ : Signature Sorts} (M : Fam.{w} Sorts) [L.Structure M]
  (v : α →ₛ M) (x : M [^] σ) (p : L.FSet α σ) (q : L.FSet α σ)

/-- Rename all bounded formulas. -/
def rename {β : Fam Sorts} (f : α →ₛ β) : L.FSet α σ  → L.FSet β σ :=
  fun p => (BoundedFormula.rename f)'' p

/-- Reindex all bounded formulas. -/
def reindex {τ : Signature Sorts} (f : SigMap σ τ) : L.FSet α σ → L.FSet α τ :=
  fun p => (BoundedFormula.reindex f)'' p

attribute [coe] StructureType.Carrier

instance instCoeSort : CoeSort (L.StructureType α σ) (Fam.{w} Sorts) :=
  ⟨StructureType.Carrier⟩

/-- An set of bounded formulas is realized if all the formulas in it evaluate to True.
  A generalization of the Mathlib notion of Theory.Model, but as a def rather than a class. -/
def Realizes (M : L.StructureType α σ) (p : L.FSet α σ) :=
  ∀ φ ∈ p, φ.Realize M.v M.x

variable {M : L.StructureType α σ}

/-- Input \vDash or \|=, but not using \models. -/
infixl:51 " ⊨ᵖ " => Realizes

/-- Every member of a set of formulas is realized in a realization. -/
theorem realize_of_mem (hp : M ⊨ᵖ p) {φ : L.BoundedFormula α σ} (h : φ ∈ p) :
  φ.Realize M.v M.x := hp φ h

/- TODO: make this a simp lemma again? Is @[simp default - 10] in the equivalent Mathlib def -/
theorem realize_iff {p : L.FSet α σ} (M : L.StructureType α σ) :
  M ⊨ᵖ p ↔ ∀ φ ∈ p, φ.Realize M.v M.x := by rfl

/-- If M satisfies some type `p`, then it also satisfies each weaker type `q`. -/
theorem realize_mono {p q : L.FSet α σ} {M : L.StructureType α σ} (h : M ⊨ᵖ p) (hs : q ⊆ p) :
    M ⊨ᵖ q := fun φ hφ => h φ (hs hφ)

theorem isModel_union {p q : L.FSet α σ} (h : M ⊨ᵖ p) (h' : M ⊨ᵖ q) : M ⊨ᵖ p ∪ q :=
  fun _φ hφ => hφ.elim (h _) (h' _)

theorem realize_left {p q : L.FSet α σ} (h : M ⊨ᵖ p ∪ q) : M ⊨ᵖ p  :=
  realize_mono h Set.subset_union_left

theorem realize_right {p q : L.FSet α σ} (h : M ⊨ᵖ p ∪ q) : M ⊨ᵖ q :=
  realize_mono h Set.subset_union_right

@[simp]
theorem realize_union_iff : M ⊨ᵖ p ∪ q ↔ M ⊨ᵖ p ∧ M ⊨ᵖ q :=
  ⟨fun h => ⟨realize_left h, realize_right h⟩,
  fun h => isModel_union h.1 h.2⟩



@[simp]
theorem realize_singleton_iff {φ : L.BoundedFormula α σ} :
     M ⊨ᵖ ({φ} : L.FSet α σ) ↔ φ.Realize M.v M.x := by
  rw [realize_iff]
  simp only [Set.mem_singleton_iff, forall_eq]

theorem realize_insert_iff {φ : L.BoundedFormula α σ} : M ⊨ᵖ insert φ p ↔  φ.Realize M.v M.x ∧
  M ⊨ᵖ p
  := by rw [Set.insert_eq, realize_union_iff, realize_singleton_iff]

variable {N : Fam Sorts} [L.Structure N] {w : β →ₛ N} {y : N [^] τ}

theorem realize_rename_iff {f : α →ₛ β} {r : L.FSet α τ} :
    ⟨N, w, y⟩  ⊨ᵖ r.rename f ↔ ⟨N, w ∘ₛ f, y⟩ ⊨ᵖ r := by
  simp only [realize_iff, rename, Set.forall_mem_image, BoundedFormula.realize_rename]

theorem realize_rename_inl (h : M ⊨ᵖ p) (w : (α ⊕ₛ β) →ₛ M) (hw : w ∘ₛ inl = M.v) :
    ⟨M, w, M.x⟩ ⊨ᵖ p.rename inl := by
  rw [realize_rename_iff]
  simp only [hw, h]

theorem realize_rename_inr (h : M ⊨ᵖ p) (w : (β ⊕ₛ α) →ₛ M) (hw : w ∘ₛ inr = M.v) :
    ⟨M, w, M.x⟩ ⊨ᵖ p.rename inr := by
  rw [realize_rename_iff]
  simp only [hw, h]

/-- A structure realizes the union of types in `p`, `q` in disjoint variables if it realizes both of
 the types separately. -/
theorem realize_union_rename_sum {M : Fam Sorts} [L.Structure M] {p : L.FSet α σ} {q : L.FSet β σ}
    {v : α →ₛ M} {w : β →ₛ M} {x : M [^] σ} (hp : ⟨M, v, x⟩ ⊨ᵖ p) (hq : ⟨M, w, x⟩ ⊨ᵖ q) :
    ⟨M, Fam.sumElim v w, x⟩ ⊨ᵖ (p.rename inl) ∪ (q.rename inr) := by
  rw [realize_iff]
  intro φ hφ
  cases hφ with
  | inl hφ =>
    apply realize_rename_inl p hp (Fam.sumElim v w) (Fam.sumElim_inl _ _)
    exact hφ
  | inr hφ =>
    apply realize_rename_inr q hq (Fam.sumElim v w) (Fam.sumElim_inr _ _)
    exact hφ

theorem realize_reindex_iff {f : SigMap σ τ} {r : L.FSet β σ} :
    ⟨N, w, y⟩ ⊨ᵖ r.reindex f ↔ ⟨N, w, y.comap f⟩ ⊨ᵖ r := by
  simp only [reindex, realize_iff, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, BoundedFormula.realize_reindex]

theorem realize_reindex_nil {r : L.FSet α ⦃⦄} {M : L.StructureType α ⦃⦄}
    (h : M ⊨ᵖ r) {x : M [^] σ} : ⟨M,M.v,x⟩ ⊨ᵖ r.reindex default := by
  rw [realize_reindex_iff]
  simp only [h]

theorem realize_reindex_nil_iff {r : L.FSet α ⦃⦄} {M : L.StructureType α ⦃⦄}
    {x : M [^] σ} : M ⊨ᵖ r ↔ ⟨M, M.v, x⟩ ⊨ᵖ r.reindex (default : SigMap ⦃⦄ σ)  := by
  rw [realize_reindex_iff]


/-TODO: evaluate this particular design choice. I really want this to just be a bundle for a
  StructureType with a proof of realization  -/
/-- All realizations of a type `p` given by `M : Fam.{w} Sorts`. -/
structure Realization {L : Language.{u, v, z} Sorts} {α : Fam.{u'} Sorts} {σ : Signature Sorts}
    (p : L.FSet α σ) extends NonemptyStructureType L α σ where
  is_realization : ⟨Carrier, v, x⟩  ⊨ᵖ p

instance instCoeNonemptyStructureType : CoeOut (Realization p) (NonemptyStructureType L α σ) where
  coe := Realization.toNonemptyStructureType
/-
def Realizations {L : Language.{u, v, z} Sorts} {α : Fam.{u'} Sorts} {σ : Signature Sorts}
    (p : L.FSet α σ) : Set (NonemptyStructureType.{u, v, u', z, w} L α σ) := {M | M ⊨ᵖ p}
-/

/-
@[simp]
theorem mem_realizations_iff (M : NonemptyStructureType L α σ) : (M ∈ Realizations p) ↔ M ⊨ᵖ p :=
  by rfl
-/

/-
structure Realization {L : Language.{u, v, z} Sorts} {α : Fam.{u'} Sorts} {σ : Signature Sorts}
  (p : L.FSet α σ) where
  Carrier : Fam.{w} Sorts
  v : α →ₛ Carrier
  x : Carrier [^] σ
  [struc : L.Structure Carrier]
  [nonempty' : ∀ s, Nonempty (Carrier s)]
  is_realization : ⟨Carrier, v, x⟩  ⊨ᵖ p


-- As in Mathlib's bundled file, increase priority
attribute [instance 2000] Realization.struc Realization.nonempty'

namespace Realization

def Struc {p : L.FSet α σ} (M : Realization p) : L.NonemptyStructureType α σ :=
  letI := M.struc
  letI := M.nonempty'
  ⟨M.Carrier, M.v, M.x⟩

def ofStruc (p : L.FSet α σ) (M : L.NonemptyStructureType α σ) (hsat : M ⊨ᵖ p) :
    Realization p :=
    letI := M.nonempty
    ⟨M.Carrier, M.v, M.x, hsat⟩

theorem struc_realizes {p : L.FSet α σ} (M : Realization p) : M.Struc ⊨ᵖ p :=  M.is_realization

@[simp]
theorem ofStruc_Struc {p : L.FSet α σ} (M : Realization p) :
  ofStruc p (Struc M) M.is_realization = M := rfl

@[simp]
theorem Struc_ofStruc {p : L.FSet α σ}
    (M : L.NonemptyStructureType α σ) (hsat : M ⊨ᵖ p) :
  Struc (ofStruc p M hsat) = M := rfl


instance instCoeNonemptyStructureType : CoeOut (Realization p) (NonemptyStructureType L α σ) where
  coe M := Struc M

end Realization
-/
/-
/-- A realization of a set of bounded formulas consists of a carrier that is nonempty in all sorts
  + interpretations that realize the formulas. -/
structure Realization where
  Carrier : Fam.{w} Sorts
  v : Fam.FamMap α Carrier
  x : Carrier [^] σ
  [struc : L.Structure Carrier]
  is_model : ⟨Carrier, v, x⟩ ⊨ᵖ p
  [nonempty' : ∀ {s : Sorts}, Nonempty (Carrier s)]

attribute [instance 2000] Realization.struc Realization.is_model Realization.nonempty'

namespace Realization

attribute [coe] Realization.Carrier

instance instCoeSort : CoeSort p.Realization (Fam.{w} Sorts) :=
  ⟨Realization.Carrier⟩

def of (p : L.FSet α σ) (M : Fam Sorts) (v : α →ₛ M) (x : M [^] σ) [L.Structure M]
  (hsat : ⟨M, v, x⟩ ⊨ᵖ p) [∀ s, Nonempty (M s)] : p.Realization := ⟨M, v, x, hsat⟩

@[simp]
theorem coe_of {p : L.FSet α σ} {M : Fam Sorts} {v : α →ₛ M} {x : M [^] σ} [L.Structure M]
  {hsat : ⟨M, v, x⟩ ⊨ᵖ p} [∀ s, Nonempty (M s)] : of p M v x hsat = M :=
  rfl

instance instNonempty (M : p.Realization) : ∀ s, Nonempty (M.Carrier s) :=
  inferInstance

section Inhabited

attribute [local instance] Inhabited.trivialStructure


instance instInhabited [Inhabited Sorts] : Inhabited (Realization (∅ : L.FSet α σ)) :=
  let M : Fam Sorts := ⟨fun _ => Unit⟩
  letI : (s : Sorts) → Inhabited (M s) := fun _ => inferInstanceAs (Inhabited Unit)
  ⟨⟨⟨ fun _ => Unit⟩, default, default , by rw [realize_iff]; simp only [Set.mem_empty_iff_false,
    IsEmpty.forall_iff, implies_true]⟩⟩

end Inhabited

end Realization
-/
/-- A theory is satisfiable if there exists a realization at the minimal universe level. -/
def IsSatisfiable : Prop :=
  Nonempty (Realization.{u, v, u', z, max u v u' z} p)

def IsFinitelySatisfiable : Prop :=
  ∀ p0 : Finset (L.BoundedFormula α σ),
    (p0 : FSet L α σ) ⊆ p → IsSatisfiable (p0 : FSet L α σ)

theorem IsSatisfiable.mono {p q : L.FSet α σ} (h : q.IsSatisfiable) (hs : p ⊆ q) : p.IsSatisfiable
  := by
  obtain ⟨M, hsat⟩  := h.some
  exact ⟨M, realize_mono hsat hs⟩

/-- The **Compactness theorem in first-order logic**: A set of formulas is
  satisfiable if and only if it is finitely satisfiable. -/
theorem isSatisfiable_of_isFinitelySatisfiable
  (h : IsFinitelySatisfiable.{u, v, u', z} p) : IsSatisfiable.{u, v, u', z} p := by
    let getreal : (p0 : Finset p) →
      Realization.{u, v, u', z, max u v u' z} (p0.map (Function.Embedding.subtype p) : L.FSet α σ)
      := fun p0 => (h (p0.map (Function.Embedding.subtype p)) p0.map_subtype_subset).some
    let getStruc := fun p0 => (getreal p0).toNonemptyStructureType
    let getSat :=  fun p0 => (getreal p0).is_realization
    letI hstruc : ∀ p0, L.Structure (getStruc p0).Carrier :=
      fun p0 => ((getStruc p0)).struc
    letI hnonempty : ∀ p0  s, Nonempty ((getStruc p0).Carrier s) :=
      fun p0 => (getStruc p0).nonempty
    let U := Ultrafilter.of (Filter.atTop : Filter (Finset p))
    letI := Ultraproduct.structure (fun p0 => (getStruc p0).Carrier) U (i := hstruc)
    refine ⟨?_ , ?_⟩
    · exact NonemptyStructureType.mk.{u,v,u',z, max u v u' z}
        ⟨Ultraproduct (fun p0 => (getStruc p0).Carrier) U,
        MSQuotient.mk _ ∘ₛ ⟨fun s x p0 => (getStruc p0).v s x⟩,
        (pi_lift_inv (fun p0 => (getStruc p0).x)).toQuot (R := ReducedProductSetoid _ _)⟩
    · intro φ hφ
      rw [Ultraproduct.boundedFormula_realize]
      refine Filter.Eventually.filter_mono (Ultrafilter.of_le _) ?_
      rw [Filter.eventually_atTop]
      use {⟨φ, hφ⟩}
      intro p0 hp0
      rw [pi_lift_LeftInverse]
      refine (getSat p0) φ ?_
      simp only [Finset.coe_map, Function.Embedding.subtype_apply, Set.mem_image, SetLike.mem_coe,
        Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨⟨φ, hφ⟩, hp0 (Finset.mem_singleton_self _), rfl⟩

theorem isSatisfiable_iff_isFinitelySatisfiable : IsSatisfiable p ↔ IsFinitelySatisfiable p := by
  refine ⟨fun hsat p0 hp0 => IsSatisfiable.mono hsat hp0,
    fun hp => isSatisfiable_of_isFinitelySatisfiable p hp⟩

theorem isSatisfiable_directed_union_iff {ι : Type*} [Nonempty ι] {p : ι → L.FSet α σ}
    (h : Directed (· ⊆ ·) p) : IsSatisfiable (⋃ i, p i) ↔ ∀ i, (p i).IsSatisfiable := by
  refine ⟨fun h' i => h'.mono (Set.subset_iUnion _ _), fun h' => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable, IsFinitelySatisfiable]
  intro T0 hT0
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_biUnion hT0
  exact (h' i).mono hi


section elementaryDiagram

/-- The elementary diagram as a type. -/
abbrev DiagType (L : Language Sorts) (N : Fam Sorts) [L.Structure N] : L.FSet N ⦃⦄ :=
  {φ | φ.Realize FamMap.idₛ default}

/-- If N satisfies all formulas in the elementary diagram of M, then M elementary embeds into M,
  using the given variable assignment as map. -/
def ElementaryEmbedding.ofModelsDiagType {M : Fam Sorts} [L.Structure M]
    {N : L.StructureType M ⦃⦄} (h : N ⊨ᵖ DiagType L M) : ElementaryEmbedding L M N := by
  refine ElementaryEmbedding.ofMapFormulaM N.v ?_
  intro φ
  rw [Formula.Realize]
  /- One implication is trivial, for the other we need to show that formulas not realized by
    M are also not realized by N -/
  constructor
  · intro hφ
    -- If M does not model φ, then ∼φ will be in the elementary diagram of M
    by_contra hM
    rw [Formula.Realize,← BoundedFormula.realize_not] at hM
    have hN : BoundedFormula.Realize (∼φ) N.v default := by
      apply h
      exact hM
    rw [BoundedFormula.realize_not] at hN
    exact hN hφ
  · apply h


open scoped Classical in
/-- If a type `p` is finitely satisfiable in M, then the union of that type and the elementary
  diagram is satisfiable as well (up to renaming). -/
theorem isSatisfiable_finsat_union_diagtype (p : L.FSet α σ) (M : Fam.{w} Sorts)
    [L.Structure M] [∀ s, Nonempty (M s)] (hsat : ∀ (p0 : Finset (L.BoundedFormula α σ)),
     ((p0 : L.FSet α σ) ⊆ p) →
     ∃ (v : α →ₛ M) (x : M [^] σ), ⟨M, v, x⟩ ⊨ᵖ (p0 : L.FSet α σ))
    : IsSatisfiable ((((DiagType L M).reindex default).rename (Fam.inl : M →ₛ M ⊕ₛ α))
      ∪ (rename (Fam.inr : α →ₛ M ⊕ₛ α) p))  := by
  apply isSatisfiable_of_isFinitelySatisfiable
  rw [IsFinitelySatisfiable]
  intro q0 hsub
  have hinj : Function.Injective (BoundedFormula.rename (f := Fam.inr) :
      L.BoundedFormula α σ → L.BoundedFormula (M ⊕ₛ α) σ) :=
    BoundedFormula.rename_injective_of_injective (fun s => Sum.inr_injective)
  let p0' := q0.filter (· ∈ rename inr p)
  have hp0 : ∀ φ, φ ∈ p0' ↔ φ ∈ q0 ∧ φ ∈ p.rename inr := fun _ => Finset.mem_filter
  /- p0 consists of all formulas in p that map to a formula in p0' under renaming.
    It is finite by injectivity of formula renaming. -/
  set p0 := Finset.preimage p0' (BoundedFormula.rename inr) hinj.injOn with p0_def
  /- Since p0' is in the image of the rename operation, it is the image of p0 under renaming. -/
  have hp0_eq : FSet.rename (inr : α →ₛ  M ⊕ₛ α) p0 = (↑p0' : L.FSet (M ⊕ₛ α) σ) := by
    change (BoundedFormula.rename inr)'' (↑p0 : Set _) = (↑p0' : L.FSet (M ⊕ₛ α) σ)
    simp only [Finset.coe_preimage, p0_def]
    refine Set.image_preimage_eq_iff.mpr (fun φ hφ => ?_)
    exact Set.image_subset_range _ p ((hp0 φ).mp hφ).2
  /- Since we renamed only elements from p and renaming is injective, p0 is a subset of p. -/
  have hp0_sub : (p0 : L.FSet α σ) ⊆ p := fun φ hφ => by
    rw [Finset.mem_coe, Finset.mem_preimage, hp0, FSet.rename, Set.mem_image] at hφ
    obtain ⟨ψ, hψ, hψ_eq⟩ := hφ.2
    exact hinj hψ_eq ▸ hψ
  obtain ⟨v, x, h'⟩ := hsat p0 hp0_sub
  set d := rename (Fam.inl : M →ₛ M ⊕ₛ α) ((DiagType L M).reindex (default : SigMap ⦃⦄ σ))
    with d_def
  /- It suffices to show the statement with q0 replaced by the larger set given by adding all
    (renamed) formulas from the elementary diagram. -/
  refine IsSatisfiable.mono (p := q0) (q := (d ∪ p0')) ?_ ?_
  · apply Nonempty.intro ?_
    -- Create a lift of M at the appropriate universe level
    -- this is necessary because of the presence of variables `α` in `p`
    let N : Fam.{max u v u' z w} Sorts := ⟨fun s => ULift.{max u v u' z} (M s)⟩
    let equivM : M ≃ₛ N  := MSEquiv.fromEquivs (fun s => Equiv.ulift.symm)
    letI : L.Structure N := Equiv.inducedStructure equivM
    let equivL : M ≃[L] N := Equiv.inducedStructureEquiv equivM
    letI : ∀ s, Nonempty (N s) := fun {s} => Nonempty.map (Equiv.ulift.symm) inferInstance
    refine ⟨⟨N,?_,?_⟩,?_⟩
      -- Constructing the map M ⊕ₛ α → M → N
    · exact Fam.sumElim equivL (equivL ∘ₛ v)
      -- Mapping M [^] σ → N [^] σ
    · exact equivL <$>ₛ x
    · rw [d_def, ← hp0_eq]
      refine realize_union_rename_sum ?_ ?_
      · -- N satisfies all formulas from the elementary diagram of M
        rw [← realize_reindex_nil_iff (M := ⟨N,_,default⟩), realize_iff]
        intro φ hφ
        change Formula.Realize φ ((equivL : M →ₛ N) ∘ₛ FamMap.idₛ)
        rw [StrongHomClass.realize_formula equivL]
        exact hφ
      · -- N satisfies all formulas from p
        rw [realize_iff]
        intro φ hφ
        rw [StrongHomClass.realize_boundedFormula equivL φ]
        exact h' φ hφ
  · -- It remains to check that q0 ⊆ p0 ∪ d
    intro x hx
    rcases hsub hx with hd | hr
    · exact Set.mem_union_left _ hd
    · apply Set.mem_union_right
      rw [Finset.mem_coe, hp0]
      exact ⟨Finset.mem_coe.mp hx, hr⟩


/-- If p is finitely satisfiable in M, then it is realized in an elementary extension of M. -/
theorem realize_in_ext_of_finsat (p : L.FSet α σ) (M : Fam.{w} Sorts)
    [L.Structure M] [∀ s, Nonempty (M s)] (h_finsat : ∀ (p0 : Finset (L.BoundedFormula α σ)),
     ((p0 : L.FSet α σ) ⊆ p) →
     ∃ (v : α →ₛ M) (x : M [^] σ), ⟨M, v, x⟩ ⊨ᵖ (p0 : L.FSet α σ)) :
     ∃ (N : StructureType.{u, v, u', z, max u v u' z w} L α σ) (_f : ElementaryEmbedding L M N),
     N ⊨ᵖ p := by
  -- The proof is essentially immediate after using that the given type is satisfiable
  have hsat := isSatisfiable_finsat_union_diagtype p M h_finsat
  obtain ⟨N', hN⟩ := hsat
  obtain ⟨⟨N, v, x⟩, _⟩ := N'
  use ⟨N, v ∘ₛ inr, x⟩
  rw  [realize_union_iff] at hN
  rcases hN with ⟨hN₁, hN₂⟩
  have hNd : ⟨N, v ∘ₛ inl, default⟩ ⊨ᵖ DiagType L M := by
    rw [realize_rename_iff] at hN₁
    rw [realize_reindex_nil_iff]
    apply hN₁
  let f := ElementaryEmbedding.ofModelsDiagType hNd
  use f
  rw [realize_rename_iff] at hN₂
  exact hN₂

end elementaryDiagram

section Models

variable {φ : L.BoundedFormula α σ}

/-- A set of bounded formulas `p` models a formula `φ` if `φ` evaluations to true in all
  realizations of `p` (at the lowest possible universe level). -/
def Models (p : L.FSet α σ) (φ : L.BoundedFormula α σ) : Prop :=
  ∀ (M : Realization.{u, v, u', z, max u u' v z} p), φ.Realize M.v M.x

/-- Input \vDash or \|=, but not using \models. -/
infixl:51 " ⊨ᵇ " => Models

theorem models_iff : p ⊨ᵇ φ ↔ ∀ (M : Realization.{u, v, u', z, max u u' v z} p),
  φ.Realize M.v M.x := Iff.rfl

theorem models_bounded_formula_iff_models_imp_imp {ψ : L.BoundedFormula α σ} : p ⊨ᵇ φ ⇔ ψ ↔
  p ⊨ᵇ φ ⟹ ψ ∧ p ⊨ᵇ ψ ⟹ φ
    := by
  simp_all only [models_iff, BoundedFormula.realize_iff, BoundedFormula.realize_imp]
  grind

/-- A set of formulas models all of its members. -/
theorem models_of_mem : ∀ φ ∈ p, p ⊨ᵇ φ := fun φ hφ M => M.is_realization φ hφ

theorem models_mono {p : L.FSet α σ} (q : L.FSet α σ) (h : p ⊨ᵇ φ) (hsub : p ⊆ q) : q ⊨ᵇ φ :=
  fun M => h ⟨M, realize_mono M.is_realization hsub⟩

theorem models_of_models_mem_set (h : ∀ φ ∈ p, q ⊨ᵇ φ) (hp : p ⊨ᵇ φ) : q ⊨ᵇ φ := fun M =>
  hp ⟨M, fun ψ hψ => h ψ hψ M⟩

/-- A type `p` models a sentence `φ` if and only if `p ∪ {∼φ}` is not satisfiable. -/
theorem models_iff_not_satisfiable : p ⊨ᵇ φ ↔ ¬IsSatisfiable (p ∪ {φ.not}) := by
  rw [models_iff, IsSatisfiable]
  constructor
  · intro h h_nonempty
    obtain ⟨M,hsat⟩  := h_nonempty
    simp only [realize_union_iff] at hsat
    obtain ⟨hp, hφ⟩ := hsat
    rw [realize_singleton_iff, BoundedFormula.realize_not] at hφ
    exact hφ (h ⟨M, hp⟩)
  · contrapose!
    intro ⟨M, hφ⟩
    refine ⟨M, ?_⟩
    rw [realize_union_iff, realize_singleton_iff, BoundedFormula.realize_not]
    exact ⟨M.is_realization, hφ⟩

/-- A type is satisfiable iff it does not imply the falsum. -/
theorem satisfiable_iff_not_models_bot : IsSatisfiable p ↔ ¬ (p ⊨ᵇ ⊥) := by
  rw [iff_not_comm, models_iff_not_satisfiable, not_iff_not]
  constructor
  · intro ⟨M, hM⟩
    refine ⟨M, realize_mono hM Set.subset_union_left⟩
  · intro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    rw [realize_union_iff]
    refine ⟨hM, ?_⟩
    simp only [realize_singleton_iff, BoundedFormula.realize_not, BoundedFormula.realize_bot,
      not_false_eq_true]

/-- A standard application of the compactness theorem. A set of formulas `p` implies a formula `φ`
  iff there is a a finite subset `p0` of `p` that implies `φ`. -/
theorem models_iff_finset_models : p ⊨ᵇ φ ↔ ∃ (p0 : Finset (L.BoundedFormula α σ)),
    (p0 : L.FSet α σ) ⊆ p ∧ p0 ⊨ᵇ φ := by
  simp only [models_iff_not_satisfiable]
  rw [isSatisfiable_iff_isFinitelySatisfiable, IsFinitelySatisfiable]
  contrapose!
  letI := Classical.decEq (L.BoundedFormula α σ)
  constructor
  · intro h p0 hp0
    simpa using h (p0 ∪ {∼ φ})
      (by
        simp only [Finset.coe_union, Finset.coe_singleton]
        exact Set.union_subset_union hp0 (Set.Subset.refl _))
  · intro h p0 hp0
    exact IsSatisfiable.mono (h (p0.erase (∼ φ))
      (by simpa using hp0)) (by simp)


/-- A handy recurring lemma if `p ∪ A` implies some formula `φ`, and  `A` is finite, then
  `p` models the implication `⋀_{ψ ∈ A} ψ → φ`. -/
theorem union_finset_models_iff {A : Finset (L.BoundedFormula α σ)} :
    p ∪ A ⊨ᵇ φ ↔ p ⊨ᵇ BoundedFormula.iInf (fun (ψ : A) => ψ) ⟹ φ := by
  constructor
  · intro hpA M
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_iInf]
    intro hAM
    have hMpA : M ⊨ᵖ p ∪ A := by
      rw [realize_union_iff]
      refine ⟨M.is_realization, ?_⟩
      exact fun ψ hψ => hAM ⟨ψ, hψ⟩
    rw [models_iff] at hpA
    exact hpA ⟨M, hMpA⟩
  · intro hp ⟨M, hM⟩
    let ψ : L.BoundedFormula α σ := BoundedFormula.iInf (fun (ψ : A) => ψ)
    have hψ : ψ.Realize M.v M.x := by
      rw [BoundedFormula.realize_iInf]
      exact fun ψ => (realize_right hM) ψ.val ψ.prop
    have := hp ⟨M, realize_left hM⟩
    rw [BoundedFormula.realize_imp] at this
    exact this hψ


open scoped Classical in
/-- A version of `models_iff_finset_models` relative to an ambient set of formulas which is
  frequently useful in model-theoretic applications. -/
theorem union_models_iff_exists_finset_union_models : (q ∪ p ⊨ᵇ  φ) ↔
    ∃ (p0 : Finset (L.BoundedFormula α σ)), (p0 : L.FSet α σ) ⊆ p ∧ (q ∪ p0) ⊨ᵇ φ := by
  constructor
  · intro h
    rw [models_iff_finset_models] at h
    obtain ⟨r0, hsub, hmodels⟩ := h
    let p0 := r0.filter (· ∈ p)
    use p0
    refine ⟨?_, ?_⟩
    · grind --discharges the set-theoretic combinatorics
    · apply models_mono (q ∪ p0) hmodels
      grind
  · intro ⟨p0, hsub, hmodels⟩
    exact models_mono _ hmodels (Set.union_subset_union_right q hsub)


theorem union_singleton_models_iff_models_imp {ψ : L.BoundedFormula α σ} :
    (p ∪ {φ} ⊨ᵇ ψ ) ↔ p ⊨ᵇ φ ⟹ ψ := by
  constructor
  · intro h ⟨M, hM⟩
    rw [BoundedFormula.realize_imp]
    intro hφ
    refine h ⟨M, ?_⟩
    rw [realize_union_iff, realize_singleton_iff]
    exact ⟨hM, hφ⟩
  · intro h ⟨M, hM⟩
    rw [realize_union_iff, realize_singleton_iff] at hM
    have himp : (φ ⟹ ψ).Realize M.v M.x := h ⟨M, hM.1⟩
    rw [BoundedFormula.realize_imp] at himp
    exact himp hM.2



end Models

end FSet

end Language

end MSFirstOrder
