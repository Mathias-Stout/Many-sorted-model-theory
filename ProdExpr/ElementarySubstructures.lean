/-
Based on the corresponding Mathlib file by Aaron Anderson
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProdExpr.ElementaryMapsMS

/-!
# Elementary Substructures

## Main Definitions

- A `MSFirstOrder.MSLanguage.ElementarySubstructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.

## Main Results

- The Tarski-Vaught Test for substructures:
  `MSFirstOrder.MSLanguage.Substructure.isElementary_of_exists` gives a simple criterion for a
  substructure to be elementary.
-/

universe u v z w

open MSFirstOrder

namespace MSFirstOrder

namespace MSLanguage

open MSStructure
variable {Sorts : Type z}
variable {L : MSLanguage.{u, v, z} Sorts} {M : Fam.{w} Sorts} [L.MSStructure M]

/-- A substructure is elementary when every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
def Substructure.IsElementary (S : L.Substructure M) : Prop :=
  ∀ ⦃σ : Signature Sorts⦄ (φ : L.BoundedFormula Fam.EmptyFam σ) (x : S[^]σ),
      φ.Realize default (x : M[^]σ) ↔ φ.Realize default x

variable (L M)

/-- An elementary substructure is one in which every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
structure ElementarySubstructure where
  /-- The underlying substructure -/
  toSubstructure : L.Substructure M
  isElementary' : toSubstructure.IsElementary

variable {L M}

namespace ElementarySubstructure

attribute [coe] toSubstructure

instance instCoe : Coe (L.ElementarySubstructure M) (L.Substructure M) :=
  ⟨ElementarySubstructure.toSubstructure⟩

instance instDepSetLike : DepSetLike (L.ElementarySubstructure M) M where
  toDepSet S := (S.toSubstructure : DepSet M)
  toDepSet_injective := by
    intro S T h
    have hsub : S.toSubstructure = T.toSubstructure := by
      exact (DepSetLike.toDepSet_injective (F := L.Substructure M) (α := M)) h
    cases S
    cases T
    cases hsub
    simp

/-- The underlying family of a bundled elementary substructure. -/
abbrev Subtype (S : L.ElementarySubstructure M) : Fam Sorts :=
  (S.toSubstructure).Subtype

instance inducedMSStructure (S : L.ElementarySubstructure M) : L.MSStructure S :=
  Substructure.inducedStructure (S := (S : L.Substructure M))

@[simp]
theorem isElementary (S : L.ElementarySubstructure M) : (S : L.Substructure M).IsElementary :=
  S.isElementary'

/-- The natural embedding of an `L.Substructure` of `M` into `M`. -/
def subtype (S : L.ElementarySubstructure M) : S ↪ₑ[L] M where
  toFun := ⟨fun s (x : S.Subtype s) => x.1⟩
  map_boundedFormula' := by
    intro σ φ x
    simpa using (S.isElementary (σ := σ) φ x)

@[simp]
theorem subtype_apply {S : L.ElementarySubstructure M} {s : Sorts} (x : S.Subtype s) :
    subtype S s x = x.1 :=
  rfl

theorem subtype_injective (S : L.ElementarySubstructure M) (s : Sorts) :
    Function.Injective (subtype S s) := by
  intro x y h
  exact Subtype.ext h

/-- The substructure `M` of the structure `M` is elementary. -/
instance instTop : Top (L.ElementarySubstructure M) :=
  ⟨⟨⊤, by
      intro σ φ x
      letI : L.MSStructure ((⊤ : L.Substructure M).Subtype) :=
        Substructure.inducedStructure (S := (⊤ : L.Substructure M))
      let mapx : M[^]σ := ((⊤ : DepSet M).subtypeVal <$>ₛ x)
      let vTop : Fam.EmptyFam →ₛ M :=
        (Fam.FamMapClass.toFamMap
          (⇑((((⊤ : DepSet M).subtypeVal) ∘ₛ
            (default : Fam.EmptyFam →ₛ (⊤ : L.Substructure M).Subtype)))))
      have htop :
          φ.Realize (default : Fam.EmptyFam →ₛ (⊤ : L.Substructure M).Subtype) x ↔
            φ.Realize vTop mapx :=
          (Substructure.realize_boundedFormula_top (L := L) (M := M) (φ := φ)
            (v := (default : Fam.EmptyFam →ₛ (⊤ : L.Substructure M).Subtype)) (xs := x))
      have hv : vTop = (default : Fam.EmptyFam →ₛ M) := by
        ext s a
        cases a
      have hleft :
          φ.Realize (default : Fam.EmptyFam →ₛ M) mapx ↔ φ.Realize vTop mapx := by
        simp [hv]
      simpa [mapx] using (hleft.trans htop.symm)
      ⟩⟩


instance instInhabited : Inhabited (L.ElementarySubstructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top {s : Sorts} (x : M s) :
    x ∈ (((⊤ : L.ElementarySubstructure M) : L.Substructure M) s) := by
  simpa only [DepSetLike.carrier_toDepSet] using
    (Substructure.mem_top (L := L) (M := M) (s := s) x)

@[simp]
theorem top_apply (s : Sorts) :
    ((((⊤ : L.ElementarySubstructure M) : L.Substructure M) s)) = Set.univ := by
  rfl

@[simp]
theorem realize_sentence (S : L.ElementarySubstructure M) (φ : L.Sentence) :
    S ⊨ φ ↔ M ⊨ φ :=
  S.subtype.map_sentence φ

@[simp]
theorem theory_model_iff (S : L.ElementarySubstructure M) (T : L.Theory) :
    S ⊨ T ↔ M ⊨ T := by
  simp only [Theory.model_iff, realize_sentence]

instance theory_model {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M} :
    S ⊨ T :=
  (theory_model_iff S T).2 h

theorem elementarilyEquivalent (S : L.ElementarySubstructure M) : S ≅[L] M :=
  S.subtype.elementarilyEquivalent

end ElementarySubstructure

namespace Substructure

/-- The Tarski-Vaught test for elementarity of a substructure. -/
theorem isElementary_of_exists (S : L.Substructure M)
    (htv :
      ∀ (s : Sorts) (σ : Signature Sorts)
        (φ : L.BoundedFormula Fam.EmptyFam (σ.prod (.of s)))
        (xs : S [^] σ) (a : M s),
          φ.Realize default ⟨S.subtype <$>ₛ xs, a⟩ →
            ∃ b : S s, φ.Realize default ⟨S.subtype <$>ₛ xs, S.subtype s b⟩) :
    S.IsElementary := by
  intro σ φ xs
  simpa only [Signature.Interpret.mapClass_eq_map] using
    (S.subtype.isElementary_of_exists htv (σ := σ) (φ := φ) (xs := xs))

/-- Bundles a substructure satisfying the Tarski-Vaught test as an elementary substructure. -/
@[simps]
def toElementarySubstructure (S : L.Substructure M)
    (htv :
      ∀ (s : Sorts) (σ : Signature Sorts)
        (φ : L.BoundedFormula Fam.EmptyFam (σ.prod (.of s)))
        (xs : S [^] σ) (a : M s),
          φ.Realize default ⟨S.subtype <$>ₛ xs, a⟩ →
            ∃ b : S s, φ.Realize default ⟨S.subtype <$>ₛ xs, S.subtype s b⟩) :
    L.ElementarySubstructure M :=
  ⟨S, S.isElementary_of_exists htv⟩

end Substructure

end MSLanguage

end MSFirstOrder
