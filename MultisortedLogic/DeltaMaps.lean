/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Complexity
public import MultisortedLogic.ElementaryMaps

/-!
# Δ-types and Δ-maps

For a class of formulas `Δ`, the `Δ`-type of a tuple is the set of formulas of `Δ` it realizes,
and a `Δ`-map is a family of maps that preserves the formulas of `Δ`.

## Main definitions

* `Formula.typeOf Δ xs`: the `Δ`-type of a tuple.
* `DeltaMap Δ M N` (`M →[Δ]ᶠ N`): a family of maps preserving the formulas of `Δ`.

## Main results

* `Formula.typeOf_subset_iff_eq`: for a negation-closed class, one type contained in another is
  equal to it.
* `DeltaMap.toEmbedding`: a `Δ`-map for a class that is negation-closed and has the atomic formulas
  is an embedding. Conversely, embeddings are `Δ`-maps for the quantifier-free formulas
  (`Embedding.toDeltaMap`) and for the formulas quantifier-free relative to no sorts
  (`Embedding.toQFRelToEmptyMap`).
* `ElementaryEmbedding.toDeltaMap`, `DeltaMap.toElementaryEmbedding`: elementary embeddings are the
  `Δ`-maps for the class of all formulas.
-/

@[expose] public section

universe u v w w' w'' z

namespace ManySorted.Language

open Arity Structure

variable {S : Type z} {L : Language.{u, v} S}

open FormulaClass

/-! ### Δ-types -/

namespace Formula

variable {M : S → Type w} {N : S → Type w'} [L.Structure M] [L.Structure N] {σ : Arity S}

/-- The `Δ`-type of a tuple: the formulas of `Δ` that it realizes. -/
def typeOf (Δ : Set (L.Formula σ)) (xs : M [^] σ) : Set (L.Formula σ) := {φ ∈ Δ | φ.Realize xs}

@[simp]
theorem mem_typeOf {Δ : Set (L.Formula σ)} {xs : M [^] σ} {φ : L.Formula σ} :
    φ ∈ typeOf Δ xs ↔ φ ∈ Δ ∧ φ.Realize xs := Iff.rfl

theorem typeOf_subset (Δ : Set (L.Formula σ)) (xs : M [^] σ) : typeOf Δ xs ⊆ Δ :=
  fun _ h => h.1

/-! The bridge between statements about types and statements about the formulas in them. -/

section bridge

variable {Δ Δ' : Set (L.Formula σ)} {xs : M [^] σ} {ys : N [^] σ} {ψ : L.Formula σ}

theorem typeOf_subset_typeOf_iff :
    typeOf Δ xs ⊆ typeOf Δ ys ↔ ∀ ψ ∈ Δ, ψ.Realize xs → ψ.Realize ys :=
  ⟨fun h _ hψ hx => (h ⟨hψ, hx⟩).2, fun h ψ ⟨hψ, hx⟩ => ⟨hψ, h ψ hψ hx⟩⟩

theorem typeOf_eq_typeOf_iff :
    typeOf Δ xs = typeOf Δ ys ↔ ∀ ψ ∈ Δ, (ψ.Realize xs ↔ ψ.Realize ys) :=
  ⟨fun h ψ hψ => ⟨fun hx => ((Set.ext_iff.1 h ψ).1 ⟨hψ, hx⟩).2,
      fun hy => ((Set.ext_iff.1 h ψ).2 ⟨hψ, hy⟩).2⟩,
    fun h => Set.ext fun ψ =>
      ⟨fun ⟨hψ, hx⟩ => ⟨hψ, (h ψ hψ).1 hx⟩, fun ⟨hψ, hy⟩ => ⟨hψ, (h ψ hψ).2 hy⟩⟩⟩

theorem realize_of_typeOf_subset (h : typeOf Δ xs ⊆ typeOf Δ ys) (hψ : ψ ∈ Δ) :
    ψ.Realize xs → ψ.Realize ys :=
  typeOf_subset_typeOf_iff.1 h ψ hψ

theorem realize_iff_of_typeOf_eq (h : typeOf Δ xs = typeOf Δ ys) (hψ : ψ ∈ Δ) :
    ψ.Realize xs ↔ ψ.Realize ys :=
  typeOf_eq_typeOf_iff.1 h ψ hψ

/-- Equal types for a class give equal types for every smaller class. -/
theorem typeOf_eq_typeOf_of_subset (hΔ : Δ ⊆ Δ') (h : typeOf Δ' xs = typeOf Δ' ys) :
    typeOf Δ xs = typeOf Δ ys :=
  typeOf_eq_typeOf_iff.2 fun _ hψ => realize_iff_of_typeOf_eq h (hΔ hψ)

end bridge

/-- For a negation-closed class, one type contained in another is equal to it. -/
theorem typeOf_subset_iff_eq (Δ : L.FormulaClass) [NegClosed Δ] {xs : M [^] σ} {ys : N [^] σ} :
    typeOf (Δ σ) xs ⊆ typeOf (Δ σ) ys ↔ typeOf (Δ σ) xs = typeOf (Δ σ) ys :=
  ⟨fun h => subset_antisymm h fun _ ⟨hφ, hy⟩ =>
    ⟨hφ, by_contra fun hx => (h ⟨NegClosed.not_mem hφ, hx⟩).2 hy⟩, fun h => h.subset⟩

end Formula


open Formula

/-! ### Δ-maps -/

/-- A `Δ`-map: a family of maps that preserves the formulas of `Δ`. -/
structure DeltaMap (Δ : L.FormulaClass) (M : S → Type w) (N : S → Type w') [L.Structure M]
    [L.Structure N] where
  /-- The underlying family of maps. -/
  toFun : ∀ s, M s → N s
  map_formula' : ∀ {σ : Arity S} (φ : L.Formula σ), φ ∈ Δ σ →
    ∀ xs : M [^] σ, φ.Realize xs → φ.Realize (xs.map toFun)

@[inherit_doc] scoped[ManySorted] notation:25 A " →[" Δ "]ᶠ " B =>
  ManySorted.Language.DeltaMap Δ A B

namespace DeltaMap

variable {Δ Δ' : L.FormulaClass} {M : S → Type w} {N : S → Type w'} {P : S → Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P] {σ : Arity S}

instance : DFunLike (M →[Δ]ᶠ N) S fun s => M s → N s where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

@[simp]
theorem toFun_eq_coe (f : M →[Δ]ᶠ N) : f.toFun = ⇑f := rfl

/-- A `Δ`-map preserves the formulas of `Δ`. -/
theorem map_formula (f : M →[Δ]ᶠ N) {φ : L.Formula σ} (hφ : φ ∈ Δ σ) {xs : M [^] σ} :
    φ.Realize xs → φ.Realize (xs.map f) :=
  f.map_formula' φ hφ xs

/-- A `Δ`-map sends the `Δ`-type of a tuple into the `Δ`-type of its image. -/
theorem typeOf_subset (f : M →[Δ]ᶠ N) (xs : M [^] σ) :
    typeOf (Δ σ) xs ⊆ typeOf (Δ σ) (xs.map f) :=
  fun _ ⟨hφ, h⟩ => ⟨hφ, f.map_formula hφ h⟩

/-- A family of maps that sends the `Δ`-type of every tuple into the `Δ`-type of its image is a
`Δ`-map. -/
def ofTypeOfSubset (g : ∀ s, M s → N s)
    (h : ∀ (σ : Arity S) (xs : M [^] σ), typeOf (Δ σ) xs ⊆ typeOf (Δ σ) (xs.map g)) :
    M →[Δ]ᶠ N :=
  ⟨g, fun _ hφ xs hx => (h _ xs ⟨hφ, hx⟩).2⟩

@[simp]
theorem coe_ofTypeOfSubset (g : ∀ s, M s → N s)
    (h : ∀ (σ : Arity S) (xs : M [^] σ), typeOf (Δ σ) xs ⊆ typeOf (Δ σ) (xs.map g)) :
    ⇑(ofTypeOfSubset g h) = g := rfl

section NegClosed

variable [NegClosed Δ]

/-- For a negation-closed class, a `Δ`-map also reflects the formulas of `Δ`. -/
theorem map_formula_iff (f : M →[Δ]ᶠ N) {φ : L.Formula σ} (hφ : φ ∈ Δ σ) (xs : M [^] σ) :
    φ.Realize (xs.map f) ↔ φ.Realize xs :=
  ⟨fun h => by_contra fun hn => f.map_formula (NegClosed.not_mem hφ) hn h, f.map_formula hφ⟩

/-- For a negation-closed class, a `Δ`-map preserves `Δ`-types. -/
theorem typeOf_map (f : M →[Δ]ᶠ N) (xs : M [^] σ) :
    typeOf (Δ σ) (xs.map f) = typeOf (Δ σ) xs :=
  ((typeOf_subset_iff_eq Δ).1 (f.typeOf_subset xs)).symm

end NegClosed

variable (Δ M) in
/-- The identity is a `Δ`-map. -/
protected def id : M →[Δ]ᶠ M where
  toFun _ a := a
  map_formula' _ _ xs h := by rwa [Interpret.map_id']

/-- The composition of `Δ`-maps. -/
def comp (g : N →[Δ]ᶠ P) (f : M →[Δ]ᶠ N) : M →[Δ]ᶠ P where
  toFun s := g s ∘ f s
  map_formula' _ hφ xs h := by
    rw [← Interpret.map_map]
    exact g.map_formula hφ (f.map_formula hφ h)

@[simp]
theorem comp_apply (g : N →[Δ]ᶠ P) (f : M →[Δ]ᶠ N) (s : S) (a : M s) :
    g.comp f s a = g s (f s a) := rfl

/-- A `Δ`-map is a `Δ'`-map for every smaller class `Δ'`. -/
def mono (hΔ : ∀ σ, Δ' σ ⊆ Δ σ) (f : M →[Δ]ᶠ N) : M →[Δ']ᶠ N where
  toFun := f
  map_formula' _ hφ _ h := f.map_formula (hΔ _ hφ) h

@[simp]
theorem coe_mono (hΔ : ∀ σ, Δ' σ ⊆ Δ σ) (f : M →[Δ]ᶠ N) : ⇑(f.mono hΔ) = f := rfl

/-! #### Δ-maps that reflect the atomic formulas are embeddings -/

section Embedding

variable [HasAtomic Δ] [NegClosed Δ]

theorem map_fun (f : M →[Δ]ᶠ N) {σ : Arity S} {t : S} (g : L.Functions σ t) (x : M [^] σ) :
    f t (funMap g x) = funMap g (x.map f) := by
  have := (f.map_formula_iff (HasAtomic.atomic_mem (.equal
    (.func g (Term.vars (Interpret.ofFn fun _ i => .left i))) (.var (.right .var))))
    ((x, funMap (M := M) g x) : M [^] (σ ⨯ ⦃t⦄))).2
    (by simp [Interpret.map_ofFn, Function.comp_def])
  simpa [Interpret.map_ofFn, Function.comp_def, -Interpret.get_map] using this.symm

theorem map_rel (f : M →[Δ]ᶠ N) {σ : Arity S} (r : L.Relations σ) (x : M [^] σ) :
    RelMap r (x.map f) ↔ RelMap r x := by
  simpa [Interpret.map_ofFn, Function.comp_def, -Interpret.get_map] using
    f.map_formula_iff (HasAtomic.atomic_mem (.rel r (Term.vars (Interpret.ofFn fun _ i => i)))) x

theorem injective (f : M →[Δ]ᶠ N) (s : S) : Function.Injective (f s) := fun a b h =>
  (f.map_formula_iff (HasAtomic.atomic_mem (.equal (.var (.left .var)) (.var (.right .var))))
    ((a, b) : M [^] (⦃s⦄ ⨯ ⦃s⦄))).1 h

instance : StrongHomClass L (M →[Δ]ᶠ N) M N where
  map_fun := map_fun
  map_rel := map_rel

/-- A `Δ`-map for a class with the atomic formulas and closed under negation, as an embedding. -/
def toEmbedding (f : M →[Δ]ᶠ N) : M ↪[L] N where
  toEmbedding s := ⟨f s, f.injective s⟩
  map_fun' := f.map_fun
  map_rel' := f.map_rel

@[simp]
theorem coe_toEmbedding (f : M →[Δ]ᶠ N) : ⇑f.toEmbedding = f := rfl

end Embedding

end DeltaMap

/-- An embedding is a `Δ`-map for the quantifier-free formulas. -/
def Embedding.toDeltaMap {M : S → Type w} {N : S → Type w'} [L.Structure M] [L.Structure N]
    (g : M ↪[L] N) : M →[qf L]ᶠ N where
  toFun := g
  map_formula' _ hφ xs h := (StrongHomClass.realize_of_isQF g g.injective hφ xs).2 h

@[simp]
theorem Embedding.coe_toDeltaMap {M : S → Type w} {N : S → Type w'} [L.Structure M]
    [L.Structure N] (g : M ↪[L] N) : ⇑g.toDeltaMap = g := rfl

/-! ### Embeddings are the Δ-maps for formulas quantifier-free relative to no sorts -/

section QFRelToEmpty

variable {M : S → Type w} {N : S → Type w'} [L.Structure M] [L.Structure N]

/-- An embedding as a `Δ`-map for the formulas quantifier-free relative to no sorts. -/
def Embedding.toQFRelToEmptyMap (g : M ↪[L] N) : M →[FormulaClass.qfRelTo L ∅]ᶠ N where
  toFun := g
  map_formula' _ hφ xs h := (g.realize_of_isQFRelTo_empty hφ xs).2 h

@[simp]
theorem Embedding.coe_toQFRelToEmptyMap (g : M ↪[L] N) : ⇑g.toQFRelToEmptyMap = g := rfl

@[simp]
theorem Embedding.toQFRelToEmptyMap_toEmbedding (g : M ↪[L] N) :
    g.toQFRelToEmptyMap.toEmbedding = g :=
  DFunLike.coe_injective rfl

@[simp]
theorem DeltaMap.toEmbedding_toQFRelToEmptyMap (f : M →[FormulaClass.qfRelTo L ∅]ᶠ N) :
    f.toEmbedding.toQFRelToEmptyMap = f :=
  DFunLike.coe_injective rfl

end QFRelToEmpty

/-! ### Elementary embeddings and Δ-maps -/

namespace ElementaryEmbedding

variable {Δ : L.FormulaClass} {M : S → Type w} {N : S → Type w'} {P : S → Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P]

/-! #### Conversions to and from Δ-maps -/

variable (Δ) in
/-- An elementary embedding is a `Δ`-map for every class `Δ`. -/
def toDeltaMap (j : M ↪ₑ[L] N) : M →[Δ]ᶠ N :=
  ⟨j, fun φ _ xs h => (j.map_formula φ xs).2 h⟩

@[simp]
theorem coe_toDeltaMap (j : M ↪ₑ[L] N) : ⇑(j.toDeltaMap Δ) = j := rfl

end ElementaryEmbedding

/-- A `Δ`-map for a class containing all formulas is an elementary embedding. -/
def DeltaMap.toElementaryEmbedding {Δ : L.FormulaClass} {M : S → Type w} {N : S → Type w'}
    [L.Structure M] [L.Structure N] (hΔ : ∀ {σ : Arity S} (φ : L.Formula σ), φ ∈ Δ σ)
    (f : M →[Δ]ᶠ N) : M ↪ₑ[L] N :=
  ElementaryEmbedding.ofMapFormula f fun φ _ h => f.map_formula (hΔ φ) h

namespace ElementaryEmbedding

variable {Δ : L.FormulaClass} {M : S → Type w} {N : S → Type w'} {P : S → Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P]

@[simp]
theorem _root_.ManySorted.Language.DeltaMap.coe_toElementaryEmbedding
    (hΔ : ∀ {σ : Arity S} (φ : L.Formula σ), φ ∈ Δ σ) (f : M →[Δ]ᶠ N) :
    ⇑(f.toElementaryEmbedding hΔ) = f := rfl

@[simp]
theorem toDeltaMap_toElementaryEmbedding (hΔ : ∀ {σ : Arity S} (φ : L.Formula σ), φ ∈ Δ σ)
    (j : M ↪ₑ[L] N) : (j.toDeltaMap Δ).toElementaryEmbedding hΔ = j :=
  DFunLike.coe_injective rfl

@[simp]
theorem _root_.ManySorted.Language.DeltaMap.toElementaryEmbedding_toDeltaMap
    (hΔ : ∀ {σ : Arity S} (φ : L.Formula σ), φ ∈ Δ σ) (f : M →[Δ]ᶠ N) :
    (f.toElementaryEmbedding hΔ).toDeltaMap Δ = f :=
  DFunLike.coe_injective rfl

/-! #### The API of elementary embeddings -/

/-- Elementary embeddings preserve complete types. -/
theorem typeOf_map (j : M ↪ₑ[L] N) {σ : Arity S} (xs : M [^] σ) :
    typeOf (all L σ) (xs.map j) = typeOf (all L σ) xs :=
  (j.toDeltaMap (all L)).typeOf_map xs

end ElementaryEmbedding

end ManySorted.Language
