/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Basic

/-!
# Composition, identity and inverses of maps of structures

Homomorphisms, embeddings and equivalences of `L`-structures form categories, and equivalences have
inverses. This file also defines the empty language, for which every family of maps is a
homomorphism.

## Main declarations

* `HomClass.map_constants`: maps of structures fix the constants.
* `Hom.id`, `Hom.comp`; `Embedding.refl`, `Embedding.comp`, `Embedding.toHom`; `Equiv.refl`,
  `Equiv.comp`, `Equiv.symm`, `Equiv.toEmbedding`, `Equiv.toHom`, with the usual identities.
* `Language.empty`, the language without symbols, with the structure `emptyStructure` on every
  family.

## References

This file was originally based on `Mathlib/ModelTheory/Basic.lean`, by Aaron Anderson, Jesse Michael
Han and Floris van Doorn.
-/

@[expose] public section

universe u v w w' w₁ w₂ z

namespace ManySorted

open Arity

namespace Language

open Structure

variable {S : Type z} {L : Language.{u, v} S}
  {M : S → Type w} {N : S → Type w'} {P : S → Type w₁} {Q : S → Type w₂}
  [L.Structure M] [L.Structure N] [L.Structure P] [L.Structure Q]

/-! ### Constants -/

/-- Maps of structures fix the constants. -/
@[simp]
theorem HomClass.map_constants {F : Type*} [DFunLike F S fun s => M s → N s] [HomClass L F M N]
    (φ : F) {t : S} (c : L.Constants t) :
    φ t (funMap c PUnit.unit) = funMap (M := N) c PUnit.unit :=
  HomClass.map_fun φ c PUnit.unit

/-! ### Homomorphisms -/

namespace Hom

@[simp]
theorem toFun_eq_coe (φ : M →[L] N) : φ.toFun = ⇑φ :=
  rfl

@[ext]
theorem ext {φ ψ : M →[L] N} (h : ∀ s x, φ s x = ψ s x) : φ = ψ :=
  DFunLike.ext _ _ fun s => funext (h s)

theorem map_fun (φ : M →[L] N) {σ : Arity S} {t : S} (f : L.Functions σ t) (x : M [^] σ) :
    φ t (funMap f x) = funMap f (x.map φ) :=
  HomClass.map_fun φ f x

theorem map_rel (φ : M →[L] N) {σ : Arity S} (r : L.Relations σ) (x : M [^] σ) :
    RelMap r x → RelMap r (x.map φ) :=
  HomClass.map_rel φ r x

variable (L M) in
/-- The identity homomorphism. -/
protected def id : M →[L] M where
  toFun _ := id
  map_fun' _ x := (congrArg (funMap _) (Interpret.map_id x)).symm
  map_rel' _ x h := (Interpret.map_id x).symm ▸ h

@[simp]
theorem id_apply {s : S} (x : M s) : Hom.id L M s x = x :=
  rfl

/-- The composition of homomorphisms. -/
def comp (g : N →[L] P) (f : M →[L] N) : M →[L] P where
  toFun s := g s ∘ f s
  map_fun' h x := by
    change g _ (f _ (funMap h x)) = funMap h (x.map fun s => g s ∘ f s)
    rw [f.map_fun, g.map_fun, Interpret.map_map]
  map_rel' r x hx := by
    rw [← Interpret.map_map]
    exact g.map_rel r _ (f.map_rel r x hx)

@[simp]
theorem comp_apply (g : N →[L] P) (f : M →[L] N) {s : S} (x : M s) :
    g.comp f s x = g s (f s x) :=
  rfl

theorem comp_assoc (h : P →[L] Q) (g : N →[L] P) (f : M →[L] N) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_id (f : M →[L] N) : f.comp (Hom.id L M) = f :=
  rfl

@[simp]
theorem id_comp (f : M →[L] N) : (Hom.id L N).comp f = f :=
  rfl

end Hom

/-! ### Embeddings -/

namespace Embedding

@[ext]
theorem ext {φ ψ : M ↪[L] N} (h : ∀ s x, φ s x = ψ s x) : φ = ψ :=
  DFunLike.ext _ _ fun s => funext (h s)

theorem map_fun (φ : M ↪[L] N) {σ : Arity S} {t : S} (f : L.Functions σ t) (x : M [^] σ) :
    φ t (funMap f x) = funMap f (x.map φ) :=
  StrongHomClass.map_fun φ f x

theorem map_rel (φ : M ↪[L] N) {σ : Arity S} (r : L.Relations σ) (x : M [^] σ) :
    RelMap r (x.map φ) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- An embedding as a homomorphism. -/
def toHom (φ : M ↪[L] N) : M →[L] N :=
  HomClass.toHom φ

@[simp]
theorem coe_toHom (φ : M ↪[L] N) : ⇑φ.toHom = ⇑φ :=
  rfl

theorem toHom_injective : Function.Injective (toHom : (M ↪[L] N) → M →[L] N) :=
  fun _ _ h => DFunLike.coe_injective (congrArg DFunLike.coe h :)

variable (L M) in
/-- The identity embedding. -/
def refl : M ↪[L] M where
  toEmbedding s := Function.Embedding.refl (M s)
  map_fun' f x := (congrArg (funMap f) (Interpret.map_id x)).symm
  map_rel' r x := Iff.of_eq (congrArg (RelMap r) (Interpret.map_id x))

@[simp]
theorem refl_apply {s : S} (x : M s) : refl L M s x = x :=
  rfl

/-- The composition of embeddings. -/
def comp (g : N ↪[L] P) (f : M ↪[L] N) : M ↪[L] P where
  toEmbedding s := (f.toEmbedding s).trans (g.toEmbedding s)
  map_fun' h x := by
    change g _ (f _ (funMap h x)) = funMap h (x.map fun s => g s ∘ f s)
    rw [f.map_fun, g.map_fun, Interpret.map_map]
  map_rel' r x := by
    change RelMap r (x.map fun s => g s ∘ f s) ↔ RelMap r x
    rw [← Interpret.map_map, g.map_rel, f.map_rel]

@[simp]
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) {s : S} (x : M s) :
    g.comp f s x = g s (f s x) :=
  rfl

theorem comp_assoc (h : P ↪[L] Q) (g : N ↪[L] P) (f : M ↪[L] N) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_refl (f : M ↪[L] N) : f.comp (refl L M) = f :=
  rfl

@[simp]
theorem refl_comp (f : M ↪[L] N) : (refl L N).comp f = f :=
  rfl

@[simp]
theorem comp_toHom (g : N ↪[L] P) (f : M ↪[L] N) : (g.comp f).toHom = g.toHom.comp f.toHom :=
  rfl

@[simp]
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

end Embedding

/-! ### Equivalences -/

namespace Equiv

@[ext]
theorem ext {φ ψ : M ≃[L] N} (h : ∀ s x, φ s x = ψ s x) : φ = ψ :=
  DFunLike.ext _ _ fun s => funext (h s)

theorem map_fun (φ : M ≃[L] N) {σ : Arity S} {t : S} (f : L.Functions σ t) (x : M [^] σ) :
    φ t (funMap f x) = funMap f (x.map φ) :=
  StrongHomClass.map_fun φ f x

theorem map_rel (φ : M ≃[L] N) {σ : Arity S} (r : L.Relations σ) (x : M [^] σ) :
    RelMap r (x.map φ) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- Mapping a tuple by the inverse equivalences and then by `φ` gives it back. -/
theorem map_map_symm (φ : M ≃[L] N) {σ : Arity S} (x : N [^] σ) :
    (x.map fun s => (φ.toEquiv s).symm).map φ = x := by
  rw [Interpret.map_map]
  exact (congrArg (Interpret.map · x) (funext fun s => funext fun a =>
    (φ.toEquiv s).apply_symm_apply a)).trans (Interpret.map_id x)

/-- The inverse of an equivalence. -/
def symm (φ : M ≃[L] N) : N ≃[L] M where
  toEquiv s := (φ.toEquiv s).symm
  map_fun' f x := (φ.toEquiv _).injective <| by
    rw [_root_.Equiv.apply_symm_apply]
    change funMap f x = φ _ (funMap f (x.map fun s => (φ.toEquiv s).symm))
    rw [φ.map_fun, φ.map_map_symm]
  map_rel' r x := by
    rw [← φ.map_rel, φ.map_map_symm]

@[simp]
theorem apply_symm_apply (φ : M ≃[L] N) {s : S} (x : N s) : φ s (φ.symm s x) = x :=
  (φ.toEquiv s).apply_symm_apply x

@[simp]
theorem symm_apply_apply (φ : M ≃[L] N) {s : S} (x : M s) : φ.symm s (φ s x) = x :=
  (φ.toEquiv s).symm_apply_apply x

@[simp]
theorem symm_symm (φ : M ≃[L] N) : φ.symm.symm = φ :=
  rfl

theorem bijective (φ : M ≃[L] N) (s : S) : Function.Bijective (φ s) :=
  (φ.toEquiv s).bijective

/-- An equivalence as an embedding. -/
def toEmbedding (φ : M ≃[L] N) : M ↪[L] N :=
  StrongHomClass.toEmbedding' (fun ψ : M ≃[L] N => ψ.injective) φ

/-- An equivalence as a homomorphism. -/
def toHom (φ : M ≃[L] N) : M →[L] N :=
  HomClass.toHom φ

@[simp]
theorem coe_toEmbedding (φ : M ≃[L] N) : ⇑φ.toEmbedding = ⇑φ :=
  rfl

@[simp]
theorem coe_toHom (φ : M ≃[L] N) : ⇑φ.toHom = ⇑φ :=
  rfl

@[simp]
theorem toEmbedding_toHom (φ : M ≃[L] N) : φ.toEmbedding.toHom = φ.toHom :=
  rfl

variable (L M) in
/-- The identity equivalence. -/
def refl : M ≃[L] M where
  toEquiv s := _root_.Equiv.refl (M s)
  map_fun' f x := (congrArg (funMap f) (Interpret.map_id x)).symm
  map_rel' r x := Iff.of_eq (congrArg (RelMap r) (Interpret.map_id x))

@[simp]
theorem refl_apply {s : S} (x : M s) : refl L M s x = x :=
  rfl

/-- The composition of equivalences. -/
def comp (g : N ≃[L] P) (f : M ≃[L] N) : M ≃[L] P where
  toEquiv s := (f.toEquiv s).trans (g.toEquiv s)
  map_fun' h x := by
    change g _ (f _ (funMap h x)) = funMap h (x.map fun s => g s ∘ f s)
    rw [f.map_fun, g.map_fun, Interpret.map_map]
  map_rel' r x := by
    change RelMap r (x.map fun s => g s ∘ f s) ↔ RelMap r x
    rw [← Interpret.map_map, g.map_rel, f.map_rel]

@[simp]
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) {s : S} (x : M s) :
    g.comp f s x = g s (f s x) :=
  rfl

theorem comp_assoc (h : P ≃[L] Q) (g : N ≃[L] P) (f : M ≃[L] N) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_refl (f : M ≃[L] N) : f.comp (refl L M) = f :=
  rfl

@[simp]
theorem refl_comp (f : M ≃[L] N) : (refl L N).comp f = f :=
  rfl

@[simp]
theorem symm_comp_self (f : M ≃[L] N) : f.symm.comp f = refl L M :=
  ext fun _ => f.symm_apply_apply

@[simp]
theorem self_comp_symm (f : M ≃[L] N) : f.comp f.symm = refl L N :=
  ext fun _ => f.apply_symm_apply

theorem comp_symm (g : N ≃[L] P) (f : M ≃[L] N) : (g.comp f).symm = f.symm.comp g.symm :=
  rfl

@[simp]
theorem comp_toEmbedding (g : N ≃[L] P) (f : M ≃[L] N) :
    (g.comp f).toEmbedding = g.toEmbedding.comp f.toEmbedding :=
  rfl

@[simp]
theorem refl_toEmbedding : (refl L M).toEmbedding = Embedding.refl L M :=
  rfl

end Equiv

/-! ### Structures transported along equivalences -/

section Induced

variable {A : S → Type w₁} {B : S → Type w₂} [L.Structure A] (e : ∀ s, A s ≃ B s)

theorem _root_.ManySorted.Arity.Interpret.map_symm_map {σ : Arity S} (x : A [^] σ) :
    (x.map fun s => e s).map (fun s => (e s).symm) = x := by
  rw [Interpret.map_map]
  exact (congrArg (Interpret.map · x) (funext fun s => funext fun a =>
    (e s).symm_apply_apply a)).trans (Interpret.map_id x)

variable (L) in
/-- The `L`-structure on `B` transported from `A` along a family of equivalences. -/
@[instance_reducible]
def Equiv.inducedStructure : L.Structure B where
  funMap f x := e _ (funMap f (x.map fun s => (e s).symm))
  RelMap R x := RelMap R (x.map fun s => (e s).symm)

/-- A family of equivalences, as an isomorphism onto the transported structure. -/
def Equiv.inducedStructureEquiv :
    @Language.Equiv _ L A B _ (Equiv.inducedStructure L e) :=
  let := Equiv.inducedStructure L e
  { toEquiv := e
    map_fun' := fun f x => by
      change e _ (funMap f x) = e _ (funMap f ((x.map fun s => e s).map fun s => (e s).symm))
      rw [Interpret.map_symm_map]
    map_rel' := fun R x => by
      change RelMap R ((x.map fun s => e s).map fun s => (e s).symm) ↔ RelMap R x
      rw [Interpret.map_symm_map] }

end Induced

/-! ### The empty language -/

/-- The language without function or relation symbols. -/
protected def empty : Language.{u, v} S :=
  ⟨fun _ _ => PEmpty, fun _ => PEmpty⟩

instance isEmpty_empty_functions {σ : Arity S} {t : S} :
    IsEmpty ((Language.empty : Language.{u, v} S).Functions σ t) :=
  inferInstanceAs (IsEmpty PEmpty)

instance isEmpty_empty_relations {σ : Arity S} :
    IsEmpty ((Language.empty : Language.{u, v} S).Relations σ) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- Every family carries the structure of the empty language. -/
instance emptyStructure (M : S → Type w) : (Language.empty : Language.{u, v} S).Structure M where
  funMap f := isEmptyElim f
  RelMap r := isEmptyElim r

/-- Every family of maps is a homomorphism for the empty language. -/
def Hom.ofEmpty (f : ∀ s, M s → N s) : M →[(Language.empty : Language.{u, v} S)] N where
  toFun := f
  map_fun' g := isEmptyElim g
  map_rel' r := isEmptyElim r

end Language

end ManySorted
