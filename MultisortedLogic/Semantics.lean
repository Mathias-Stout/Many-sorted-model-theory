/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Complexity
public import Mathlib.Data.Set.Image

/-!
# Many-sorted first-order logic: semantics

The realization of terms and formulas in a structure, models of theories, and the basic
consequences: realization of relabelled and substituted formulas, and invariance of realization
under embeddings and equivalences.

## Main declarations

* `Term.realize`, `Formula.Realize`, `Sentence.Realize` (`M ⊨ φ`), `Theory.Model` (`M ⊨ T`),
  `Theory.ModelsFormula` (`T ⊨ᵇ φ`).
* `Formula.realize_relabel`: a relabelled formula holds of `xs` iff the formula holds of the
  pulled-back tuple `xs.comap g`. Together with the `Interpret.comap` lemmas for the `Idx`
  combinators (`comap_left`, `comap_extendRight`, `comap_assoc`, …), `simp` computes such
  pullbacks. `Formula.realize_relabel_of_get_eq` is the entrywise version, with a hypothesis
  `∀ s i, ys.get s i = xs.get s (g s i)` proved position by position. It is needed where the
  tuple's type is only definitionally a product, as in the named layer, where `simp` cannot see
  through `(ψ₁.imp ψ₂).ctx`.
* `Formula.realize_subst`: substituting a tuple of terms `r` realizes as `φ.Realize (r.realize xs)`.
* `Embedding.realize_of_isQF`, `Equiv.realize_formula`: embeddings preserve and reflect
  quantifier-free formulas, and equivalences all formulas.
* `StrongHomClass.realize_of_isQFRelTo`: an injective strong homomorphism that is onto on the
  sorts of `R` preserves and reflects the formulas quantifier-free relative to `R`.
* `Formula.realize_iff_of_isQFRelTo_empty`: tuples that agree on the atomic formulas agree on the
  formulas quantifier-free relative to no sorts.

## References

This file was originally based on `Mathlib/ModelTheory/Semantics.lean`, by Aaron Anderson, Jesse
Michael Han and Floris van Doorn.
-/

@[expose] public section

universe u v w w' z

namespace ManySorted

open Arity

namespace Language

open Structure

variable {S : Type z} {L : Language.{u, v} S} {Γ Γ' : Arity S} {M : S → Type w} [L.Structure M]

/-! ### Realization of terms -/

namespace Term

/-- Evaluate a tuple of terms at a tuple of values for its context. -/
def realize (xs : M [^] Γ) : ∀ {σ}, L.Term Γ σ → M [^] σ
  | _, var i => xs.get _ i
  | _, func f ts => funMap (M := M) f (ts.realize xs)
  | _, nil => PUnit.unit
  | _, prod t₁ t₂ => (t₁.realize xs, t₂.realize xs)

section realize

variable (xs : M [^] Γ)


@[simp]
theorem realize_var {s : S} (i : Γ.Idx s) : (var i : L.Term Γ s).realize xs = xs.get s i := rfl

@[simp]
theorem realize_func {σ : Arity S} {t : S} (f : L.Functions σ t) (ts : L.Term Γ σ) :
    (func f ts).realize xs = funMap f (ts.realize xs) := rfl

@[simp]
theorem realize_nil : (nil : L.Term Γ ⦃⦄).realize xs = PUnit.unit := rfl

@[simp]
theorem realize_prod {σ τ : Arity S} (t₁ : L.Term Γ σ) (t₂ : L.Term Γ τ) :
    (prod t₁ t₂).realize xs = (t₁.realize xs, t₂.realize xs) := rfl

@[simp]
theorem realize_vars (xs : M [^] Γ) :
    ∀ {σ : Arity S} (x : Γ.Idx [^] σ), (vars x : L.Term Γ σ).realize xs = x.map xs.get
  | .nil, _ => rfl
  | .of _, _ => rfl
  | .prod _ _, x => congrArg₂ Prod.mk (realize_vars xs x.1) (realize_vars xs x.2)

end realize

/-- Realizing a relabelled term, entrywise. Prefer `realize_relabel`; this form is for tuples
whose type `simp` cannot see as a product (see the module docstring). -/
theorem realize_relabel_of_get_eq {g : ∀ s, Γ.Idx s → Γ'.Idx s} {xs : M [^] Γ'} {ys : M [^] Γ}
    (h : ∀ s i, ys.get s i = xs.get s (g s i)) {σ : Arity S} (t : L.Term Γ σ) :
    (t.relabel g).realize xs = t.realize ys := by
  induction t with
  | var i => exact (h _ i).symm
  | func f ts ih => simp only [relabel, realize_func, ih]
  | nil => rfl
  | prod t₁ t₂ ih₁ ih₂ => simp only [relabel, realize_prod, ih₁, ih₂]

@[simp]
theorem realize_relabel (g : ∀ s, Γ.Idx s → Γ'.Idx s) (xs : M [^] Γ') {σ : Arity S}
    (t : L.Term Γ σ) : (t.relabel g).realize xs = t.realize (xs.comap g) :=
  realize_relabel_of_get_eq (fun s i => Interpret.get_comap g xs s i) t

@[simp]
theorem realize_get (xs : M [^] Γ) :
    ∀ {σ} (t : L.Term Γ σ) (s : S) (i : σ.Idx s), (t.get s i).realize xs = (t.realize xs).get s i
  | _, t, _, .var => by cases t <;> rfl
  | _, prod t _, _, .left i => realize_get xs t _ i
  | _, prod _ u, _, .right j => realize_get xs u _ j

@[simp]
theorem realize_subst (xs : M [^] Γ') :
    ∀ {σ} (t : L.Term Γ σ) (r : L.Term Γ' Γ), (t.subst r).realize xs = t.realize (r.realize xs)
  | _, var i, r => realize_get xs r _ i
  | _, func f ts, r => by simp only [subst, realize_func, realize_subst xs ts r]
  | _, nil, _ => rfl
  | _, prod t₁ t₂, r => by simp only [subst, realize_prod, realize_subst xs t₁, realize_subst xs t₂]

@[simp]
theorem realize_extendSubst {ρ : Arity S} (r : L.Term Γ' Γ) (xs : M [^] Γ')
    (zs : M [^] ρ) :
    (r.extendSubst (ρ := ρ)).realize ((xs, zs) : M [^] (Γ' ⨯ ρ)) = (r.realize xs, zs) := by
  simp [extendSubst, Interpret.map_ofFn, Function.comp_def]

end Term

/-! ### Realization of formulas -/

namespace Formula

variable {σ τ : Arity S}

/-- Evaluate a formula `φ` at a tuple `xs`: `φ(xs)`. -/
def Realize : ∀ {σ}, L.Formula σ → M [^] σ → Prop
  | _, falsum, _ => False
  | _, equal t₁ t₂, xs => t₁.realize xs = t₂.realize xs
  | _, rel R ts, xs => RelMap R (ts.realize xs)
  | _, imp φ ψ, xs => φ.Realize xs → ψ.Realize xs
  | _, all _ φ, xs => ∀ ys, φ.Realize (xs, ys)

section realize

variable {φ ψ : L.Formula σ} {xs : M [^] σ}

@[simp]
theorem realize_falsum : (falsum : L.Formula σ).Realize xs ↔ False := Iff.rfl

@[simp]
theorem realize_bot : (⊥ : L.Formula σ).Realize xs ↔ False := Iff.rfl

@[simp]
theorem realize_equal {τ : Arity S} (t₁ t₂ : L.Term σ τ) :
    (equal t₁ t₂).Realize xs ↔ t₁.realize xs = t₂.realize xs := Iff.rfl

@[simp]
theorem realize_rel {τ : Arity S} (R : L.Relations τ) (ts : L.Term σ τ) :
    (rel R ts).Realize xs ↔ RelMap R (ts.realize xs) := Iff.rfl

@[simp]
theorem realize_imp : (φ.imp ψ).Realize xs ↔ (φ.Realize xs → ψ.Realize xs) := Iff.rfl

@[simp]
theorem realize_all {φ : L.Formula (σ ⨯ τ)} :
    (all τ φ).Realize xs ↔ ∀ ys : M [^] τ, φ.Realize (xs, ys) := Iff.rfl

@[simp]
theorem realize_not : φ.not.Realize xs ↔ ¬φ.Realize xs := Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.Formula σ).Realize xs ↔ True :=
  ⟨fun _ => trivial, fun _ => id⟩

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize xs ↔ φ.Realize xs ∧ ψ.Realize xs := by
  simp only [min, realize_not, realize_imp, not_imp, not_not]

@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize xs ↔ φ.Realize xs ∨ ψ.Realize xs := by
  simp only [max]
  tauto

@[simp]
theorem realize_iff : (φ.iff ψ).Realize xs ↔ (φ.Realize xs ↔ ψ.Realize xs) := by
  simp only [Formula.iff, realize_inf, realize_imp]
  tauto

@[simp]
theorem realize_ex {φ : L.Formula (σ ⨯ τ)} :
    (φ.ex τ).Realize xs ↔ ∃ ys : M [^] τ, φ.Realize (xs, ys) := by simp [Formula.ex]

end realize

section finite

variable {β : Type*} {xs : M [^] σ}

theorem realize_foldr_inf (l : List (L.Formula σ)) :
    (l.foldr (· ⊓ ·) ⊤).Realize xs ↔ ∀ φ ∈ l, φ.Realize xs := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

theorem realize_foldr_sup (l : List (L.Formula σ)) :
    (l.foldr (· ⊔ ·) ⊥).Realize xs ↔ ∃ φ ∈ l, φ.Realize xs := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

@[simp]
theorem realize_iInf (s : Finset β) (f : β → L.Formula σ) :
    (iInf s f).Realize xs ↔ ∀ b ∈ s, (f b).Realize xs := by
  simp [iInf, realize_foldr_inf]

@[simp]
theorem realize_iSup (s : Finset β) (f : β → L.Formula σ) :
    (iSup s f).Realize xs ↔ ∃ b ∈ s, (f b).Realize xs := by
  simp [iSup, realize_foldr_sup]

end finite

/-! ### Relabelling and substitution -/

/-- Realizing a relabelled formula, entrywise. Prefer `realize_relabel`; this form is for tuples
whose type `simp` cannot see as a product (see the module docstring). -/
theorem realize_relabel_of_get_eq : ∀ {σ τ : Arity S} {g : ∀ s, σ.Idx s → τ.Idx s}
    (φ : L.Formula σ) {xs : M [^] τ} {ys : M [^] σ},
    (∀ s i, ys.get s i = xs.get s (g s i)) → ((φ.relabel g).Realize xs ↔ φ.Realize ys)
  | _, _, _, falsum, _, _, _ => Iff.rfl
  | _, _, _, equal t₁ t₂, _, _, h => by
      simp only [relabel, realize_equal, Term.realize_relabel_of_get_eq h]
  | _, _, _, rel R ts, _, _, h => by
      simp only [relabel, realize_rel, Term.realize_relabel_of_get_eq h]
  | _, _, _, imp φ ψ, _, _, h => by
      simp only [relabel, realize_imp, realize_relabel_of_get_eq φ h, realize_relabel_of_get_eq ψ h]
  | _, _, _, all _ φ, _, _, h => by
      simp only [relabel, realize_all]
      refine forall_congr' fun zs => realize_relabel_of_get_eq φ ?_
      intro s i
      cases i with
      | left i => exact h s i
      | right j => rfl

@[simp]
theorem realize_relabel {g : ∀ s, σ.Idx s → τ.Idx s} {φ : L.Formula σ}
    {xs : M [^] τ} : (φ.relabel g).Realize xs ↔ φ.Realize (xs.comap g) :=
  realize_relabel_of_get_eq φ fun s i => Interpret.get_comap g xs s i

@[simp]
theorem realize_subst : ∀ {σ τ : Arity S} (φ : L.Formula σ) (r : L.Term τ σ)
    (xs : M [^] τ), (φ.subst r).Realize xs ↔ φ.Realize (r.realize xs)
  | _, _, falsum, _, _ => Iff.rfl
  | _, _, equal _ _, _, _ => by simp only [subst, realize_equal, Term.realize_subst]
  | _, _, rel _ _, _, _ => by simp only [subst, realize_rel, Term.realize_subst]
  | _, _, imp φ ψ, r, xs => by
      simp only [subst, realize_imp, realize_subst φ r xs, realize_subst ψ r xs]
  | _, _, all _ φ, r, xs => by
      simp only [subst, realize_all, realize_subst φ, Term.realize_extendSubst]

end Formula

/-! ### Sets of formulas in a context -/

namespace FormulaSet

variable {σ : Arity S}

/-- The tuple `xs` realizes every formula of `P`. -/
def Realize (P : L.FormulaSet σ) (xs : M [^] σ) : Prop :=
  ∀ φ ∈ P, φ.Realize xs

theorem Realize.mono {P Q : L.FormulaSet σ} {xs : M [^] σ} (h : Q.Realize xs) (hPQ : P ⊆ Q) :
    P.Realize xs :=
  fun φ hφ => h φ (hPQ hφ)

end FormulaSet

/-! ### Sentences and theories -/

variable (M) in
/-- `M ⊨ φ`: the sentence `φ` holds in `M`. -/
def Sentence.Realize (φ : L.Sentence) : Prop := Formula.Realize (M := M) φ PUnit.unit

@[inherit_doc] scoped[ManySorted] infixl:51 " ⊨ " => ManySorted.Language.Sentence.Realize

/-- A sentence holds when it holds for the empty tuple. Tagged `simp` so that `simp` reduces
`M ⊨ φ` all the way to a statement about `M`. -/
@[simp]
theorem Sentence.realize_def (φ : L.Sentence) :
    M ⊨ φ ↔ Formula.Realize (M := M) φ PUnit.unit := Iff.rfl

@[simp]
theorem Sentence.realize_lift {σ : Arity S} (φ : L.Sentence) (xs : M [^] σ) :
    (φ.lift : L.Formula σ).Realize xs ↔ M ⊨ φ :=
  Formula.realize_relabel

variable (M) in
/-- `M ⊨ T`: every sentence of `T` holds in `M`. -/
class Theory.Model (T : L.Theory) : Prop where
  /-- Every sentence of `T` holds in `M`. -/
  realize_of_mem : ∀ φ ∈ T, M ⊨ φ

@[inherit_doc] scoped[ManySorted] infixl:51 " ⊨ " => ManySorted.Language.Theory.Model

namespace Theory

variable {T T' : L.Theory}

theorem model_iff (T : L.Theory) : M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem realize_sentence_of_mem [M ⊨ T] {φ : L.Sentence} (h : φ ∈ T) : M ⊨ φ :=
  Model.realize_of_mem φ h

instance model_empty : M ⊨ (∅ : L.Theory) := ⟨fun _ h => h.elim⟩

theorem Model.mono (h : M ⊨ T') (hs : T ⊆ T') : M ⊨ T := ⟨fun φ hφ => h.1 φ (hs hφ)⟩

@[simp]
theorem model_union_iff : M ⊨ T ∪ T' ↔ M ⊨ T ∧ M ⊨ T' :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩,
    fun ⟨h, h'⟩ => ⟨fun φ hφ => (Set.mem_union φ T T').1 hφ |>.elim (h.1 φ) (h'.1 φ)⟩⟩

@[simp]
theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ :=
  ⟨fun ⟨h⟩ => h φ (Set.mem_singleton φ), fun h => ⟨fun ψ (hψ : ψ = φ) => hψ ▸ h⟩⟩

/-- `T ⊨ᵇ φ`: the formula `φ` holds of every tuple in every model of `T` with nonempty sorts.
As in Mathlib's `ModelsBoundedFormula`, models are nonempty and taken in the universe `max u v z`
of the language. -/
def ModelsFormula (T : L.Theory) {σ : Arity S} (φ : L.Formula σ) : Prop :=
  ∀ (N : S → Type (max u v z)) [L.Structure N] [∀ s, Nonempty (N s)] [N ⊨ T] (xs : N [^] σ),
    φ.Realize xs

@[inherit_doc] scoped[ManySorted] infixl:51 " ⊨ᵇ " => ManySorted.Language.Theory.ModelsFormula

end Theory

variable (L M) in
/-- The complete theory of `M`: the sentences that hold in `M`. -/
def completeTheory : L.Theory := {φ | M ⊨ φ}

@[simp]
theorem mem_completeTheory {φ : L.Sentence} : φ ∈ L.completeTheory M ↔ M ⊨ φ := Iff.rfl

instance model_completeTheory : M ⊨ L.completeTheory M := ⟨fun _ h => h⟩

variable (L M) in
/-- Two structures are elementarily equivalent when they satisfy the same sentences. -/
def ElementarilyEquivalent (N : S → Type w') [L.Structure N] : Prop :=
  L.completeTheory M = L.completeTheory N

theorem elementarilyEquivalent_iff {N : S → Type w'} [L.Structure N] :
    L.ElementarilyEquivalent M N ↔ ∀ φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ := by
  simp only [ElementarilyEquivalent, Set.ext_iff, mem_completeTheory]

/-! ### Realization along maps of structures -/

section MapsRealize

variable {N : S → Type w'} [L.Structure N] {F : Type*} [DFunLike F S fun s => M s → N s]

@[simp]
theorem HomClass.realize_term [HomClass L F M N] (φ : F) (xs : M [^] Γ) {σ : Arity S}
    (t : L.Term Γ σ) : t.realize (xs.map φ) = (t.realize xs).map φ := by
  induction t with
  | var i => exact Interpret.get_map _ xs _ i
  | func f ts ih =>
    rw [Term.realize_func, ih, Term.realize_func]
    exact (HomClass.map_fun φ f _).symm
  | nil => rfl
  | prod t₁ t₂ ih₁ ih₂ => rw [Term.realize_prod, ih₁, ih₂]; rfl


/-- An injective strong homomorphism preserves and reflects atomic formulas. -/
theorem StrongHomClass.realize_of_isAtomic [StrongHomClass L F M N] (g : F)
    (hinj : ∀ s, Function.Injective (g s)) {σ : Arity S} {φ : L.Formula σ} (h : φ.IsAtomic)
    (xs : M [^] σ) : φ.Realize (xs.map g) ↔ φ.Realize xs := by
  cases h with
  | equal t₁ t₂ =>
    rw [Formula.realize_equal, Formula.realize_equal, HomClass.realize_term,
      HomClass.realize_term]
    exact (Interpret.map_injective hinj).eq_iff
  | rel R ts =>
    rw [Formula.realize_rel, Formula.realize_rel, HomClass.realize_term]
    exact StrongHomClass.map_rel g R _

/-- An injective strong homomorphism preserves and reflects quantifier-free formulas. -/
theorem StrongHomClass.realize_of_isQF [StrongHomClass L F M N] (g : F)
    (hinj : ∀ s, Function.Injective (g s)) {σ : Arity S} {φ : L.Formula σ} (h : φ.IsQF)
    (xs : M [^] σ) : φ.Realize (xs.map g) ↔ φ.Realize xs := by
  induction h with
  | falsum => exact Iff.rfl
  | of_isAtomic h => exact StrongHomClass.realize_of_isAtomic g hinj h xs
  | imp _ _ ih₁ ih₂ => simp only [Formula.realize_imp, ih₁, ih₂]

/-- A strong homomorphism that is bijective on every sort preserves and reflects all formulas. -/
theorem StrongHomClass.realize_formula [StrongHomClass L F M N] (g : F)
    (hinj : ∀ s, Function.Injective (g s)) (hsurj : ∀ s, Function.Surjective (g s)) :
    ∀ {σ : Arity S} (φ : L.Formula σ) (xs : M [^] σ), φ.Realize (xs.map g) ↔ φ.Realize xs
  | _, .falsum, _ => Iff.rfl
  | _, .equal _ _, xs => StrongHomClass.realize_of_isAtomic g hinj (.equal _ _) xs
  | _, .rel _ _, xs => StrongHomClass.realize_of_isAtomic g hinj (.rel _ _) xs
  | _, .imp φ ψ, xs => by
    simp only [Formula.realize_imp, StrongHomClass.realize_formula g hinj hsurj φ xs,
      StrongHomClass.realize_formula g hinj hsurj ψ xs]
  | _, .all _ φ, xs => by
    simp only [Formula.realize_all]
    refine ⟨fun h ys => (StrongHomClass.realize_formula g hinj hsurj φ (xs, ys)).1 (h _),
      fun h ys => ?_⟩
    obtain ⟨zs, rfl⟩ := Interpret.map_surjective (fun s _ => hsurj s) ys
    exact (StrongHomClass.realize_formula g hinj hsurj φ (xs, zs)).2 (h zs)

/-- Embeddings preserve and reflect quantifier-free formulas. -/
theorem Embedding.realize_of_isQF (g : M ↪[L] N) {σ : Arity S} {φ : L.Formula σ} (h : φ.IsQF)
    (xs : M [^] σ) : φ.Realize (xs.map g) ↔ φ.Realize xs :=
  StrongHomClass.realize_of_isQF g g.injective h xs

/-! #### Formulas quantifier-free relative to a set of sorts -/

/-- A formula in context `σ ⨯ τ`, for a block `τ` without positions, is a formula in context
`σ`. -/
theorem Formula.realize_prod_of_isEmpty {σ τ : Arity S} (e : τ.FromSorts ∅)
    (ψ : L.Formula (σ ⨯ τ)) (xs : M [^] σ) (z : M [^] τ) :
    ψ.Realize ((xs, z) : M [^] (σ ⨯ τ)) ↔
      (ψ.relabel (Idx.elim (fun _ => id) fun s => (e.isEmpty_idx s).elim)).Realize xs :=
  (Formula.realize_relabel_of_get_eq ψ fun s i => by
    cases i with
    | left i => rfl
    | right i => exact (e.isEmpty_idx s).elim i).symm

/-- **Transfer of quantifier-free formulas**: two tuples that agree on the atomic formulas agree
on the formulas quantifier-free relative to no sorts. Such formulas may still quantify over
blocks without positions. -/
theorem Formula.realize_iff_of_isQFRelTo_empty {σ : Arity S} {φ : L.Formula σ}
    (hφ : φ.IsQFRelTo ∅) :
    ∀ (x : M [^] σ) (y : N [^] σ), (∀ ψ : L.Formula σ, ψ.IsAtomic → (ψ.Realize x ↔ ψ.Realize y)) →
      (φ.Realize x ↔ φ.Realize y) := by
  induction hφ with
  | falsum => exact fun _ _ _ => Iff.rfl
  | of_isAtomic h => exact fun _ _ hxy => hxy _ h
  | imp _ _ ih₁ ih₂ => exact fun x y hxy => imp_congr (ih₁ x y hxy) (ih₂ x y hxy)
  | @all σ τ φ _ hτ ih =>
    intro x y hxy
    have e : ∀ s, τ.Idx s → False := fun s i => (hτ.isEmpty_idx s).elim i
    have key : ∀ (z : M [^] τ) (z' : N [^] τ),
        φ.Realize ((x, z) : M [^] (σ ⨯ τ)) ↔ φ.Realize ((y, z') : N [^] (σ ⨯ τ)) :=
      fun z z' => ih (x, z) (y, z') fun ψ hψ => by
        rw [realize_prod_of_isEmpty hτ, realize_prod_of_isEmpty hτ]
        exact hxy _ (hψ.relabel _)
    have zM : M [^] τ := Interpret.ofFn fun s i => (e s i).elim
    have zN : N [^] τ := Interpret.ofFn fun s i => (e s i).elim
    simp only [Formula.realize_all]
    exact ⟨fun h z' => (key zM z').1 (h zM), fun h z => (key z zN).2 (h zN)⟩

/-- An injective strong homomorphism that is onto on the sorts of `R` preserves and reflects
formulas that are quantifier-free relative to `R`. -/
theorem StrongHomClass.realize_of_isQFRelTo [StrongHomClass L F M N] {R : Set S} (g : F)
    (hinj : ∀ s, Function.Injective (g s)) (hsurj : ∀ s ∈ R, Function.Surjective (g s))
    {σ : Arity S} {φ : L.Formula σ} (h : φ.IsQFRelTo R) (xs : M [^] σ) :
    φ.Realize (xs.map g) ↔ φ.Realize xs := by
  induction h with
  | falsum => exact Iff.rfl
  | of_isAtomic h => exact StrongHomClass.realize_of_isAtomic g hinj h xs
  | imp _ _ ih₁ ih₂ => simp only [Formula.realize_imp, ih₁, ih₂]
  | all _ hτ ih =>
    simp only [Formula.realize_all]
    refine ⟨fun h ys => (ih (xs, ys)).1 (h _), fun h ys => ?_⟩
    obtain ⟨zs, rfl⟩ := Interpret.map_surjective (fun s hmem => hsurj s (hτ s hmem)) ys
    exact (ih (xs, zs)).2 (h zs)

/-- Embeddings preserve and reflect the formulas quantifier-free relative to no sorts. -/
theorem Embedding.realize_of_isQFRelTo_empty (g : M ↪[L] N) {σ : Arity S} {φ : L.Formula σ}
    (hφ : φ.IsQFRelTo ∅) (xs : M [^] σ) : φ.Realize (xs.map g) ↔ φ.Realize xs :=
  (Formula.realize_iff_of_isQFRelTo_empty hφ xs (xs.map g) fun _ hψ =>
    (StrongHomClass.realize_of_isAtomic g g.injective hψ xs).symm).symm

namespace Equiv

@[simp]
theorem realize_formula (g : M ≃[L] N) {σ : Arity S} (φ : L.Formula σ) (xs : M [^] σ) :
    φ.Realize (xs.map g) ↔ φ.Realize xs :=
  StrongHomClass.realize_formula g g.injective g.surjective φ xs

theorem realize_sentence (g : M ≃[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  (g.realize_formula φ PUnit.unit).symm

theorem elementarilyEquivalent (g : M ≃[L] N) : L.ElementarilyEquivalent M N :=
  elementarilyEquivalent_iff.2 g.realize_sentence

theorem theory_model (g : M ≃[L] N) {T : L.Theory} [M ⊨ T] : N ⊨ T :=
  ⟨fun φ h => (g.realize_sentence φ).1 (Theory.realize_sentence_of_mem h)⟩

end Equiv

end MapsRealize

end Language

end ManySorted
