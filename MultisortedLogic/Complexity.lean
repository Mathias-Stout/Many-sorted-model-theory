/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Syntax

/-!
# Classes of formulas

Classes of formulas by complexity, beyond the atomic and quantifier-free formulas of
`Syntax.lean`.

## Main declarations

* `Arity.FromSorts R τ`: every sort of `τ` lies in `R`.
* `Formula.IsQFRelTo R`: quantifier-free except for quantifiers over blocks of sorts in `R`.
* `FormulaClass`: a set of formulas in each context; the classes `NegClosed` and `HasAtomic`, and
  the instances `FormulaClass.all`, `FormulaClass.qf`, `FormulaClass.qfRelTo`.
* `IsFragment`: sets of (positional or named) formulas closed under finite conjunctions and
  disjunctions.
-/

@[expose] public section

universe u v z

namespace ManySorted

namespace Arity

variable {S : Type z}

/-- Every sort occurring in `σ` lies in `R`. -/
def FromSorts (σ : Arity S) (R : Set S) : Prop := ∀ s ∈ σ, s ∈ R

theorem FromSorts.of {R : Set S} {s : S} (h : s ∈ R) : (⦃s⦄ : Arity S).FromSorts R :=
  fun _ i => (mem_of.mp i) ▸ h

/-- An arity all of whose sorts lie in `∅` has no positions. -/
theorem FromSorts.isEmpty_idx {σ : Arity S} (h : σ.FromSorts ∅) (s : S) : IsEmpty (σ.Idx s) :=
  ⟨fun i => Set.notMem_empty s (h s i.mem)⟩

end Arity

namespace Language

open Arity Structure

variable {S : Type z} {L : Language.{u, v} S} {R R' : Set S}

namespace Formula

/-- Quantifier-free relative to `R`: the only quantifiers range over blocks of sorts in `R`. -/
inductive IsQFRelTo (R : Set S) : ∀ {σ : Arity S}, L.Formula σ → Prop
  | falsum {σ : Arity S} : IsQFRelTo R (falsum : L.Formula σ)
  /- Recall that under the chosen conventions, `⊥` and `⊤` are not atomic, so they are not
    duplicated here. -/
  | of_isAtomic {σ : Arity S} {φ : L.Formula σ} : φ.IsAtomic → IsQFRelTo R φ
  | imp {σ : Arity S} {φ ψ : L.Formula σ} : IsQFRelTo R φ → IsQFRelTo R ψ → IsQFRelTo R (φ.imp ψ)
  | all {σ τ : Arity S} {φ : L.Formula (σ ⨯ τ)} :
      IsQFRelTo R φ → τ.FromSorts R → IsQFRelTo R (all τ φ)

variable {σ τ : Arity S}

theorem IsQF.isQFRelTo {φ : L.Formula σ} (h : φ.IsQF) : φ.IsQFRelTo R := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h => exact .of_isAtomic h
  | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂

theorem IsQFRelTo.not {φ : L.Formula σ} (h : φ.IsQFRelTo R) : φ.not.IsQFRelTo R := h.imp .falsum

theorem IsQFRelTo.ex {φ : L.Formula (σ ⨯ τ)} (h : φ.IsQFRelTo R) (hτ : τ.FromSorts R) :
    (φ.ex τ).IsQFRelTo R :=
  (IsQFRelTo.all h.not hτ).not

theorem IsQFRelTo.mono {φ : L.Formula σ} (h : φ.IsQFRelTo R) (hR : R ⊆ R') : φ.IsQFRelTo R' := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h => exact .of_isAtomic h
  | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂
  | all _ hτ ih => exact .all ih fun s i => hR (hτ s i)

theorem IsQFRelTo.relabel : ∀ {σ τ : Arity S} {φ : L.Formula σ} (g : ∀ s, σ.Idx s → τ.Idx s),
    φ.IsQFRelTo R → (φ.relabel g).IsQFRelTo R
  | _, _, _, _, .falsum => .falsum
  | _, _, _, g, .of_isAtomic h => .of_isAtomic (h.relabel g)
  | _, _, _, g, .imp h₁ h₂ => .imp (h₁.relabel g) (h₂.relabel g)
  | _, _, _, g, .all h hτ => .all (h.relabel (Idx.extendRight g)) hτ

/-- Substituting terms keeps a formula quantifier-free relative to `R`. -/
theorem IsQFRelTo.subst : ∀ {σ τ : Arity S} {φ : L.Formula σ} (r : L.Term τ σ),
    φ.IsQFRelTo R → (φ.subst r).IsQFRelTo R
  | _, _, _, _, .falsum => .falsum
  | _, _, _, _, .of_isAtomic (.equal _ _) => .of_isAtomic (.equal _ _)
  | _, _, _, _, .of_isAtomic (.rel _ _) => .of_isAtomic (.rel _ _)
  | _, _, _, r, .imp h₁ h₂ => .imp (h₁.subst r) (h₂.subst r)
  | _, _, _, r, .all h hτ => .all (h.subst r.extendSubst) hτ

end Formula

/-! ### Classes of formulas -/

variable (L) in
/-- A class of formulas: a set of formulas in each context. -/
abbrev FormulaClass := ∀ σ : Arity S, L.FormulaSet σ

namespace FormulaClass

/-- `Δ` is closed under negation. -/
class NegClosed (Δ : L.FormulaClass) : Prop where
  not_mem : ∀ {σ : Arity S} {φ : L.Formula σ}, φ ∈ Δ σ → φ.not ∈ Δ σ

/-- `Δ` contains the atomic formulas. -/
class HasAtomic (Δ : L.FormulaClass) : Prop where
  atomic_mem : ∀ {σ : Arity S} {φ : L.Formula σ}, φ.IsAtomic → φ ∈ Δ σ

variable (L) in
/-- All formulas. -/
def all : L.FormulaClass := fun _ => Set.univ

variable (L) in
/-- The quantifier-free formulas. -/
def qf : L.FormulaClass := fun _ => {φ | φ.IsQF}

variable (L) in
/-- The formulas quantifier-free relative to the sorts `R`. -/
def qfRelTo (R : Set S) : L.FormulaClass := fun _ => {φ | φ.IsQFRelTo R}

instance : NegClosed (all L) := ⟨fun _ => Set.mem_univ _⟩
instance : HasAtomic (all L) := ⟨fun _ => Set.mem_univ _⟩
instance : NegClosed (qf L) := ⟨fun h => Formula.IsQF.not h⟩
instance : HasAtomic (qf L) := ⟨fun h => Formula.IsQF.of_isAtomic h⟩
instance (R : Set S) : NegClosed (qfRelTo L R) := ⟨fun h => Formula.IsQFRelTo.not h⟩
instance (R : Set S) : HasAtomic (qfRelTo L R) := ⟨fun h => Formula.IsQFRelTo.of_isAtomic h⟩

end FormulaClass

open FormulaClass

variable {σ : Arity S}

/-! ### Fragments -/

/-- A set of formulas closed under finite conjunctions and disjunctions. It is stated for any type
with `⊓`, `⊔`, `⊤` and `⊥`, so that it covers positional and named formulas alike. -/
structure IsFragment {X : Type*} [Min X] [Max X] [Top X] [Bot X] (Δ : Set X) : Prop where
  top_mem : ⊤ ∈ Δ
  bot_mem : ⊥ ∈ Δ
  inf_mem {φ ψ : X} : φ ∈ Δ → ψ ∈ Δ → φ ⊓ ψ ∈ Δ
  sup_mem {φ ψ : X} : φ ∈ Δ → ψ ∈ Δ → φ ⊔ ψ ∈ Δ

namespace IsFragment

variable {X : Type*} [Min X] [Max X] [Top X] [Bot X] {Δ : Set X} (hΔ : IsFragment Δ)
  {ι : Type*}
include hΔ

theorem foldr_inf_mem : ∀ l : List X, (∀ φ ∈ l, φ ∈ Δ) → l.foldr (· ⊓ ·) ⊤ ∈ Δ
  | [], _ => hΔ.top_mem
  | φ :: l, h => hΔ.inf_mem (h φ (by simp)) (foldr_inf_mem l fun ψ hψ => h ψ (by simp [hψ]))

theorem foldr_sup_mem : ∀ l : List X, (∀ φ ∈ l, φ ∈ Δ) → l.foldr (· ⊔ ·) ⊥ ∈ Δ
  | [], _ => hΔ.bot_mem
  | φ :: l, h => hΔ.sup_mem (h φ (by simp)) (foldr_sup_mem l fun ψ hψ => h ψ (by simp [hψ]))

/-- A fragment contains the conjunction of finitely many of its members. The finite conjunctions
`Formula.iInf` and `BoundedFormula.iInf` are this fold. -/
theorem iInf_mem (s : Finset ι) (f : ι → X) (h : ∀ i ∈ s, f i ∈ Δ) :
    (s.toList.map f).foldr (· ⊓ ·) ⊤ ∈ Δ :=
  hΔ.foldr_inf_mem _ (by simpa using h)

/-- A fragment contains the disjunction of finitely many of its members. The finite disjunctions
`Formula.iSup` and `BoundedFormula.iSup` are this fold. -/
theorem iSup_mem (s : Finset ι) (f : ι → X) (h : ∀ i ∈ s, f i ∈ Δ) :
    (s.toList.map f).foldr (· ⊔ ·) ⊥ ∈ Δ :=
  hΔ.foldr_sup_mem _ (by simpa using h)

end IsFragment

theorem Formula.isFragment_qfRelTo (R : Set S) : IsFragment (qfRelTo L R σ) where
  top_mem := Formula.IsQFRelTo.falsum.not
  bot_mem := .falsum
  inf_mem h₁ h₂ := (h₁.imp h₂.not).not
  sup_mem h₁ h₂ := h₁.not.imp h₂

end Language

end ManySorted
