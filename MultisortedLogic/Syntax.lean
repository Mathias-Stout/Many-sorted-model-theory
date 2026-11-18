/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Order.Notation

/-!
# Many-sorted first-order logic: syntax

Terms and formulas of many-sorted first-order logic. Contrary to the one-sorted development in
Mathlib, we only use positional (indexed) variables in terms and formulas. A formula of
shape `σ` has a variable slot for each term of `σ`. This keeps the basic definitions minimal. Free
'named' variables are a layer built on top of this. A formula in named variables, with names
from `α : S → Type*`, is a combination of some formula with variables of shape `ctx : Arity S`
and an assignment `n : ∀ s, ctx.Idx s → α s`. For the precise implementation, see
`Language.BoundedFormula L α σ` in `Named.lean`.

## Main declarations

* `Language.Term L Γ σ`: tuples of terms of shape `σ` whose variables are the positions of `Γ`.
  `#n` is the variable at de Bruijn position `n`, counted from the right.
* `Language.Formula L σ`: formulas in context `σ`; `L.Sentence` is `L.Formula ⦃⦄`, and `L.Theory`
  is a set of sentences.
* `Formula.relabel` and `Formula.subst`: relabelling along a map of positions, which covers
  weakening, permuting and reassociating variables, and substitution of a tuple of terms for the
  context.
* `Formula.IsAtomic`, `Formula.IsQF`: atomic and quantifier-free formulas.

## References

This file was originally based on `Mathlib/ModelTheory/Syntax.lean`, by Aaron Anderson, Jesse
Michael Han and Floris van Doorn, and its atomic and quantifier-free formulas on
`Mathlib/ModelTheory/Complexity.lean`, by Aaron Anderson.
-/

@[expose] public section

universe u v z

namespace ManySorted

open Arity

namespace Language

variable {S : Type z} (L : Language.{u, v} S)

/-! ### Terms -/

/-- `L.Term Γ σ` is the type of tuples of terms of shape `σ` that take in arguments of shape `Γ`.
A single term of sort `s` is an `L.Term Γ ⦃s⦄`. -/
inductive Term (Γ : Arity S) : Arity S → Type (max z u)
  /-- Picking out a single variable (position) in the tuple `Γ`. -/
  | var {s : S} (i : Γ.Idx s) : Term Γ ⦃s⦄
  /-- A function symbol applied to a tuple of terms. -/
  | func {σ : Arity S} {t : S} (f : L.Functions σ t) (ts : Term Γ σ) : Term Γ ⦃t⦄
  /-- The empty tuple. -/
  | nil : Term Γ ⦃⦄
  /-- The pairing of two tuples. -/
  | prod {σ τ : Arity S} (t₁ : Term Γ σ) (t₂ : Term Γ τ) : Term Γ (σ ⨯ τ)

variable {L} {Γ Γ' : Arity S}

namespace Term

/-- A tuple of positions in `Γ` of shape `σ` can be interpreted as a tuple of variables of shape
  `σ` with input `Γ`, which a `Term Γ σ`. -/
def vars : ∀ {σ : Arity S}, Γ.Idx [^] σ → L.Term Γ σ
  | .nil, _ => nil
  | .of _, i => var i
  | .prod _ _, x => prod (vars x.1) (vars x.2)

/-- Relabel the positions of a tuple of terms along a map of positions `Γ → Γ'`. -/
def relabel (g : ∀ s, Γ.Idx s → Γ'.Idx s) : ∀ {σ}, L.Term Γ σ → L.Term Γ' σ
  | _, var i => var (g _ i)
  | _, func f ts => func f (ts.relabel g)
  | _, nil => nil
  | _, prod t₁ t₂ => prod (t₁.relabel g) (t₂.relabel g)

/-- Turn a tuple of terms `L.Term Γ σ` into a dependent assignment of positions in `σ`. -/
def get : ∀ {σ}, L.Term Γ σ → ∀ s, σ.Idx s → L.Term Γ ⦃s⦄
  | _, t, _, .var => t
  | _, prod t _, _, .left i => t.get _ i
  | _, prod _ u, _, .right j => u.get _ j

/-- `get` at the unique position of `⦃s⦄`. This is not `rfl` for a variable `t`: the match in
`get` splits on the term first. -/
@[simp]
theorem get_var {s : S} (t : L.Term Γ ⦃s⦄) : t.get s .var = t := by cases t <;> rfl

/-- Substitute a tuple of terms `r : L.Term Γ' Γ` for the positions of `Γ` in `t : L.Term Γ σ`:
the variable at position `i` is replaced by the entry `r.get _ i`. -/
def subst : ∀ {σ}, L.Term Γ σ → L.Term Γ' Γ → L.Term Γ' σ
  | _, var i, r => r.get _ i
  | _, func f ts, r => func f (ts.subst r)
  | _, nil, _ => nil
  | _, prod t₁ t₂, r => prod (t₁.subst r) (t₂.subst r)

/-- Extend a tuple to substitute for `Γ` to one to substitute for `Γ ⨯ ρ`, which keeps the positions
of `ρ`. -/
def extendSubst {ρ : Arity S} (r : L.Term Γ' Γ) : L.Term (Γ' ⨯ ρ) (Γ ⨯ ρ) :=
  prod (r.relabel fun _ => .left) (vars (Interpret.ofFn fun _ => .right))

end Term

/-! ### Formulas -/

variable (L) in
/-- `L.Formula σ` is the type of formulas in context `σ`: their variables are the positions of
`σ`, and quantifiers extend the context on the right. -/
inductive Formula : Arity S → Type (max z u v)
  /-- Falsum. -/
  | falsum {σ : Arity S} : Formula σ
  /-- Equality of two tuples of terms of the same shape. -/
  | equal {σ τ : Arity S} (t₁ t₂ : L.Term σ τ) : Formula σ
  /-- A relation symbol applied to a tuple of terms. -/
  | rel {σ τ : Arity S} (R : L.Relations τ) (ts : L.Term σ τ) : Formula σ
  /-- Implication. -/
  | imp {σ : Arity S} (φ ψ : Formula σ) : Formula σ
  /-- Universal quantification over a block of variables of shape `τ`. -/
  | all {σ : Arity S} (τ : Arity S) (φ : Formula (σ ⨯ τ)) : Formula σ

variable (L) in
/-- A sentence is a formula in the empty context. -/
abbrev Sentence := L.Formula ⦃⦄

variable (L) in
/-- A set of formulas in the context `σ`, for instance a partial type in the variables of `σ`. -/
abbrev FormulaSet (σ : Arity S) := Set (L.Formula σ)

variable (L) in
/-- A theory is a set of sentences, that is, a set of formulas in the empty context. The notions
for sets of formulas apply to theories through dot notation, as in `T.IsSatisfiable`. -/
abbrev Theory := L.FormulaSet ⦃⦄

namespace Formula

variable {σ τ : Arity S}

instance : Bot (L.Formula σ) := ⟨falsum⟩

instance : Inhabited (L.Formula σ) := ⟨falsum⟩

/-- Negation. -/
protected def not (φ : L.Formula σ) : L.Formula σ := φ.imp ⊥

instance : Top (L.Formula σ) := ⟨(⊥ : L.Formula σ).not⟩

instance : Min (L.Formula σ) := ⟨fun φ ψ => (φ.imp ψ.not).not⟩

instance : Max (L.Formula σ) := ⟨fun φ ψ => φ.not.imp ψ⟩

/-- Biimplication. -/
protected def iff (φ ψ : L.Formula σ) : L.Formula σ := φ.imp ψ ⊓ ψ.imp φ

/-- Existential quantification over a block of variables of shape `τ`. -/
protected def ex (τ : Arity S) (φ : L.Formula (σ ⨯ τ)) : L.Formula σ := (all τ φ.not).not

section finite

variable {β : Type*}

/-- The conjunction of finitely many formulas. -/
noncomputable def iInf (s : Finset β) (f : β → L.Formula σ) : L.Formula σ :=
  (s.toList.map f).foldr (· ⊓ ·) ⊤

/-- The disjunction of finitely many formulas. -/
noncomputable def iSup (s : Finset β) (f : β → L.Formula σ) : L.Formula σ :=
  (s.toList.map f).foldr (· ⊔ ·) ⊥

end finite

/-! ### Relabelling and substitution -/

/-- Relabel the positions of a formula along a map of positions `σ → τ`. This covers weakening,
permuting, duplicating and reassociating variables. -/
def relabel : ∀ {σ τ : Arity S}, (∀ s, σ.Idx s → τ.Idx s) → L.Formula σ → L.Formula τ
  | _, _, _, falsum => falsum
  | _, _, g, equal t₁ t₂ => equal (t₁.relabel g) (t₂.relabel g)
  | _, _, g, rel R ts => rel R (ts.relabel g)
  | _, _, g, imp φ ψ => imp (φ.relabel g) (ψ.relabel g)
  | _, _, g, all _ φ => all _ (φ.relabel (Idx.extendRight g))

/-- Substitute a tuple of terms `r : L.Term τ σ` for the positions of a formula in context `σ`.
This also uses a formula in context `σ` like a relation symbol of arity `σ`. -/
def subst : ∀ {σ τ : Arity S}, L.Formula σ → L.Term τ σ → L.Formula τ
  | _, _, falsum, _ => falsum
  | _, _, equal t₁ t₂, r => equal (t₁.subst r) (t₂.subst r)
  | _, _, rel R ts, r => rel R (ts.subst r)
  | _, _, imp φ ψ, r => imp (φ.subst r) (ψ.subst r)
  | _, _, all _ φ, r => all _ (φ.subst r.extendSubst)

/-! ### Atomic and quantifier-free formulas -/

/-- An atomic formula: an equality or a relation symbol applied to terms.
Note that `⊥` and `⊤` are not considered atomic. -/
inductive IsAtomic : L.Formula σ → Prop
  | equal {τ : Arity S} (t₁ t₂ : L.Term σ τ) : IsAtomic (equal t₁ t₂)
  | rel {τ : Arity S} (R : L.Relations τ) (ts : L.Term σ τ) : IsAtomic (rel R ts)

/-- A quantifier-free formula: built from atomic formulas and `⊥` by implication. -/
inductive IsQF : L.Formula σ → Prop
  | falsum : IsQF falsum
  | of_isAtomic {φ : L.Formula σ} : φ.IsAtomic → IsQF φ
  | imp {φ ψ : L.Formula σ} : IsQF φ → IsQF ψ → IsQF (φ.imp ψ)

theorem IsQF.not {φ : L.Formula σ} (h : φ.IsQF) : φ.not.IsQF := h.imp .falsum

theorem IsAtomic.relabel {φ : L.Formula σ} (h : φ.IsAtomic) (g : ∀ s, σ.Idx s → τ.Idx s) :
    (φ.relabel g).IsAtomic := by
  cases h with
  | equal t₁ t₂ => exact .equal _ _
  | rel R ts => exact .rel _ _

theorem IsQF.relabel {φ : L.Formula σ} (h : φ.IsQF) (g : ∀ s, σ.Idx s → τ.Idx s) :
    (φ.relabel g).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h => exact .of_isAtomic (h.relabel g)
  | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂

end Formula

/-! ### Notation -/

/-- `∀' τ φ` quantifies over a block of shape `τ`; a sort `s` stands for `⦃s⦄`. -/
scoped[ManySorted] notation:110 "∀'" τ:max φ:110 =>
  ManySorted.Language.Formula.all (τ : ManySorted.Arity _) φ

/-- `∃' τ φ` quantifies over a block of shape `τ`; a sort `s` stands for `⦃s⦄`. -/
scoped[ManySorted] notation:110 "∃'" τ:max φ:110 =>
  ManySorted.Language.Formula.ex (τ : ManySorted.Arity _) φ

@[inherit_doc] scoped[ManySorted] infix:50 " =' " => ManySorted.Language.Formula.equal
@[inherit_doc] scoped[ManySorted] infixr:25 " ⟹ " => ManySorted.Language.Formula.imp
@[inherit_doc] scoped[ManySorted] infix:20 " ⇔ " => ManySorted.Language.Formula.iff
@[inherit_doc] scoped[ManySorted] prefix:max "∼" => ManySorted.Language.Formula.not

/-! ### Sentences -/

/-- A sentence as a formula in any context. -/
def Sentence.lift {σ : Arity S} (φ : L.Sentence) : L.Formula σ := φ.relabel Idx.elimNil

end Language

/-- `#n` is the variable at de Bruijn position `n`, counted from the right of a stack-shaped
context. -/
scoped syntax:max "#" term:max : term
macro_rules
  | `(# $n) => `(ManySorted.Language.Term.var (ManySorted.Arity.VarIndex.get (n := $n)))

end ManySorted
