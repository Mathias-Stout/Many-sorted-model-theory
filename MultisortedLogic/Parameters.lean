/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.LanguageMap

/-!
# Formulas with parameters

A formula with parameters from a family `α` is a positional formula of `L[[α]]`: the parameter
`a : α s` is the constant symbol `L.con a`. Values `v : ∀ s, α s → M s` for the parameters are the
`L[[α]]`-structure `withConstantsStructure v`, and `φ.RealizeWith v xs` is realization in it.

## Main definitions

* `Term.ofFn`: a tuple of terms from a term for each position.
* `Constants.term`: a constant symbol as a term.
* `Formula.RealizeWith`, `FormulaSet.RealizeWith`: realization when the parameters take given
  values.
* `Formula.ofNames φ names`: a positional `L`-formula with its positions named by parameters, as a
  sentence of `L[[α]]`.

## Implementation notes

`RealizeWith` is an abbreviation, so that statements show the values of the parameters. `rw` does
not see through it when the goal shows `Formula.Realize`; use `simp only` or term mode there.
-/

@[expose] public section

universe u v w z u''

namespace ManySorted.Language

open Arity Structure

variable {S : Type z} {L : Language.{u, v} S} {M : S → Type w} {α : S → Type u''}

/-! ### Terms -/

namespace Term

variable {Γ : Arity S}

/-- A tuple of terms from a term for each position. -/
def ofFn : ∀ {σ : Arity S}, (∀ s, σ.Idx s → L.Term Γ ⦃s⦄) → L.Term Γ σ
  | .nil, _ => nil
  | .of s, f => f s .var
  | .prod _ _, f => prod (ofFn fun s i => f s (.left i)) (ofFn fun s i => f s (.right i))

@[simp]
theorem realize_ofFn [L.Structure M] (xs : M [^] Γ) :
    ∀ {σ : Arity S} (f : ∀ s, σ.Idx s → L.Term Γ ⦃s⦄),
      (ofFn f).realize xs = Interpret.ofFn fun s i => (f s i).realize xs
  | .nil, _ => rfl
  | .of _, _ => rfl
  | .prod _ _, f =>
    congrArg₂ Prod.mk (realize_ofFn xs fun s i => f s (.left i))
      (realize_ofFn xs fun s i => f s (.right i))

/-- `get` is a left inverse of `ofFn`. -/
@[simp]
theorem get_ofFn : ∀ {σ : Arity S} (f : ∀ s, σ.Idx s → L.Term Γ ⦃s⦄) (s : S) (i : σ.Idx s),
    (ofFn f).get s i = f s i
  | _, f, _, .var => get_var (f _ .var)
  | _, f, _, .left i => get_ofFn (fun s i => f s (.left i)) _ i
  | _, f, _, .right i => get_ofFn (fun s i => f s (.right i)) _ i

/-- `get` is a right inverse of `ofFn`. -/
@[simp]
theorem ofFn_get : ∀ {σ : Arity S} (t : L.Term Γ σ), ofFn t.get = t
  | _, .var _ => rfl
  | _, .func _ _ => rfl
  | _, .nil => rfl
  | _, .prod t₁ t₂ => congrArg₂ prod (ofFn_get t₁) (ofFn_get t₂)

variable {Γ' Γ'' : Arity S}

theorem relabel_ofFn (g : ∀ s, Γ.Idx s → Γ'.Idx s) :
    ∀ {σ : Arity S} (f : ∀ s, σ.Idx s → L.Term Γ ⦃s⦄),
      (ofFn f).relabel g = ofFn fun s i => (f s i).relabel g
  | .nil, _ => rfl
  | .of _, _ => rfl
  | .prod _ _, _ => congrArg₂ prod (relabel_ofFn g _) (relabel_ofFn g _)

theorem get_relabel (g : ∀ s, Γ.Idx s → Γ'.Idx s) :
    ∀ {σ : Arity S} (t : L.Term Γ σ) (s : S) (i : σ.Idx s),
      (t.relabel g).get s i = (t.get s i).relabel g
  | _, .var _, _, .var => rfl
  | _, .func _ _, _, .var => rfl
  | _, .prod t₁ _, _, .left i => get_relabel g t₁ _ i
  | _, .prod _ t₂, _, .right i => get_relabel g t₂ _ i

/-- Substituting into a relabelled tuple of terms substitutes the relabelled entries. -/
theorem subst_relabel (g : ∀ s, Γ.Idx s → Γ'.Idx s) (r : L.Term Γ'' Γ') :
    ∀ {σ : Arity S} (t : L.Term Γ σ),
      (t.relabel g).subst r = t.subst (ofFn fun s i => r.get s (g s i))
  | _, .var i => (get_ofFn (fun s i => r.get s (g s i)) _ i).symm
  | _, .func f ts => congrArg (func f) (subst_relabel g r ts)
  | _, .nil => rfl
  | _, .prod t₁ t₂ => congrArg₂ prod (subst_relabel g r t₁) (subst_relabel g r t₂)

end Term

/-- Substituting into a relabelled formula substitutes the relabelled entries. -/
theorem Formula.subst_relabel :
    ∀ {σ τ ρ : Arity S} (g : ∀ s, σ.Idx s → τ.Idx s) (r : L.Term ρ τ) (φ : L.Formula σ),
      (φ.relabel g).subst r = φ.subst (Term.ofFn fun s i => r.get s (g s i))
  | _, _, _, _, _, .falsum => rfl
  | _, _, _, g, r, .equal t₁ t₂ =>
    congrArg₂ Formula.equal (Term.subst_relabel g r t₁) (Term.subst_relabel g r t₂)
  | _, _, _, g, r, .rel _ ts => congrArg (Formula.rel _) (Term.subst_relabel g r ts)
  | _, _, _, g, r, .imp φ ψ =>
    congrArg₂ Formula.imp (Formula.subst_relabel g r φ) (Formula.subst_relabel g r ψ)
  | _, _, _, g, r, .all τ φ => by
    refine congrArg (Formula.all τ) ((Formula.subst_relabel _ _ φ).trans
      (congrArg φ.subst (congrArg₂ Term.prod ?_ (Term.ofFn_get _))))
    rw [Term.relabel_ofFn]
    exact congrArg Term.ofFn (funext₂ fun s i => Term.get_relabel _ r s (g s i))

/-- A constant symbol, as a term in any context. -/
def Constants.term {s : S} (c : L.Constants s) {Γ : Arity S} : L.Term Γ ⦃s⦄ :=
  .func c .nil

@[simp]
theorem Term.realize_constants [L.Structure M] {Γ : Arity S} (xs : M [^] Γ) {s : S}
    (c : L.Constants s) : (c.term : L.Term Γ ⦃s⦄).realize xs = funMap c PUnit.unit :=
  rfl

/-! ### Realization with values for the parameters -/

/-- `φ.RealizeWith v xs`: the formula `φ` with parameters in `α` holds at `xs` when the parameters
take the values `v`. -/
abbrev Formula.RealizeWith [L.Structure M] {σ : Arity S} (φ : L[[α]].Formula σ)
    (v : ∀ s, α s → M s) (xs : M [^] σ) : Prop :=
  @Formula.Realize _ _ M (withConstantsStructure v) σ φ xs

/-- `P.RealizeWith v xs`: every formula of `P` holds at `xs` when the parameters take the values
`v`. -/
abbrev FormulaSet.RealizeWith [L.Structure M] {σ : Arity S} (P : L[[α]].FormulaSet σ)
    (v : ∀ s, α s → M s) (xs : M [^] σ) : Prop :=
  @FormulaSet.Realize _ _ M (withConstantsStructure v) σ P xs

variable (L) in
/-- The parameter `a`, as a term in any context. -/
def Term.con {Γ : Arity S} {s : S} (a : α s) : L[[α]].Term Γ ⦃s⦄ :=
  (L.con a).term

/-- A parameter is realized by its value. -/
@[simp]
theorem Term.realize_con [L.Structure M] (v : ∀ s, α s → M s) {Γ : Arity S} (xs : M [^] Γ)
    {s : S} (a : α s) :
    @Term.realize _ L[[α]] Γ M (withConstantsStructure v) xs ⦃s⦄ (Term.con L a) = v s a :=
  rfl

/-- A positional `L`-formula in context `τ`, with its positions named by parameters, as a sentence
with parameters. -/
def Formula.ofNames {τ : Arity S} (φ : L.Formula τ) (names : ∀ s, τ.Idx s → α s) :
    L[[α]].Sentence :=
  ((L.lhomWithConstants α).onFormula φ).subst (Term.ofFn fun s i => Term.con L (names s i))

@[simp]
theorem Formula.realize_ofNames [L.Structure M] (v : ∀ s, α s → M s) {τ : Arity S}
    (φ : L.Formula τ) (names : ∀ s, τ.Idx s → α s) :
    (φ.ofNames names).RealizeWith v PUnit.unit ↔
      φ.Realize (Interpret.ofFn fun s => v s ∘ names s) := by
  simp only [Formula.ofNames, Formula.RealizeWith, Formula.realize_subst, Term.realize_ofFn,
    Term.realize_con, LHom.realize_onFormula]
  rfl

/-- Naming the positions of a relabelled formula names the positions of the formula. -/
theorem Formula.ofNames_relabel {σ τ : Arity S} (φ : L.Formula σ) (g : ∀ s, σ.Idx s → τ.Idx s)
    (names : ∀ s, τ.Idx s → α s) :
    (φ.relabel g).ofNames names = φ.ofNames fun s i => names s (g s i) := by
  simp only [Formula.ofNames, LHom.onFormula_relabel, Formula.subst_relabel, Term.get_ofFn]

theorem Formula.ofNames_top {τ : Arity S} (names : ∀ s, τ.Idx s → α s) :
    (⊤ : L.Formula τ).ofNames names = ⊤ :=
  rfl

theorem Formula.ofNames_inf {τ : Arity S} (φ ψ : L.Formula τ) (names : ∀ s, τ.Idx s → α s) :
    (φ ⊓ ψ).ofNames names = φ.ofNames names ⊓ ψ.ofNames names :=
  rfl

/-- A sentence with parameters, lifted to a context, holds of every tuple iff it holds. -/
theorem Formula.realizeWith_lift [L.Structure M] (v : ∀ s, α s → M s) {σ : Arity S}
    (φ : L[[α]].Sentence) (xs : M [^] σ) :
    (φ.lift : L[[α]].Formula σ).RealizeWith v xs ↔ φ.RealizeWith v PUnit.unit :=
  let := withConstantsStructure (L := L) v
  Sentence.realize_lift φ xs

/-- A formula of a realized set of formulas is realized. -/
theorem FormulaSet.Realize.realize_of_mem [L.Structure M] {σ : Arity S} {P : L.FormulaSet σ}
    {xs : M [^] σ} (h : P.Realize xs) {φ : L.Formula σ} (hφ : φ ∈ P) : φ.Realize xs :=
  h φ hφ

/-- `FormulaSet.Realize.realize_of_mem` with values for the parameters. -/
theorem FormulaSet.RealizeWith.realize_of_mem [L.Structure M] {v : ∀ s, α s → M s}
    {σ : Arity S} {P : L[[α]].FormulaSet σ} {xs : M [^] σ} (h : P.RealizeWith v xs)
    {φ : L[[α]].Formula σ} (hφ : φ ∈ P) : φ.RealizeWith v xs :=
  let := withConstantsStructure (L := L) v
  FormulaSet.Realize.realize_of_mem h hφ

/-- `Formula.realize_iInf` with values for the parameters. -/
theorem Formula.realizeWith_iInf [L.Structure M] (v : ∀ s, α s → M s) {σ : Arity S}
    {β : Type*} (s : Finset β) (f : β → L[[α]].Formula σ) (xs : M [^] σ) :
    (Formula.iInf s f).RealizeWith v xs ↔ ∀ b ∈ s, (f b).RealizeWith v xs :=
  let := withConstantsStructure (L := L) v
  Formula.realize_iInf s f

/-- Rename the parameters of a formula along `g`. -/
def Formula.mapParams {β : S → Type*} (g : ∀ s, α s → β s) {σ : Arity S}
    (φ : L[[α]].Formula σ) : L[[β]].Formula σ :=
  (L.lhomWithConstantsMap g).onFormula φ

@[simp]
theorem Formula.realize_mapParams [L.Structure M] {β : S → Type*} (g : ∀ s, α s → β s)
    (v : ∀ s, β s → M s) {σ : Arity S} (φ : L[[α]].Formula σ) (xs : M [^] σ) :
    (φ.mapParams g).RealizeWith v xs ↔ φ.RealizeWith (fun s => v s ∘ g s) xs :=
  @LHom.realize_onFormula _ _ _ M _ (withConstantsStructure _) (withConstantsStructure v)
    (isExpansionOn_lhomWithConstantsMap g v) σ φ xs

end ManySorted.Language
