/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Semantics

/-!
# Many-sorted first-order logic: named free variables

Terms and formulas with named free variables, as a layer on top of the positional terms and
formulas of `Syntax.lean` and `Semantics.lean`.

## Main declarations

* `Language.BoundedTerm L α σ τ` and `Language.BoundedFormula L α σ`: terms and formulas with named
  variables in a family `α` and positional variables in `σ`. `L.FSet α σ` is a set of named
  formulas.
* `BoundedTerm.realize`, `BoundedFormula.Realize`, `FSet.IsSatisfiable`: realization of the named
  layer.
* `Language.qfDiagram N`, `Embedding.ofRealizeQFDiagram` and `Embedding.realize_qfDiagram`: a
  family of maps `N → M` realizing the quantifier-free diagram of `N` is an embedding, and every
  embedding realizes it.
-/

@[expose] public section

universe u v w w' z u' v'

namespace ManySorted

open Arity

namespace Language

variable {S : Type z} {L : Language.{u, v} S}

/-! ### Named free variables

A named formula `ψ : L.BoundedFormula α σ` is a positional formula in context `ψ.ctx ⨯ σ`
together with a name in `α` for each position of `ψ.ctx`; named terms are stored the same way.
`α` can be any family, for instance the carrier of a structure, and realization takes values
`v : ∀ s, α s → M s` for the names directly. -/

section Named

variable {α : S → Type u'} {β : S → Type v'}

/-! ### Terms with named variables -/

variable (L) in
/-- A tuple of terms of shape `τ` with named variables in `α` and positional variables in `σ`,
stored as a positional tuple of terms in context `ctx ⨯ σ` together with a name for each position
of `ctx`. -/
structure BoundedTerm (α : S → Type u') (σ τ : Arity S) where
  /-- The arity of the named positions. -/
  ctx : Arity S
  /-- The name of each named position. -/
  names : ∀ s, ctx.Idx s → α s
  /-- The underlying positional tuple of terms. -/
  term : L.Term (ctx ⨯ σ) τ

namespace BoundedTerm

variable {σ τ τ' : Arity S}

/-- The tuple of named variables listed in `x`. -/
def vars (x : α [^] τ) : L.BoundedTerm α σ τ :=
  ⟨τ, x.get, Term.vars (Interpret.ofFn fun _ i => .left i)⟩

/-- A single named variable. -/
def var {s : S} (a : α s) : L.BoundedTerm α σ ⦃s⦄ := BoundedTerm.vars a

/-- A positional variable. -/
def bvar {s : S} (i : σ.Idx s) : L.BoundedTerm α σ ⦃s⦄ := ⟨⦃⦄, Idx.elimNil, .var (.right i)⟩

/-- A function symbol applied to a tuple of terms. -/
def func {t : S} (f : L.Functions τ t) (ts : L.BoundedTerm α σ τ) : L.BoundedTerm α σ ⦃t⦄ :=
  ⟨ts.ctx, ts.names, .func f ts.term⟩

/-- The pairing of two tuples; their named positions are placed side by side. -/
def prod (t₁ : L.BoundedTerm α σ τ) (t₂ : L.BoundedTerm α σ τ') : L.BoundedTerm α σ (τ ⨯ τ') :=
  ⟨t₁.ctx ⨯ t₂.ctx, Idx.elim t₁.names t₂.names,
    .prod (t₁.term.relabel (Idx.extendRight fun _ => .left))
      (t₂.term.relabel (Idx.extendRight fun _ => .right))⟩

/-- The empty tuple. -/
def nil : L.BoundedTerm α σ ⦃⦄ := ⟨⦃⦄, Idx.elimNil, .nil⟩

end BoundedTerm

/-! ### Named formulas -/

variable (L) in
/-- A formula with free variables named by `α` and bound variables in context `σ`, stored as a
positional formula in context `ctx ⨯ σ` together with a name for each position of `ctx`. -/
structure BoundedFormula (α : S → Type u') (σ : Arity S) where
  /-- The arity of the named positions. -/
  ctx : Arity S
  /-- The name of each named position. -/
  names : ∀ s, ctx.Idx s → α s
  /-- The underlying positional formula. -/
  formula : L.Formula (ctx ⨯ σ)

namespace BoundedFormula

variable {σ τ : Arity S}

/-- Rename the named variables. -/
def rename (g : ∀ s, α s → β s) (ψ : L.BoundedFormula α σ) : L.BoundedFormula β σ :=
  ⟨ψ.ctx, fun s => g s ∘ ψ.names s, ψ.formula⟩

/-- Lift a formula to a bounded formula. -/
def ofFormula (φ : L.Formula σ) : L.BoundedFormula α σ :=
  ⟨⦃⦄, (fun _ i => nomatch i), φ.relabel fun _ => .right⟩

/-- A positional formula in context `τ` with every position named: a named formula without
bound variables. -/
def ofNames (φ : L.Formula τ) (names : ∀ s, τ.Idx s → α s) : L.BoundedFormula α ⦃⦄ :=
  ⟨τ, names, φ.relabel fun _ => .left⟩

instance : Bot (L.BoundedFormula α σ) := ⟨ofFormula ⊥⟩

/-- Implication; the named positions of both sides are placed side by side. -/
def imp (ψ₁ ψ₂ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  ⟨ψ₁.ctx ⨯ ψ₂.ctx,Idx.elim ψ₁.names ψ₂.names,
    (ψ₁.formula.relabel (Idx.extendRight fun _ => .left)).imp
    (ψ₂.formula.relabel (Idx.extendRight fun _ => .right))⟩

/-- Universal quantification over a block of shape `τ`. -/
def all (τ : Arity S) (ψ : L.BoundedFormula α (σ ⨯ τ)) : L.BoundedFormula α σ :=
  ⟨ψ.ctx, ψ.names, Formula.all τ (ψ.formula.relabel Idx.assoc)⟩

/-- Negation. -/
protected def not (ψ : L.BoundedFormula α σ) : L.BoundedFormula α σ := ψ.imp ⊥

/-- Existential quantification over a block of shape `τ`. -/
protected def ex (τ : Arity S) (ψ : L.BoundedFormula α (σ ⨯ τ)) : L.BoundedFormula α σ :=
  (all τ ψ.not).not

instance : Top (L.BoundedFormula α σ) := ⟨(⊥ : L.BoundedFormula α σ).not⟩

instance : Min (L.BoundedFormula α σ) := ⟨fun ψ₁ ψ₂ => (ψ₁.imp ψ₂.not).not⟩

instance : Max (L.BoundedFormula α σ) := ⟨fun ψ₁ ψ₂ => ψ₁.not.imp ψ₂⟩

/-- Biimplication. -/
protected def iff (ψ₁ ψ₂ : L.BoundedFormula α σ) : L.BoundedFormula α σ := ψ₁.imp ψ₂ ⊓ ψ₂.imp ψ₁

section finite

variable {ι : Type*}

/-- The conjunction of finitely many named formulas. -/
noncomputable def iInf (s : Finset ι) (f : ι → L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  (s.toList.map f).foldr (· ⊓ ·) ⊤

/-- The disjunction of finitely many named formulas. -/
noncomputable def iSup (s : Finset ι) (f : ι → L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  (s.toList.map f).foldr (· ⊔ ·) ⊥

end finite

/-- Equality of two tuples of terms with named and positional variables. -/
def equal (t₁ t₂ : L.BoundedTerm α σ τ) : L.BoundedFormula α σ :=
  ⟨t₁.ctx ⨯ t₂.ctx, Idx.elim t₁.names t₂.names,
    .equal (t₁.term.relabel (Idx.extendRight fun _ => .left))
    (t₂.term.relabel (Idx.extendRight fun _ => .right))⟩

/-- A relation symbol applied to a tuple of terms with named and positional variables. -/
def rel (R : L.Relations τ) (ts : L.BoundedTerm α σ τ) : L.BoundedFormula α σ :=
  ⟨ts.ctx, ts.names, .rel R ts.term⟩

/-! ### Quantifier-free named formulas -/

/-- A named formula is quantifier-free when its positional formula is. -/
def IsQF (ψ : L.BoundedFormula α σ) : Prop := ψ.formula.IsQF

theorem isQF_bot : (⊥ : L.BoundedFormula α σ).IsQF := .falsum

theorem IsQF.imp {ψ₁ ψ₂ : L.BoundedFormula α σ} (h₁ : ψ₁.IsQF) (h₂ : ψ₂.IsQF) :
    (ψ₁.imp ψ₂).IsQF :=
  Formula.IsQF.imp (h₁.relabel _) (h₂.relabel _)

theorem IsQF.not {ψ : L.BoundedFormula α σ} (h : ψ.IsQF) : ψ.not.IsQF := h.imp isQF_bot

theorem isQF_equal (t₁ t₂ : L.BoundedTerm α σ τ) : (equal t₁ t₂).IsQF :=
  .of_isAtomic (.equal _ _)

theorem isQF_rel (R : L.Relations τ) (ts : L.BoundedTerm α σ τ) :
    (rel R ts).IsQF :=
  .of_isAtomic (.rel _ _)

end BoundedFormula

/-! ### Sets of named formulas -/

variable (L) in
/-- A set of formulas with names in `α` and bound variables in `σ`. Used to encode the syntactic
content of a partial type in shape `σ` over variables `α`. -/
abbrev FSet (α : S → Type u') (σ : Arity S) := Set (L.BoundedFormula α σ)

namespace FSet

variable {σ : Arity S}

/-- Rename the named variables of every formula. -/
def rename (g : ∀ s, α s → β s) (p : L.FSet α σ) : L.FSet β σ := BoundedFormula.rename g '' p

end FSet

end Named

open Structure

variable {M : S → Type w} [L.Structure M]

/-! ### Realization of named terms and formulas -/

section Named

variable {α : S → Type u'} {β : S → Type v'}

namespace BoundedTerm

variable {σ τ τ' : Arity S}

/-- Evaluate with values `v` for the names and `xs` for the positional variables. -/
def realize (t : L.BoundedTerm α σ τ) (v : ∀ s, α s → M s) (xs : M [^] σ) : M [^] τ :=
  t.term.realize (Interpret.ofFn (fun s => v s ∘ t.names s), xs)

@[simp]
theorem realize_nil (v : ∀ s, α s → M s) (xs : M [^] σ) :
    (nil : L.BoundedTerm α σ ⦃⦄).realize v xs = PUnit.unit := rfl

section realize

variable (v : ∀ s, α s → M s) (xs : M [^] σ)

@[simp]
theorem realize_var {s : S} (a : α s) :
    (var a : L.BoundedTerm α σ ⦃s⦄).realize v xs = v s a := rfl

@[simp]
theorem realize_bvar {s : S} (i : σ.Idx s) :
    (bvar i : L.BoundedTerm α σ ⦃s⦄).realize v xs = xs.get s i := rfl

@[simp]
theorem realize_func {t : S} (f : L.Functions τ t) (ts : L.BoundedTerm α σ τ) :
    (func f ts).realize v xs = funMap f (ts.realize v xs) := rfl

@[simp]
theorem realize_prod (t₁ : L.BoundedTerm α σ τ) (t₂ : L.BoundedTerm α σ τ') :
    (prod t₁ t₂).realize v xs = (t₁.realize v xs, t₂.realize v xs) :=
  congrArg₂ Prod.mk
    (Term.realize_relabel_of_get_eq (Interpret.get_ofFn_elim_left t₁.names t₂.names v xs) _)
    (Term.realize_relabel_of_get_eq (Interpret.get_ofFn_elim_right t₁.names t₂.names v xs) _)

@[simp]
theorem realize_vars (x : α [^] τ) :
    (vars x : L.BoundedTerm α σ τ).realize v xs = x.map v :=
  Interpret.ext fun s i => by simp [realize, vars]

end realize

end BoundedTerm

namespace BoundedFormula

variable {σ τ : Arity S}

/-- `ψ.Realize v xs`: `ψ` holds with values `v` for the names and `xs` for the bound variables. -/
def Realize (ψ : L.BoundedFormula α σ) (v : ∀ s, α s → M s) (xs : M [^] σ) : Prop :=
  ψ.formula.Realize (Interpret.ofFn (fun s => v s ∘ ψ.names s), xs)

@[simp]
theorem realize_rename (g : ∀ s, α s → β s) (ψ : L.BoundedFormula α σ)
    (v : ∀ s, β s → M s) (xs : M [^] σ) :
    (ψ.rename g).Realize v xs ↔ ψ.Realize (fun s => v s ∘ g s) xs := Iff.rfl

@[simp]
theorem realize_ofFormula (φ : L.Formula σ) (v : ∀ s, α s → M s) (xs : M [^] σ) :
    (ofFormula φ : L.BoundedFormula α σ).Realize v xs ↔ φ.Realize xs :=
  Formula.realize_relabel_of_get_eq φ fun _ _ => rfl

@[simp]
theorem realize_ofNames (φ : L.Formula τ) (names : ∀ s, τ.Idx s → α s)
    (v : ∀ s, α s → M s) (xs : M [^] ⦃⦄) :
    (ofNames φ names).Realize v xs ↔ φ.Realize (Interpret.ofFn fun s => v s ∘ names s) :=
  Formula.realize_relabel_of_get_eq φ fun _ _ => rfl

@[simp]
theorem realize_bot (v : ∀ s, α s → M s) (xs : M [^] σ) :
    (⊥ : L.BoundedFormula α σ).Realize v xs ↔ False := Iff.rfl

@[simp]
theorem realize_imp (ψ₁ ψ₂ : L.BoundedFormula α σ) (v : ∀ s, α s → M s) (xs : M [^] σ) :
    (ψ₁.imp ψ₂).Realize v xs ↔ (ψ₁.Realize v xs → ψ₂.Realize v xs) :=
  imp_congr
    (Formula.realize_relabel_of_get_eq _ (Interpret.get_ofFn_elim_left ψ₁.names ψ₂.names v xs))
    (Formula.realize_relabel_of_get_eq _ (Interpret.get_ofFn_elim_right ψ₁.names ψ₂.names v xs))

@[simp]
theorem realize_all (ψ : L.BoundedFormula α (σ ⨯ τ)) (v : ∀ s, α s → M s)
    (xs : M [^] σ) : (all τ ψ).Realize v xs ↔ ∀ ys : M [^] τ, ψ.Realize v (xs, ys) :=
  forall_congr' fun _ => Formula.realize_relabel_of_get_eq _ fun s i => by
    cases i with
    | left i => rfl
    | right j => cases j <;> rfl

@[simp]
theorem realize_not (ψ : L.BoundedFormula α σ) (v : ∀ s, α s → M s) (xs : M [^] σ) :
    ψ.not.Realize v xs ↔ ¬ψ.Realize v xs := by
  simp [BoundedFormula.not]

@[simp]
theorem realize_ex (ψ : L.BoundedFormula α (σ ⨯ τ)) (v : ∀ s, α s → M s)
    (xs : M [^] σ) : (ψ.ex τ).Realize v xs ↔ ∃ ys : M [^] τ, ψ.Realize v (xs, ys) := by
  simp [BoundedFormula.ex]

@[simp]
theorem realize_top (v : ∀ s, α s → M s) (xs : M [^] σ) :
    (⊤ : L.BoundedFormula α σ).Realize v xs ↔ True := by
  change (⊥ : L.BoundedFormula α σ).not.Realize v xs ↔ True
  simp

@[simp]
theorem realize_inf (ψ₁ ψ₂ : L.BoundedFormula α σ) (v : ∀ s, α s → M s) (xs : M [^] σ) :
    (ψ₁ ⊓ ψ₂).Realize v xs ↔ ψ₁.Realize v xs ∧ ψ₂.Realize v xs := by
  change (ψ₁.imp ψ₂.not).not.Realize v xs ↔ _
  simp

@[simp]
theorem realize_sup (ψ₁ ψ₂ : L.BoundedFormula α σ) (v : ∀ s, α s → M s) (xs : M [^] σ) :
    (ψ₁ ⊔ ψ₂).Realize v xs ↔ ψ₁.Realize v xs ∨ ψ₂.Realize v xs := by
  change (ψ₁.not.imp ψ₂).Realize v xs ↔ _
  simp only [realize_imp, realize_not]
  tauto

@[simp]
theorem realize_iff (ψ₁ ψ₂ : L.BoundedFormula α σ) (v : ∀ s, α s → M s) (xs : M [^] σ) :
    (ψ₁.iff ψ₂).Realize v xs ↔ (ψ₁.Realize v xs ↔ ψ₂.Realize v xs) := by
  simp only [BoundedFormula.iff, realize_inf, realize_imp]
  tauto

section finite

variable {ι : Type*} (v : ∀ s, α s → M s) (xs : M [^] σ)

theorem realize_foldr_inf (l : List (L.BoundedFormula α σ)) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ ∀ ψ ∈ l, ψ.Realize v xs := by
  induction l with
  | nil => simp
  | cons ψ l ih => simp [ih]

theorem realize_foldr_sup (l : List (L.BoundedFormula α σ)) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ ψ ∈ l, ψ.Realize v xs := by
  induction l with
  | nil => simp
  | cons ψ l ih => simp [ih]

@[simp]
theorem realize_iInf (s : Finset ι) (f : ι → L.BoundedFormula α σ) :
    (iInf s f).Realize v xs ↔ ∀ i ∈ s, (f i).Realize v xs := by
  simp [iInf, realize_foldr_inf]

@[simp]
theorem realize_iSup (s : Finset ι) (f : ι → L.BoundedFormula α σ) :
    (iSup s f).Realize v xs ↔ ∃ i ∈ s, (f i).Realize v xs := by
  simp [iSup, realize_foldr_sup]

end finite

@[simp]
theorem realize_equal (t₁ t₂ : L.BoundedTerm α σ τ) (v : ∀ s, α s → M s) (xs : M [^] σ) :
    (equal t₁ t₂).Realize v xs ↔ t₁.realize v xs = t₂.realize v xs :=
  Iff.of_eq (congrArg₂ (· = ·)
    (Term.realize_relabel_of_get_eq (Interpret.get_ofFn_elim_left t₁.names t₂.names v xs) _)
    (Term.realize_relabel_of_get_eq (Interpret.get_ofFn_elim_right t₁.names t₂.names v xs) _))

@[simp]
theorem realize_rel (R : L.Relations τ) (ts : L.BoundedTerm α σ τ) (v : ∀ s, α s → M s)
    (xs : M [^] σ) : (rel R ts).Realize v xs ↔ RelMap R (ts.realize v xs) := Iff.rfl

end BoundedFormula

section HomBounded

theorem StrongHomClass.realizeBoundedFormula_of_isQF {N : S → Type w'} {F : Type*} {σ : Arity S}
    {ψ : L.BoundedFormula α σ} [L.Structure N] [DFunLike F S fun s => M s → N s]
    [StrongHomClass L F M N] (g : F) (hinj : ∀ s, Function.Injective (g s)) (h : ψ.IsQF)
     (v : ∀ s, α s → M s) (xs : M [^] σ) :
  ψ.Realize (fun s => g s ∘ v s) (xs.map g) ↔ ψ.Realize v xs := by
  have : ((Interpret.ofFn fun s => (g s ∘ v s) ∘ ψ.names s, xs.map g) : N [^] (ψ.ctx ⨯ σ)) =
      Interpret.map (σ := ψ.ctx ⨯ σ) g (Interpret.ofFn fun s => v s ∘ ψ.names s, xs) :=
    congrArg (·, xs.map g) (Interpret.map_ofFn g fun s => v s ∘ ψ.names s).symm
  rw [BoundedFormula.Realize, this]
  exact StrongHomClass.realize_of_isQF g hinj h _

theorem Embedding.realizeBoundedFormula_of_isQF {N : S → Type w'} [L.Structure N] (g : M ↪[L] N)
    {σ : Arity S} {ψ : L.BoundedFormula α σ} (h : ψ.IsQF) (v : ∀ s, α s → M s) (xs : M [^] σ) :
    ψ.Realize (fun s => g s ∘ v s) (xs.map g) ↔ ψ.Realize v xs :=
  StrongHomClass.realizeBoundedFormula_of_isQF g g.injective h _ _

end HomBounded

namespace FSet

variable {σ : Arity S}

/-- Every formula of `p` holds with values `v` for the names and `xs` for the bound variables. -/
def Realize (p : L.FSet α σ) (v : ∀ s, α s → M s) (xs : M [^] σ) : Prop :=
  ∀ ψ ∈ p, ψ.Realize v xs

@[simp]
theorem realize_rename (g : ∀ s, α s → β s) (p : L.FSet α σ) (v : ∀ s, β s → M s)
    (xs : M [^] σ) : (p.rename g).Realize v xs ↔ p.Realize (fun s => v s ∘ g s) xs :=
  Set.forall_mem_image

theorem Realize.mono {p q : L.FSet α σ} {v : ∀ s, α s → M s} {xs : M [^] σ}
    (h : q.Realize v xs) (hpq : p ⊆ q) : p.Realize v xs :=
  fun ψ hψ => h ψ (hpq hψ)

/-- `p` is realized in some structure with nonempty sorts, taken in the universe
`max z u v u'`. Nonempty sorts are the convention of Mathlib's one-sorted development, and Łoś's
theorem needs them. -/
def IsSatisfiable (p : L.FSet α σ) : Prop :=
  ∃ (N : S → Type (max z u v u')) (_ : L.Structure N) (_ : ∀ s, Nonempty (N s))
    (v : ∀ s, α s → N s) (xs : N [^] σ), p.Realize v xs

end FSet

/-! ### The quantifier-free diagram -/

variable (L) in
/-- The quantifier-free diagram of `N`: the quantifier-free formulas with parameters from `N`
that hold in `N`. -/
def qfDiagram (N : S → Type w') [L.Structure N] : L.FSet N ⦃⦄ :=
  {ψ | ψ.IsQF ∧ ψ.Realize (fun _ => id) PUnit.unit}

variable {N : S → Type w'} [L.Structure N]

/-- A family of maps `N → M` realizing the quantifier-free diagram of `N` is an
embedding. -/
def Embedding.ofRealizeQFDiagram (v : ∀ s, N s → M s)
    (h : (L.qfDiagram N).Realize v PUnit.unit) : N ↪[L] M where
  toEmbedding s := ⟨v s, fun a b hab => by_contra fun hne => by
    have := h (BoundedFormula.equal (BoundedTerm.var a) (BoundedTerm.var b)).not
      ⟨(BoundedFormula.isQF_equal _ _).not, by simpa using hne⟩
    simp [hab] at this⟩
  map_fun' {σ t} f x := by
    have := h (BoundedFormula.equal (BoundedTerm.func f (BoundedTerm.vars x))
      (BoundedTerm.var (funMap f x))) ⟨BoundedFormula.isQF_equal _ _, by simp⟩
    simp at this
    exact this.symm
  map_rel' {σ} R x := by
    have hR := fun hx => h (BoundedFormula.rel R (BoundedTerm.vars x))
      ⟨BoundedFormula.isQF_rel _ _, by simpa using hx⟩
    have hnR := fun hx => h (BoundedFormula.rel R (BoundedTerm.vars x)).not
      ⟨(BoundedFormula.isQF_rel _ _).not, by simpa using hx⟩
    simp only [BoundedFormula.realize_not, BoundedFormula.realize_rel,
      BoundedTerm.realize_vars] at hR hnR
    exact ⟨fun h' => by_contra fun hn => hnR hn h', hR⟩

@[simp]
theorem Embedding.coe_ofRealizeQFDiagram (v : ∀ s, N s → M s)
    (h : (L.qfDiagram N).Realize v PUnit.unit) : ⇑(Embedding.ofRealizeQFDiagram v h) = v :=
  rfl

/-- An injective strong homomorphism realizes the quantifier-free diagram of its domain. -/
theorem StrongHomClass.realize_qfDiagram {F : Type*} [DFunLike F S fun s => N s → M s]
    [StrongHomClass L F N M] (g : F) (hinj : ∀ s, Function.Injective (g s)) :
    (L.qfDiagram N).Realize g PUnit.unit :=
  fun _ ⟨hqf, hψ⟩ =>
    (StrongHomClass.realizeBoundedFormula_of_isQF g hinj hqf (fun _ => id) PUnit.unit).2 hψ

/-- An embedding realizes the quantifier-free diagram of its domain. -/
theorem Embedding.realize_qfDiagram (g : N ↪[L] M) : (L.qfDiagram N).Realize g PUnit.unit :=
  StrongHomClass.realize_qfDiagram g g.injective

end Named

end Language

end ManySorted
