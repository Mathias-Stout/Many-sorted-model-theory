/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson
-/
module

public import MultisortedLogic.CompleteTheories
public import MultisortedLogic.Quotients

/-!
# The Henkin construction

A *Henkin theory* is a finitely satisfiable theory that contains every sentence or its negation and
has a witness, a tuple of closed terms, for each existential sentence it contains. Such a theory
has a canonical model, its *term model*: the closed terms, with two of them identified when the
theory contains their equality. A sentence holds in the term model exactly when it belongs to the
theory.

The construction does not use the compactness theorem. The only models it appeals to are those of
finite subsets of the theory, through `Theory.IsHenkin.mem_of_models`: a Henkin theory contains
every consequence of each of its finite subsets (Marker, Lemma 2.1.6). Every other membership in
the theory is derived from this one, so no syntactic identity between substituted formulas is ever
needed.

## Main definitions

* `Term.tuple`: a tuple of single terms, as a tuple of terms.
* `Theory.IsHenkin T`: `T` is a Henkin theory.
* `ClosedTerm T`: the closed terms, with the `L`-structure in which a relation holds of a tuple
  when `T` contains the corresponding atomic sentence. It is a one-field structure and not a plain
  synonym, so that this `L`-structure, which depends on `T`, can be an instance.
* `Theory.IsHenkin.setoid`: the equivalence relation on closed terms, a congruence of that
  structure.
* `Theory.IsHenkin.TermModel`: the term model, the quotient of the closed terms.

## Main results

* `Theory.IsHenkin.mem_of_models`: a Henkin theory contains the consequences of its finite subsets.
* `Theory.IsHenkin.exists_realize_eq`: every tuple of the term model is the value of a tuple of
  closed terms.
* `Theory.IsHenkin.realize_iff_subst_mem`: the truth lemma. A formula holds in the term model at
  the value of a tuple of closed terms iff the theory contains the formula with those terms
  substituted.
* `Theory.IsHenkin.realize_sentence_iff`: a sentence holds in the term model iff the theory
  contains it.
* `Theory.IsHenkin.isSatisfiable`, `Theory.IsHenkin.isMaximal`: a Henkin theory is satisfiable,
  hence maximal.

## Implementation notes

The witness property is stated for blocks of variables: an existential sentence `∃ ys, φ(ys)` over
a block of shape `τ` has a witness `d : L.Term ⦃⦄ τ`. Formulas quantify over blocks, so this is the
form the truth lemma uses.

## References

* David Marker, *Model Theory: An Introduction*, Graduate Texts in Mathematics 217, Springer,
  2002. Section 2.1.
-/

@[expose] public section

universe u v z

namespace ManySorted.Language

open Arity Structure

variable {S : Type z} {L : Language.{u, v} S}

/-! ### Tuples of terms -/

namespace Term

variable {Γ : Arity S}

/-- A tuple of single terms, as a tuple of terms. -/
def tuple : ∀ {σ : Arity S}, (fun s => L.Term Γ ⦃s⦄) [^] σ → L.Term Γ σ
  | .nil, _ => nil
  | .of _, t => t
  | .prod _ _, x => prod (tuple x.1) (tuple x.2)

@[simp]
theorem get_tuple : ∀ {σ : Arity S} (x : (fun s => L.Term Γ ⦃s⦄) [^] σ) (s : S) (i : σ.Idx s),
    (tuple x).get s i = x.get s i
  | .of _, t, _, .var => get_var t
  | .prod _ _, x, _, .left i => get_tuple x.1 _ i
  | .prod _ _, x, _, .right i => get_tuple x.2 _ i

/-- A tuple of terms is determined by its entries. -/
theorem ext_get : ∀ {σ : Arity S} {t u : L.Term Γ σ}, (∀ s i, t.get s i = u.get s i) → t = u
  | .nil, nil, nil, _ => rfl
  | .of s, t, u, h => by simpa only [get_var] using h s .var
  | .prod _ _, prod _ _, prod _ _, h =>
    congrArg₂ prod (ext_get fun s i => h s (.left i)) (ext_get fun s i => h s (.right i))

theorem tuple_injective {σ : Arity S} :
    Function.Injective (tuple : (fun s => L.Term Γ ⦃s⦄) [^] σ → L.Term Γ σ) := fun x y h =>
  Interpret.ext fun s i => by rw [← get_tuple x, ← get_tuple y, h]

/-- A tuple of terms is the tuple of its entries. -/
@[simp]
theorem tuple_ofFn_get {σ : Arity S} (t : L.Term Γ σ) :
    tuple (Interpret.ofFn (M := fun s => L.Term Γ ⦃s⦄) t.get) = t :=
  ext_get fun s i => by rw [get_tuple, Interpret.get_ofFn]

end Term

namespace Theory

/-! ### Henkin theories -/

/-- A Henkin theory: a finitely satisfiable theory that contains every sentence or its negation,
and a witness for each existential sentence it contains. -/
structure IsHenkin (T : L.Theory) : Prop where
  /-- Every finite subset of `T` has a model. -/
  isFinitelySatisfiable : T.IsFinitelySatisfiable
  /-- `T` contains every sentence or its negation. -/
  mem_or_not_mem (φ : L.Sentence) : φ ∈ T ∨ φ.not ∈ T
  /-- If `T` contains `∃ ys, φ(ys)`, it contains `φ(d)` for some tuple `d` of closed terms. -/
  exists_witness (τ : Arity S) (φ : L.Formula (⦃⦄ ⨯ τ)) :
    φ.ex τ ∈ T → ∃ d : L.Term ⦃⦄ τ, φ.subst (Term.nil.prod d) ∈ T

namespace IsHenkin

variable {T : L.Theory} (h : T.IsHenkin)
include h

/-! ### Closure under consequence -/

/-- **A Henkin theory contains the consequences of its finite subsets.** Otherwise it would contain
the negation of one, and the finite subset together with that negation would have a model. -/
theorem mem_of_models {φ : L.Sentence} (Δ : Finset L.Sentence) (hΔ : (Δ : L.Theory) ⊆ T)
    (hφ : FormulaSet.Models (Δ : L.Theory) φ) : φ ∈ T := by
  classical
  refine (h.mem_or_not_mem φ).resolve_right fun hn => ?_
  obtain ⟨r⟩ := h.isFinitelySatisfiable (insert φ.not Δ) (by
    rw [Finset.coe_insert]
    exact Set.insert_subset hn hΔ)
  exact r.realize φ.not (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    (hφ (r.restrict (Finset.coe_subset.2 (Finset.subset_insert _ _))))

/-- A Henkin theory contains the sentences that hold in every structure. -/
theorem mem_of_forall {φ : L.Sentence}
    (hφ : ∀ (M : S → Type (max z u v)) [L.Structure M] [∀ s, Nonempty (M s)], M ⊨ φ) : φ ∈ T :=
  h.mem_of_models ∅ (by simp) fun r => hφ r.carrier

/-- A Henkin theory contains the consequences of each of its sentences. -/
theorem mem_of_mem {φ ψ : L.Sentence} (hφ : φ ∈ T)
    (H : ∀ (M : S → Type (max z u v)) [L.Structure M] [∀ s, Nonempty (M s)], M ⊨ φ → M ⊨ ψ) :
    ψ ∈ T :=
  h.mem_of_models {φ} (by simpa using hφ) fun r => H r.carrier (r.realize φ (by simp))

/-- A Henkin theory contains the consequences of each pair of its sentences. -/
theorem mem_of_mem_of_mem {φ₁ φ₂ ψ : L.Sentence} (h₁ : φ₁ ∈ T) (h₂ : φ₂ ∈ T)
    (H : ∀ (M : S → Type (max z u v)) [L.Structure M] [∀ s, Nonempty (M s)],
      M ⊨ φ₁ → M ⊨ φ₂ → M ⊨ ψ) : ψ ∈ T := by
  classical
  exact h.mem_of_models {φ₁, φ₂} (by simp [Set.insert_subset_iff, h₁, h₂]) fun r =>
    H r.carrier (r.realize φ₁ (by simp)) (r.realize φ₂ (by simp))

/-- A Henkin theory is consistent. -/
theorem bot_notMem : (⊥ : L.Sentence) ∉ T := fun hb => by
  obtain ⟨r⟩ := h.isFinitelySatisfiable {⊥} (by simpa using hb)
  exact Formula.realize_bot.1 (r.realize ⊥ (by simp))

/-- A Henkin theory contains the negation of a sentence exactly when it does not contain the
sentence. -/
theorem not_mem_iff (φ : L.Sentence) : φ.not ∈ T ↔ φ ∉ T :=
  ⟨fun hn hφ => h.bot_notMem (h.mem_of_mem_of_mem hφ hn fun _ _ _ h₁ h₂ =>
    (Formula.realize_not.1 h₂ h₁).elim), (h.mem_or_not_mem φ).resolve_left⟩

/-- A Henkin theory contains an implication exactly when it contains the conclusion if it contains
the hypothesis. -/
theorem imp_mem_iff (φ ψ : L.Sentence) : φ.imp ψ ∈ T ↔ (φ ∈ T → ψ ∈ T) := by
  constructor
  · exact fun hi hφ => h.mem_of_mem_of_mem hi hφ fun _ _ _ h₁ h₂ => Formula.realize_imp.1 h₁ h₂
  · intro H
    rcases h.mem_or_not_mem φ with hφ | hφ
    · exact h.mem_of_mem (H hφ) fun _ _ _ hψ => Formula.realize_imp.2 fun _ => hψ
    · exact h.mem_of_mem hφ fun _ _ _ hn =>
        Formula.realize_imp.2 fun hφ => (Formula.realize_not.1 hn hφ).elim

/-- A Henkin theory contains an equality of tuples of closed terms exactly when it contains the
equality of each pair of entries. -/
theorem equal_mem_iff : ∀ {σ : Arity S} (a b : L.Term ⦃⦄ σ),
    Formula.equal a b ∈ T ↔ ∀ s i, Formula.equal (a.get s i) (b.get s i) ∈ T
  | .nil, .nil, .nil =>
    iff_of_true (h.mem_of_forall fun _ _ _ => (Formula.realize_equal _ _).2 rfl)
      fun _ i => nomatch i
  | .of s, a, b =>
    ⟨fun H _ i => by cases i; simpa only [Term.get_var] using H,
      fun H => by simpa only [Term.get_var] using H s .var⟩
  | .prod _ _, .prod a₁ a₂, .prod b₁ b₂ => by
    have e : Formula.equal (a₁.prod a₂) (b₁.prod b₂) ∈ T ↔
        Formula.equal a₁ b₁ ∈ T ∧ Formula.equal a₂ b₂ ∈ T :=
      ⟨fun H => ⟨h.mem_of_mem H fun _ _ _ e => (Formula.realize_equal _ _).2
          (Prod.mk.inj ((Formula.realize_equal _ _).1 e)).1,
        h.mem_of_mem H fun _ _ _ e => (Formula.realize_equal _ _).2
          (Prod.mk.inj ((Formula.realize_equal _ _).1 e)).2⟩,
      fun ⟨H₁, H₂⟩ => h.mem_of_mem_of_mem H₁ H₂ fun _ _ _ e₁ e₂ => (Formula.realize_equal _ _).2
        (congrArg₂ Prod.mk ((Formula.realize_equal _ _).1 e₁) ((Formula.realize_equal _ _).1 e₂))⟩
    rw [e, equal_mem_iff a₁ b₁, equal_mem_iff a₂ b₂]
    exact ⟨fun ⟨H₁, H₂⟩ s i => by cases i with
      | left i => exact H₁ s i
      | right i => exact H₂ s i, fun H => ⟨fun s i => H s (.left i), fun s i => H s (.right i)⟩⟩

end IsHenkin

end Theory

/-! ### The structure on the closed terms -/

/-- A closed term of sort `s`. The theory `T` is a phantom parameter: it selects the `L`-structure
on the closed terms, in which a relation holds of a tuple when `T` contains the corresponding
atomic sentence. -/
@[ext]
structure ClosedTerm (T : L.Theory) (s : S) : Type (max z u) where
  /-- The underlying term. -/
  term : L.Term ⦃⦄ ⦃s⦄

namespace ClosedTerm

variable {T : L.Theory} {σ : Arity S}

/-- The tuple of terms underlying a tuple of closed terms. -/
def terms (x : ClosedTerm T [^] σ) : L.Term ⦃⦄ σ :=
  Term.tuple (x.map fun _ a => a.term)

@[simp]
theorem get_terms (x : ClosedTerm T [^] σ) (s : S) (i : σ.Idx s) :
    (terms x).get s i = (x.get s i).term := by
  rw [terms, Term.get_tuple, Interpret.get_map]

theorem terms_injective : Function.Injective (terms : ClosedTerm T [^] σ → L.Term ⦃⦄ σ) :=
  Term.tuple_injective.comp (Interpret.map_injective fun _ _ _ => ClosedTerm.ext)

instance : L.Structure (ClosedTerm T) where
  funMap f x := ⟨Term.func f (terms x)⟩
  RelMap R x := Formula.rel R (terms x) ∈ T

theorem funMap_def {t : S} (f : L.Functions σ t) (x : ClosedTerm T [^] σ) :
    funMap f x = ⟨Term.func f (terms x)⟩ := rfl

theorem relMap_iff (R : L.Relations σ) (x : ClosedTerm T [^] σ) :
    RelMap R x ↔ Formula.rel R (terms x) ∈ T := Iff.rfl

variable (T) in
/-- In the structure on the closed terms, a tuple of closed terms is its own value. -/
@[simp]
theorem terms_realize : ∀ {σ : Arity S} (t : L.Term ⦃⦄ σ),
    terms (t.realize (M := ClosedTerm T) PUnit.unit) = t
  | _, .var i => nomatch i
  | _, .func f ts => congrArg (Term.func f) (terms_realize ts)
  | _, .nil => rfl
  | _, .prod t₁ t₂ => congrArg₂ Term.prod (terms_realize t₁) (terms_realize t₂)

/-- A tuple of closed terms is the value of its underlying tuple of terms. -/
@[simp]
theorem realize_terms (x : ClosedTerm T [^] σ) :
    (terms x).realize (M := ClosedTerm T) PUnit.unit = x :=
  terms_injective (terms_realize T _)

end ClosedTerm

namespace Theory.IsHenkin

variable {T : L.Theory} (h : T.IsHenkin)

/-! ### The term model -/

/-- Two closed terms are identified when the theory contains their equality. -/
def setoid (s : S) : Setoid (ClosedTerm T s) where
  r a b := Formula.equal a.term b.term ∈ T
  iseqv :=
    ⟨fun _ => h.mem_of_forall fun _ _ _ => (Formula.realize_equal _ _).2 rfl,
      fun hab => h.mem_of_mem hab fun _ _ _ e =>
        (Formula.realize_equal _ _).2 ((Formula.realize_equal _ _).1 e).symm,
      fun hab hbc => h.mem_of_mem_of_mem hab hbc fun _ _ _ e₁ e₂ =>
        (Formula.realize_equal _ _).2
          (((Formula.realize_equal _ _).1 e₁).trans ((Formula.realize_equal _ _).1 e₂))⟩

theorem setoid_r_iff {s : S} (a b : ClosedTerm T s) :
    (h.setoid s).r a b ↔ Formula.equal a.term b.term ∈ T := Iff.rfl

/-- Tuples of closed terms are identified entrywise exactly when the theory contains the equality
of their underlying tuples of terms. -/
theorem setoid_r_iff_equal_mem {σ : Arity S} (x y : ClosedTerm T [^] σ) :
    (Interpret.setoid h.setoid σ).r x y ↔
      Formula.equal (ClosedTerm.terms x) (ClosedTerm.terms y) ∈ T := by
  rw [h.equal_mem_iff]
  exact forall₂_congr fun s i => by
    rw [ClosedTerm.get_terms, ClosedTerm.get_terms]
    exact h.setoid_r_iff _ _

/-- The identification of closed terms is compatible with the function and relation symbols. -/
instance congruence : L.Congruence h.setoid where
  funMap_rel f _ _ hxy := h.mem_of_mem ((h.setoid_r_iff_equal_mem _ _).1 hxy) fun _ _ _ e =>
    (Formula.realize_equal _ _).2 (congrArg (funMap f) ((Formula.realize_equal _ _).1 e))
  relMap_iff _ _ _ hxy :=
    ⟨fun H => h.mem_of_mem_of_mem ((h.setoid_r_iff_equal_mem _ _).1 hxy) H fun _ _ _ e hR =>
        (Formula.realize_rel _ _).2
          ((Formula.realize_equal _ _).1 e ▸ (Formula.realize_rel _ _).1 hR),
      fun H => h.mem_of_mem_of_mem ((h.setoid_r_iff_equal_mem _ _).1 hxy) H fun _ _ _ e hR =>
        (Formula.realize_rel _ _).2
          (((Formula.realize_equal _ _).1 e).symm ▸ (Formula.realize_rel _ _).1 hR)⟩

/-- The term model of a Henkin theory: the closed terms, two of them identified when the theory
contains their equality. -/
abbrev TermModel : S → Type (max z u) := fun s => Quotient (h.setoid s)

/-- In the term model, the value of a tuple of closed terms is the tuple of the classes of its
entries. -/
theorem realize_closed {σ : Arity S} (t : L.Term ⦃⦄ σ) :
    t.realize (M := h.TermModel) PUnit.unit =
      Interpret.mkQuot h.setoid (t.realize (M := ClosedTerm T) PUnit.unit) :=
  Term.realize_mkQuot (r := h.setoid) t (PUnit.unit : ClosedTerm T [^] ⦃⦄)

/-- **Every tuple of the term model is the value of a tuple of closed terms.** -/
theorem exists_realize_eq {σ : Arity S} (ys : h.TermModel [^] σ) :
    ∃ d : L.Term ⦃⦄ σ, d.realize (M := h.TermModel) PUnit.unit = ys := by
  obtain ⟨x, rfl⟩ := Interpret.map_surjective (f := fun s => Quotient.mk (h.setoid s))
    (fun _ _ => Quotient.mk_surjective) ys
  exact ⟨ClosedTerm.terms x, by rw [h.realize_closed, ClosedTerm.realize_terms]⟩

/-- Two tuples of closed terms have the same value in the term model exactly when the theory
contains their equality. -/
theorem realize_eq_iff {σ : Arity S} (a b : L.Term ⦃⦄ σ) :
    a.realize (M := h.TermModel) PUnit.unit = b.realize PUnit.unit ↔ Formula.equal a b ∈ T := by
  rw [h.realize_closed, h.realize_closed, Interpret.mkQuot_eq_iff, h.setoid_r_iff_equal_mem,
    ClosedTerm.terms_realize, ClosedTerm.terms_realize]

/-- A relation holds in the term model at the value of a tuple of closed terms exactly when the
theory contains the corresponding atomic sentence. -/
theorem relMap_realize_iff {σ : Arity S} (R : L.Relations σ) (d : L.Term ⦃⦄ σ) :
    RelMap R (d.realize (M := h.TermModel) PUnit.unit) ↔ Formula.rel R d ∈ T := by
  rw [h.realize_closed, relMap_mkQuot, ClosedTerm.relMap_iff, ClosedTerm.terms_realize]

/-! ### The truth lemma -/

/-- Substituting closed terms for the outer variables of a formula, at the empty tuple. This is
`Term.realize_extendSubst` for the empty context, where `simp` does not see the tuple as a pair. -/
private theorem realize_subst_extendSubst {M : S → Type*} [L.Structure M] {σ τ : Arity S}
    (φ : L.Formula (σ ⨯ τ)) (c : L.Term ⦃⦄ σ) (ys : M [^] τ) :
    (φ.subst c.extendSubst).Realize ((PUnit.unit, ys) : M [^] (⦃⦄ ⨯ τ)) ↔
      φ.Realize ((c.realize PUnit.unit, ys) : M [^] (σ ⨯ τ)) := by
  rw [Formula.realize_subst]
  exact iff_of_eq (congrArg φ.Realize (Term.realize_extendSubst c (PUnit.unit : M [^] ⦃⦄) ys))

include h in
/-- A Henkin theory contains a universal sentence exactly when it contains each of its instances at
closed terms. The witness property gives the instance that fails when the sentence does. -/
theorem all_subst_mem_iff {σ τ : Arity S} (φ : L.Formula (σ ⨯ τ)) (c : L.Term ⦃⦄ σ) :
    (Formula.all τ φ).subst c ∈ T ↔ ∀ d : L.Term ⦃⦄ τ, φ.subst (c.prod d) ∈ T := by
  refine ⟨fun H d => h.mem_of_mem H fun M _ _ hM => ?_, fun H => ?_⟩
  · exact (Formula.realize_subst _ _ _).2
      (Formula.realize_all.1 ((Formula.realize_subst _ _ _).1 hM) _)
  · refine (h.mem_or_not_mem _).resolve_right fun hn => ?_
    obtain ⟨d, hd⟩ := h.exists_witness τ (φ.subst c.extendSubst).not
      (h.mem_of_mem hn fun M _ _ hM => by
        simp only [Sentence.realize_def, Formula.subst, Formula.realize_not, Formula.realize_all,
          Formula.realize_ex, not_forall] at hM ⊢
        exact hM)
    refine h.bot_notMem (h.mem_of_mem_of_mem (H d) hd fun M _ _ h₁ h₂ => ?_)
    exact (Formula.realize_not.1 ((Formula.realize_subst _ _ _).1 h₂)
      ((realize_subst_extendSubst φ c _).2 ((Formula.realize_subst _ _ _).1 h₁))).elim

/-- **The truth lemma.** A formula holds in the term model at the value of a tuple of closed terms
exactly when the theory contains the formula with those terms substituted. -/
theorem realize_iff_subst_mem : ∀ {σ : Arity S} (φ : L.Formula σ) (c : L.Term ⦃⦄ σ),
    φ.Realize (c.realize (M := h.TermModel) PUnit.unit) ↔ φ.subst c ∈ T
  | _, .falsum, _ => iff_of_false id h.bot_notMem
  | _, .equal t₁ t₂, c => by
    rw [Formula.realize_equal, ← Term.realize_subst _ t₁ c, ← Term.realize_subst _ t₂ c]
    exact h.realize_eq_iff _ _
  | _, .rel R ts, c => by
    rw [Formula.realize_rel, ← Term.realize_subst]
    exact h.relMap_realize_iff R _
  | _, .imp φ ψ, c => by
    rw [Formula.realize_imp, realize_iff_subst_mem φ c, realize_iff_subst_mem ψ c]
    exact (h.imp_mem_iff _ _).symm
  | _, .all τ φ, c => by
    rw [Formula.realize_all, h.all_subst_mem_iff]
    exact ⟨fun H d => (realize_iff_subst_mem φ (c.prod d)).1 (H _), fun H ys => by
      obtain ⟨d, rfl⟩ := h.exists_realize_eq ys
      exact (realize_iff_subst_mem φ (c.prod d)).2 (H d)⟩

/-- **A sentence holds in the term model exactly when the theory contains it.** -/
theorem realize_sentence_iff (φ : L.Sentence) : h.TermModel ⊨ φ ↔ φ ∈ T :=
  (h.realize_iff_subst_mem φ Term.nil).trans
    ⟨fun H => h.mem_of_mem H fun _ _ _ hM => (Formula.realize_subst _ _ _).1 hM,
      fun H => h.mem_of_mem H fun _ _ _ hM => (Formula.realize_subst _ _ _).2 hM⟩

/-- The term model of a Henkin theory is a model of it. -/
theorem termModel_models : h.TermModel ⊨ T :=
  ⟨fun φ hφ => (h.realize_sentence_iff φ).2 hφ⟩

/-- The sorts of the term model are nonempty: the witness property gives a closed term of each
sort. -/
theorem nonempty_termModel (s : S) : Nonempty (h.TermModel s) := by
  obtain ⟨d, -⟩ := h.exists_witness ⦃s⦄ ⊤ (h.mem_of_forall fun M _ _ =>
    Formula.realize_ex.2 ⟨Classical.arbitrary (M s), Formula.realize_top.2 trivial⟩)
  exact ⟨Quotient.mk (h.setoid s) ⟨d⟩⟩

include h in
/-- **A Henkin theory is satisfiable**, by its term model. -/
theorem isSatisfiable : T.IsSatisfiable := by
  have := h.termModel_models
  have := h.nonempty_termModel
  exact Model.isSatisfiable' h.TermModel

include h in
/-- A Henkin theory is maximal. -/
theorem isMaximal : T.IsMaximal :=
  ⟨h.isSatisfiable, h.mem_or_not_mem⟩

end Theory.IsHenkin

end ManySorted.Language
