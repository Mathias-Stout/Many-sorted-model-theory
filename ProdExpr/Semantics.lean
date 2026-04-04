import ProdExpr.SyntaxClasses

/-
Based on the corresponding Mathlib file
Mathlib\ModelTheory\Semantics.lean
which was authored by 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn,
and is released under the Apache 2.0 license.
-/

/-!
# Basics on First-Order Semantics

This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions

- `MSFirstOrder.Language.Term.realize` is defined so that `t.realize v` is the term `t` evaluated at
  variables `v`.
- `MSFirstOrder.Language.BoundedFormula.Realize` is defined so that `φ.Realize v xs` is the bounded
  formula `φ` evaluated at tuples of variables `v` and `xs`.
- `MSFirstOrder.Language.Formula.Realize` is defined so that `φ.Realize v` is the formula `φ`
  evaluated at variables `v`.
- `MSFirstOrder.Language.Sentence.Realize` is defined so that `φ.Realize M` is the sentence `φ`
  evaluated in the structure `M`. Also denoted `M ⊨ φ`.
- `MSFirstOrder.Language.Theory.Model` is defined so that `T.Model M` is true if and only if every
  sentence of `T` is realized in `M`. Also denoted `T ⊨ φ`.

## Main Results

- Several results in this file show that syntactic constructions such as `relabel`, `reindex`,
  `liftAt`, `subst`, and the actions of language maps commute with realization of terms, formulas,
  sentences, and theories.

## Implementation Notes

- Formulas use a modified version of de Bruijn variables. Specifically, a `L.BoundedFormula α σ`
  is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
  indexed by `σ : Signature Sorts`, which can. For any `φ : L.BoundedFormula α (σ ⨯ ξ)`,
  we define the formula `∀' φ : L.BoundedFormula α ξ` by universally quantifying over the
  variables indexed by `ξ`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, ⨯A formal proof of the independence of the continuum hypothesis⨯]
  [flypitch_cpp]
- [J. Han, F. van Doorn, ⨯A formalization of forcing and the unprovability of
  the continuum hypothesis⨯][flypitch_itp]
-/


universe u v w u' v' z

namespace Signature
open MSFirstOrder

--TODO: replace this by some metaprogramming
abbrev fromList {S : Type*} : (List S) → Signature S
    | [] => .nil
    | [a] => .of a
    | a :: (b :: r) => .prod (.of a) (fromList (b :: r))

instance instCoeFromList {S : Type*} : Coe (List S) (Signature S) := ⟨fromList⟩

end Signature

namespace MSFirstOrder

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
variable {M : Fam.{w} Sorts} {N : Fam Sorts} {P : Fam Sorts} [i : L.MSStructure M]
  [L.MSStructure N] [L.MSStructure P]
variable {α : Fam.{u'} Sorts} {β : Fam.{v'} Sorts} {γ : Fam Sorts}
variable {s : Sorts} {t : Sorts}
namespace MSLanguage
open MSFirstOrder Cardinal

open MSStructure MSLanguage Fin Finsupp Fam Signature
open Interpret

namespace Term

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
def realize {σ : Signature Sorts} (v : α →ₛ M) : L.Term α σ → M [^] σ
  | var t k => v t k
  | func f ts => funMap (M:= M) f (realize v ts)
  | nil => default
  | prod t₁ t₂ => ⟨realize v t₁,  realize v t₂⟩

/-
/-- Realize as a dependent map over sorts-/
def realize_as_fMap (v : α →ₛ M) : L.Term α →ₛ M :=
  fun _t => realize v
-/

@[simp]
theorem realize_var (v : α →ₛ M) (k) : realize v (var t k : L.Term α [t]) = v t k := rfl

@[simp]
theorem realize_func (v : α →ₛ M) {σ : Signature Sorts} (f : L.Functions σ t) (ts) :
    realize v (func f ts) = funMap (M:= M) f (realize v ts) := rfl

@[simp]
theorem realize_prod (v : α →ₛ M) {σ₁ σ₂ : Signature Sorts} (t₁ : L.Term α σ₁) (t₂ : L.Term α σ₂) :
    realize v (prod t₁ t₂) = ⟨ realize v t₁, realize v t₂⟩ := rfl

@[simp] lemma realize_varOf
  (v : β →ₛ M)
  (g : α →ₛ β)
  (s : Sorts) (a : α s) :
  realize v (Term.varOf (L := L) g s a)
    =
  v s (g s a) := by
  rfl

@[simp] lemma realize_bind {σ : Signature Sorts}
  (v : β →ₛ M)
  (t : L.Term α σ)
  (f : α →ₛ L.Term₁ β) :
  (t.bind f).realize v =
  t.realize (fun s a => (f s a).realize v) :=  by
  induction t <;>
  simp_all only [bind, realize_var, realize_func, realize_prod]
  rfl

/-- Realize commutes with mapVars: -/
@[simp]
lemma realize_mapVars
    {α : Fam.{u'} Sorts} {β : Fam.{v'} Sorts} {σ : Signature Sorts}
    (f : α →ₛ β) (v : β →ₛ M) (t : Term L α σ) :
    realize v (mapVars f t) =
    realize (v ∘ₛ f) t := by
  induction t <;>
  simp_all only [mapVars, bind, FamMap.mk_apply, realize_var, FamMap.comp_apply',
    realize_bind, FamMap.mk_apply, realize_var, realize_func,
                 realize_prod, realize_bind, FamMap.mk_apply, realize_var]

@[simp]
theorem realize_varterm {σ : Signature Sorts} (v : σ.IdxFam →ₛ M) :
  (varTerm σ).realize (L:= L) (M:= M) v  = fromGet v  := by
  induction σ with
  | nil => rfl
  | of s => rfl
  | prod σ₁ σ₂ ih₁ ih₂ =>
    rw [varTerm, realize_prod, realize_mapVars, realize_mapVars, ih₁, ih₂, fromGet]
    · simp_all only [Prod.mk.injEq]
      apply And.intro <;> rfl

@[simp]
theorem realize_function_term {σ} (v : σ.IdxFam →ₛ M) (f : L.Functions σ t) :
    f.term.realize v = funMap f (fromGet v) := by
  induction σ with
  | nil => rfl
  | of s => rfl
  | prod σ τ ih₁ ih₂ => simp only [Functions.term, realize_func, realize_varterm]

open Signature
open Interpret

@[simp]
theorem realize_getLeafTerm {σ : Signature Sorts}
    (t : L.Term α σ)
    (v : α →ₛ M)
    (s : Sorts)
    (w : σ.Idx s) :
    (t.realize v).get s w =
    (t.getLeafTerm s w).realize v
     := by
  induction t with
  | nil =>
      cases w
  | var s' x =>
      cases w
      rfl
  | func f ts =>
      cases w
      rfl
  | prod t₁ t₂ ih₁ ih₂ =>
      cases w with
      | left w =>
        simp_all only [getLeafTerm_prod_left, realize_prod, get_left]
      | right w =>
        simp_all only [getLeafTerm_prod_right, realize_prod, get_right]

/-- Realizing a term at a reindexed tuple is equivalent to relabelling the term
  and then realizing at the original tuple.
-/
lemma realize_comap
    {σ τ ξ : Signature Sorts}
    (g : SigMap σ τ)
    (t : L.Term (α ⊕ₛ σ.IdxFam) ξ)
    (v : α →ₛ M)
    (xs : M [^] τ) :
  t.realize (Fam.sumElim v (xs.comap g))
    =
  (t.reindex g).realize (Fam.sumElim v xs) := by
  unfold reindex
  rw[realize_mapVars (M:= M) _ _ t]
  set f1 := (Fam.sumElim v (comap g xs).get)
  set f2 := (Fam.sumElim v xs.get)
  congr!
  ext s v
  cases v <;> simp[f1, f2]

/-
@[simp]
theorem realize_liftAt {σ τ ρ: Signature Sorts} (σ'  : Signature Sorts)
    {t : L.Term (α ⊕ₛ σ.IdxFam) ξ} {v : (α ⊕ₛ (σ.prod τ).Idx ) →ₛ M} :
    (t.liftAt ξ η).realize v =
      t.realize ( fun s => (v s) ∘ Sum.map id fun i : Fin (σ s) =>
        if ↑i < (η s) then Fin.castAdd (ξ s) i else Fin.addNat i (ξ s)) :=
  realize_relabel
-/

@[simp]
theorem realize_constants {c : L.Constants t} {v : α →ₛ M} :  (c.term.realize v) = (c : M t) :=
  funMap_eq_coe_constants

/-- Renaming the left (named) variables in a term commutes with realization. -/
@[simp]
theorem realize_rename {β : Fam Sorts} {γ : Signature Sorts} {σ : Signature Sorts}
    (t : L.Term (α ⊕ₛ γ.IdxFam) σ) (g : α →ₛ β) (v : β →ₛ M) (xs : γ.Interpret M) :
    (t.rename g).realize (Fam.sumElim v xs) =
    t.realize (Fam.sumElim (v ∘ₛ g) xs) := by
  simp only [rename, mapVars, realize_bind]
  congr!
  ext s v; cases v
  · simp only [sumElim_eval_l]; rfl
  · simp_all only [sumElim_eval_r]; rfl

@[simp] lemma realize_reindex {σ τ η}
  (v : (α ⊕ₛ η.IdxFam) →ₛ M)
  (g : SigMap τ η)
  (t : L.Term (α ⊕ₛ τ.IdxFam) σ) :
  realize v (t.reindex g)
    =
  realize (Fam.sumElim (fun s a => v s (Sum.inl a))
                       (fun s x => v s (Sum.inr (g s x)))) t := by
  simp only [reindex, mapVars, realize_bind]
  congr!
  ext s v; cases v
  · simp_all only [FamMap.mk_apply, realize_var, sumElim_eval_l]; rfl
  · simp_all only [FamMap.mk_apply, realize_var, sumElim_eval_r]; rfl

theorem realize_functions_apply₁ {f : L.Functions ⦃s⦄ t} {g : L.Term α ⦃s⦄} {v : α →ₛ M} :
    (f.apply₁ g).realize v = funMap f (g.realize v) := by rw [Functions.apply₁, Term.realize]

@[simp]
theorem realize_functions_apply₂ {s s₁ s₂ : Sorts} {f : L.Functions (⦃s₁⦄ ⨯ ⦃s₂⦄) s}
    {t₁ : L.Term₁ α s₁} {t₂ : L.Term₁ α s₂} {v : α →ₛ M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ⟨t₁.realize v, t₂.realize v⟩  := by
  rw [Functions.apply₂, Term.realize]
  simp_all only [realize_prod]

theorem realize_con {A : (s : Sorts) → Set (M s)} {s : Sorts} {a : A s}
    {v : α →ₛ M} : (L.con (α := M) s a).term.realize v = (a : M s) :=
  rfl

@[simp]
theorem realize_subst {β : Fam Sorts} {σ τ : Signature Sorts}
    (t : L.Term (α ⊕ₛ σ.IdxFam) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam))
    (v : β →ₛ M)
    (xs : M [^] σ) :
    (t.subst f).realize (Fam.sumElim v xs) =
      t.realize (Fam.sumElim ⟨fun s a => (f s a).realize (Fam.sumElim v xs)⟩ xs) := by
  unfold subst
  rw[realize_bind]
  congr!
  ext s v
  cases v
  · simp_all only [sumElim_eval_l]; rfl
  · simp_all only [sumElim_eval_r]; rfl

@[simp]
theorem realize_openVars {τ η σ : Signature Sorts}
    (t : L.Term (α ⊕ₛ (η.prod τ).IdxFam) σ)
    (v : α →ₛ M)
    (ys : M [^] τ)
    (xs : M [^] η) :
    (t.openVars).realize (Fam.sumElim (Fam.sumElim v ys) xs) =
      t.realize (Fam.sumElim v (⟨xs, ys⟩ : M[^](η.prod τ))) := by
  induction t with
  | nil => rfl
  | var s x =>
      cases x with
      | inl a => simp_all only [realize_var]; rfl
      | inr w =>
          cases w with
          | left w =>  simp_all only [realize_var, sumElim_eval_r, get_left]; rfl
          | right w => simp_all only [realize_var, sumElim_eval_r, get_right]; rfl
  | func g ts ih =>
      unfold Term.openVars at *
      simp only [bind, realize_func, realize, ih]
  | prod t₁ t₂ ih₁ ih₂ =>
      unfold Term.openVars at *
      simp only [bind, realize_prod, ih₁, ih₂]


@[simp]
theorem realize_instantiate {η ρ σ : Signature Sorts}
    (t : L.Term (α ⊕ₛ (σ.prod η).IdxFam) ρ)
    (u : L.Term (α ⊕ₛ σ.IdxFam) η)
    (v : α →ₛ M)
    (xs : M [^] σ) :
    (t.instantiate u).realize (Fam.sumElim v xs) =
      t.realize (Fam.sumElim v (⟨xs, u.realize (Fam.sumElim v xs)⟩ : M[^](σ.prod η))) := by
  induction t with
  | nil => rfl
  | var s x =>
      cases x with
      | inl a => simp_all only [realize_var]; rfl
      | inr w =>
          cases w with
          | left w => simp_all only [realize_var, sumElim_eval_r, get_left]; rfl
          | right w =>
            simp_all only [realize_var, sumElim_eval_r, get_right, realize_getLeafTerm]
            rfl
  | func g ts ih =>
      rw[instantiate] at *
      simp_all only [bind, realize_func]
  | prod t₁ t₂ ih₁ ih₂ =>
      rw[instantiate] at *
      simp_all only [bind, realize_prod]

-- TODO: Update to use varType →ₛ β after resolving scoping issues
theorem realize_restrictVar
  [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
  {σ : Signature Sorts} {t : L.Term α σ}
  (f : t.varType →ₛ β)
  {v : β →ₛ M} (v' : α →ₛ M)
  (hv' :
    ∀ {s} (a : t.varType s),
      v s (f _ a) = v' s a.val) :
  (t.restrictVar (β := β) f).realize v = t.realize v' := by
  induction t with
| var =>
  simp_all only [realize_var]
  apply @hv'
| func σ g ih =>
    simp only [restrictVar, realize_func]
    congr
    let h := ih f
    apply ih
    intro s a
    apply @hv'
| prod t₁ t₂ ih₁ ih₂ =>
  simp_all only [restrictVar, realize_prod, FamMap.mk_apply, implies_true, realize]
| nil => simp_all only

/-- A special case of `realize_restrictVar`, included because we can add the `simp` attribute
to it -/
@[simp] theorem realize_restrictVar'
  [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
  {σ : Signature Sorts} {t : L.Term α σ}
  {S : DepSet α}
  (h : ∀ {s} {x : α s}, ⟨s, x⟩ ∈ Term.varFinset t → x ∈ S s)
  {v : α →ₛ M} :
  (t.restrictVar (β := S)
    ⟨fun {_} a => (⟨a.1, h a.2⟩ : S _)⟩
    ).realize
      (v ∘ₛ S.subtypeVal)
  =
  t.realize v := by
    apply realize_restrictVar
    intro s a
    simp_all only [FamMap.mk_apply, FamMap.comp_apply']

theorem realize_restrictVarLeft
  [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
  {σ : Signature Sorts} {γ : Fam Sorts}
  {t : L.Term (α ⊕ₛ γ) σ}
  (f : t.varTypeLeft →ₛ β)
  {xs : (β ⊕ₛ γ) →ₛ M}
  (xs' : α →ₛ M)
  (hxs' :
    ∀ {s} (a : t.varTypeLeft s),
      xs s (Sum.inl (f s a)) = xs' s a.val) :
  (t.restrictVarLeft (β := β) (γ := γ) f).realize xs
    =
  t.realize (Fam.sumElim xs' ⟨fun s g => xs s (Sum.inr g)⟩) := by
  induction t with
  | var s a =>
      simp_all only [varFamLeft.eq_1, realize_var]
      cases a
      · simp_all only [varFinsetLeft.eq_1, sumElim_eval_l]
        apply @hxs'
      · simp_all only [varFinsetLeft.eq_2, sumElim_eval_r, FamMap.mk_apply]
        rfl
  | func σ g ih =>
      rw [restrictVarLeft, realize_func]
      congr
      apply ih f
      intro s a
      simp_all only [varFamLeft.eq_1, varFinsetLeft.eq_3]
      apply @hxs'
  | prod t₁ t₂ ih₁ ih₂ =>
      simp_all only [restrictVarLeft, realize_prod, FamMap.mk_apply, implies_true, realize]
  | nil => simp_all only



/-- A special case of `realize_restrictVarLeft`, included because we can add the `simp` attribute
to it -/
-- TODO: Fix this theorem after restrictVarLeft changes
-- @[simp] theorem realize_restrictVarLeft'
--   [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
--   {σ : Signature Sorts} {γ : Fam Sorts}
--   {t : L.Term (α ⊕ₛ γ) σ}
--   {S : DepSet α}
--   (h : ∀ {s} {x : α s}, ⟨s, x⟩ ∈ Term.varFinsetLeft t → x ∈ S s)
--   {v : α →ₛ M} {xs : γ →ₛ M} :
--   (t.restrictVarLeft (γ := γ) (fun s a => ⟨a.val, h a.property⟩)).realize
--       (Fam.sumElim (fun s x => v s x.val) xs)
--     =
--   t.realize (Fam.sumElim v xs) := by
--   simp only [Sum.elim_inl, Subtype.forall, realize_restrictVarLeft, Sum.elim_inr]
@[simp]
theorem realize_constantsToVars
  [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
  {σ : Signature Sorts} {t : L[[α]].Term β σ} {v : β →ₛ M} :
  t.constantsToVars.realize
      (Fam.sumElim ⟨fun s a => (L.con (s := s) a : M s)⟩ v)
    =
  t.realize v := by
  induction t with
  | nil => simp only [constantsToVars]
  | var => simp only [constantsToVars, realize_var, Fam.sumElim]; rfl
  | @func σ s f t ih  =>
    cases f
    case inl w =>
      simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
      exact (withConstants_funMap_sumInl (f := w) (M := M)).symm
    case inr v =>
      cases σ
      case nil =>
        simp_all only [reduce_nil, PUnit.default_eq_unit, constantsToVars, realize_var,
          constantsOn_Functions, constantsOnFunc, realize_func]
        rfl
      case of =>
        cases v
      case prod =>
        simp_all only [constantsToVars, constantsOn_Functions, constantsOnFunc, realize_func]
        cases v
  | @prod σ τ tσ tτ ihσ ihτ =>
    simp_all only [constantsToVars, realize_prod]

@[simp]
theorem realize_varsToConstants
  [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
  {σ : Signature Sorts} {t : L.Term (α ⊕ₛ β) σ} {v : β →ₛ M} :
  (t.varsToConstants).realize v
    =
  t.realize (Fam.sumElim ⟨fun s a => (L.con (s := s) a : M s)⟩ v) := by
  induction t with
  | nil =>
      simp only [varsToConstants, realize, PUnit.default_eq_unit]
  | prod t₁ t₂ ih₁ ih₂ =>
      simp only [varsToConstants, realize_prod, ih₁, ih₂, realize]
  | var s ab =>
      -- ab : (α ⊕ₛ β) s  i.e. Sum (α s) (β s)
      cases ab with
      | inl a =>
          simp only [varsToConstants, constantsOn_Functions, constantsOnFunc.eq_1,
            realize_constants, realize, Fam.sumElim]
          rfl
      | inr b =>
          simp only [varsToConstants, realize_var, realize, Fam.sumElim]; rfl
  | @func σ' s f ts ih =>
      simp only [Term.realize, Term.varsToConstants, ih]
      rw [withConstants_funMap_sumInl]

theorem realize_constantsVarsEquivLeft
  [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
  {σ τ : Signature Sorts}
  {t : L[[α]].Term (β ⊕ₛ σ.IdxFam) τ} {v : β →ₛ M} {xs : M [^] σ} :
  (constantsVarsEquivLeft t).realize
      (Fam.sumElim
        (Fam.sumElim ⟨fun s a => (L.con (s := s) a : M s)⟩ v)
        (xs.get))
    =
  t.realize (Fam.sumElim v (xs.get)) := by
  simp only [constantsVarsEquivLeft, Equiv.trans_apply, constantsVarsEquiv_apply,
    mapVarsEquiv_symm_apply, mapVars, realize_bind]
  refine _root_.trans ?_ (realize_constantsToVars (t := t) (v := (Fam.sumElim v (xs.get))))
  congr! 1
  ext s x
  -- x : ((α ⊕ₛ β) ⊕ₛ σ.IdxFam) s, so split into the three cases
  cases x with
  | inl ab =>
      simp_all only [FamMap.mk_apply, realize_var, sumElim_eval_l]
      rfl
  | inr w =>
      cases w
      · simp_all only [FamMap.mk_apply, realize_var, sumElim_eval_r, sumElim_eval_l]
        rfl
      · simp_all only [FamMap.mk_apply, realize_var, sumElim_eval_r]
        rfl

end Term

namespace LHom


@[simp]
theorem realize_onTerm {σ : Signature Sorts} [L'.MSStructure M] (φ : L →ᴸ L')
  [φ.IsExpansionOn M] (t : L.Term α σ) (v : α →ₛ M) :
  (φ.onTerm t).realize v = t.realize v := by
  induction t with
  | nil => rfl
  | var => rfl
  | func _ _ ih => simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]
  | prod _ _ ih₁ ih₂ => simp only [onTerm, Term.realize_prod, ih₁, ih₂]

end LHom
variable {σ : Signature Sorts}


@[simp]
theorem HomClass.realize_term {F : Type*} [HomClass L F M N]
    (g : F) {t : L.Term α σ} {v : α →ₛ M} :
    t.realize (g ∘ₛ v) = g <$>ₛ (t.realize v) := by
  induction t with
  | nil => rfl
  | var => rfl
  | func _ _ ih =>
    simp only [Term.realize, ih]
    exact (HomClass.map_fun g _ _).symm
  | prod _ _ ih₁ ih₂ =>
    simp only [Term.realize_prod, ih₁, ih₂]
    simp_all only [Interpret.map_prod]

namespace BoundedFormula

open Term Interpret
/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def Realize : ∀ {ξ} (_φ : L.BoundedFormula α ξ) (_v : α →ₛ M) (_xs : ξ.Interpret M), Prop
  | _, falsum, _v, _xs => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Fam.sumElim v xs)
      = t₂.realize (Fam.sumElim v xs)
  | _, rel R ts, v, xs => RelMap R (ts.realize (Fam.sumElim v xs))
  | _, imp φ₁ φ₂, v, xs => Realize φ₁ v xs → Realize φ₂ v xs
  | _, all σ φ, v, xs => ∀ x : M [^] σ, Realize φ v ⟨xs, x⟩

variable {ξ η : Signature Sorts} {φ ψ : L.BoundedFormula α ξ} {θ : L.BoundedFormula α (ξ.prod η)}
variable {v w : α →ₛ M} {xs : ξ.Interpret M}

lemma realize_eq_val (hv : φ.Realize v xs) (heq : v = w) : φ.Realize w xs := by
   simp_all only

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormula α ξ).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_not : φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_bdEqual (t₁ t₂ : L.Term (α ⊕ₛ ξ.IdxFam) σ) :
    (t₁.bdEqual t₂).Realize v xs ↔ t₁.realize (Fam.sumElim v xs) = t₂.realize (Fam.sumElim v xs) :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormula α ξ).Realize v xs ↔ True := by simp only [Top.top,
  realize_not, realize_bot, not_false_eq_true]

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp only [Realize, imp_false, Classical.not_imp, not_not]

@[simp]
theorem realize_foldr_inf {σ} (l : List (L.BoundedFormula α σ)) (v : α →ₛ M) (xs : M [^] σ) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ ∀ φ ∈ l, φ.Realize v xs := by
  induction l with
  | nil => simp only [List.foldr_nil, realize_top, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true]
  | cons φ l ih => simp only [List.foldr_cons, realize_inf, ih, List.mem_cons, forall_eq_or_imp]

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs := by
  simp only [Realize]

/-- List.foldr on BoundedFormula.imp gives a big "And" of input conditions. -/
theorem realize_foldr_imp {η : Signature Sorts} (l : List (L.BoundedFormula α η))
    (f : L.BoundedFormula α η) :
    ∀ (v : α →ₛ M) xs,
      (l.foldr BoundedFormula.imp f).Realize v xs =
      ((∀ i ∈ l, i.Realize v xs) → f.Realize v xs) := by
  intro v xs
  induction l
  next => simp only [List.foldr_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    forall_const]
  next f' _ _ =>
  by_cases f'.Realize v xs <;> simp_all only [eq_iff_iff, List.foldr_cons, realize_imp,
    not_isEmpty_of_nonempty, IsEmpty.forall_iff,true_and, forall_const, List.mem_cons,
    forall_eq_or_imp, false_and]

@[simp]
theorem realize_rel {R : L.Relations η} {ts : L.Term _ η} :
    (R.boundedFormula ts).Realize v xs ↔ RelMap R (ts.realize (Fam.sumElim v xs)) :=
  Iff.rfl

@[simp]
theorem realize_rel₁ {s : Sorts} {R : L.Relations ⦃s⦄} {t : L.Term _ ⦃s⦄} :
    (R.boundedFormula₁ t).Realize v xs ↔ RelMap R (t.realize (Fam.sumElim v xs)) := by
  rw [Relations.boundedFormula₁, realize_rel, iff_eq_eq]

@[simp]
theorem realize_rel₂ {s₁ s₂ : Sorts} {R : L.Relations (⦃s₁⦄ ⨯ ⦃s₂⦄)}
    {t₁ : L.Term _ ⦃s₁⦄} {t₂ : L.Term _ ⦃s₂⦄} :
    (R.boundedFormula₂ t₁ t₂).Realize v xs ↔
    RelMap R ((t₁.prod t₂).realize (Fam.sumElim v xs)) := by
  rw [Relations.boundedFormula₂, realize_rel, iff_eq_eq]


@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [max]
  tauto

@[simp]
theorem realize_foldr_sup (l : List (L.BoundedFormula α σ)) (v : α →ₛ M) (xs : M [^] σ) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp only [List.foldr_nil, realize_bot, List.not_mem_nil, false_and, exists_const]
  | cons φ l ih =>
    simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
      exists_eq_left]

@[simp]
theorem realize_all : (all η θ).Realize v xs ↔ ∀ a : M[^]η , θ.Realize v ⟨xs, a⟩ :=
  Iff.rfl

@[simp]
theorem realize_ex : (θ.ex η).Realize v xs ↔ ∃ a : M[^]η, θ.Realize v ⟨xs, a⟩  := by
  rw [BoundedFormula.ex, realize_not, realize_all, not_forall]
  simp only [realize_not, Classical.not_not]

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormula.iff, realize_inf, realize_imp, ← iff_def]

@[simp]
theorem realize_rename {β : Fam Sorts} {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (f : α →ₛ β)
    (v : β →ₛ M)
    (xs : M [^] σ) :
    (φ.rename f).Realize v xs ↔ φ.Realize (v ∘ₛ f) xs := by
  induction φ with
  | falsum =>
      simp only [rename, mapTermRel]
      rfl
  | equal t₁ t₂ =>
    simp only [rename, mapTermRel, Realize, Term.realize_rename]
  | rel R ts =>
      simp only [rename, mapTermRel, Realize, Term.realize_rename]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [rename, mapTermRel, realize_imp, Realize] at *
      simp only [ih₁ xs, ih₂ xs]
  | all η φ ih =>
      simp only [rename, mapTermRel, realize_all] at *
      simp only [ih]

open Signature SigEquiv Interpret

/-- Realization commutes with substitution of free variables by terms. -/
@[simp]
theorem realize_subst {β : Fam Sorts} {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam))
    (v : β →ₛ M)
    (xs : M [^] σ) :
    (φ.subst f).Realize v xs ↔
      φ.Realize ⟨fun s a => (f s a).realize (Fam.sumElim v xs)⟩ xs := by
  induction φ with
  | falsum => simp only [subst, Realize]
  | equal t₁ t₂ =>
      simp  [BoundedFormula.subst, Realize, Term.realize_subst]
  | rel R ts =>
      simp only [BoundedFormula.subst, Realize, Term.realize_subst]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [BoundedFormula.subst, realize_imp]
      rw [ih₁, ih₂]
  | @all σ' τ φ ih =>
      simp only [BoundedFormula.subst, realize_all]
      /- f' s a = (f s a).reindex incl_left has type Term (β ⊕ₛ (σ'.prod τ).IdxFam) ⦃s⦄
      -- ih : (φ.subst f').Realize v xs' ↔
      -- φ.Realize (fun s a => (f' s a).realize (sumElim v xs')) xs'
      -- for xs' : (σ'.prod τ).Interpret M
      -- We need: reindexed term at (xs, x) equals original term at xs -/
      have hval : ∀ (x : M [^] τ),
        (fun s a => ((f s a).reindex SigMap.incl_left).realize
            (Fam.sumElim v (Interpret.get (⟨xs , x⟩ : (σ'.prod τ).Interpret M) ))) =
          (fun s a => (f s a).realize (Fam.sumElim v xs)) := by
        intro x
        funext s a
        simp only [Term.reindex, Term.realize_mapVars]
        congr 1
        ext s' b
        cases b with
        | inl b' =>
            simp_all only [Prod.forall, FamMap.comp_apply', sumMap_inl_apply,
            FamMap.idₛ_apply', sumElim_eval_l]
        | inr w =>
            simp only [Fam.sumElim, Interpret.get]
            rfl
      refine forall_congr' (fun x => ?_)
      simp_all only [Prod.forall, realize_reindex, sumElim_eval_l, SigMap.incl_left_apply,
        sumElim_eval_r, get_left, FamMap.mk_apply]
      rfl

@[simp]
lemma comap_extend_right {x : M [^] η}
    (g : SigMap σ ξ) : Interpret.comap g.extend_right (xs, x) = (xs.comap g, x) := by
    have hget :
      Interpret.get (Interpret.comap  g.extend_right (xs, x))
        = ⟨fun s v =>
            match v with
            | Idx.left  wσ => xs.get s (g s wσ)
            | Idx.right wη => x.get s wη ⟩:= by
          ext s v
          cases v with
          | left wσ =>
            rw[get_comap]; unfold SigMap.extend_right;
            simp_all only [FamMap.mk_apply]
            rfl
          | right wη =>
            rw[get_comap]; unfold SigMap.extend_right;
            simp_all only [FamMap.mk_apply]
            rfl
    have hget_rhs :
      Interpret.get (xs.comap g, x)
        = ⟨fun s (v : (σ.prod η).Idx s) =>
            match v with
            | .left w => xs.get s (g s w)
            | .right w => x.get s w⟩ := by
      ext s v
      cases v with
      | left wσ =>
          simp only [Interpret.get, comap, fromGet_get, FamMap.mk_apply]
      | right wη =>
          simp only [Interpret.get, get_comap, FamMap.mk_apply]
    have h :
    Interpret.get (Interpret.comap g.extend_right (xs, x))
      = Interpret.get (xs.comap g, x) := by
        ext s v; rw[hget, hget_rhs];
        simp_all only [SigMap.extend_right, get_comap, FamMap.mk_apply]
        rfl
    have h':= congrArg (Interpret.fromGet (S := Sorts) (α := M) (σ := σ.prod η)) h
    rw[get_fromGet] at h'
    simp only [h', get_fromGet]

instance {σ τ : Signature Sorts} : CoeTC (M [^] σ × M [^] τ) (M [^] (σ ⨯ τ)) where
  coe := fun x => x

@[simp]
lemma comap_block_swap
    {σ τ η : Signature Sorts}
    (xs : M [^] σ) (ys : M [^] τ) (zs : M [^] η) :
    Interpret.comap (X:= M)
        (@block_swap _ σ τ η : SigMap ((σ ⨯ τ) ⨯ η) ((σ ⨯ η) ⨯ τ) )
        (⟨⟨xs, zs⟩, ys⟩ : ((σ ⨯ η) ⨯ τ).Interpret M)
      = (⟨⟨xs, ys⟩, zs⟩ : ((σ ⨯ τ) ⨯ η).Interpret M) := by
  -- Prove by extensionality on `Interpret.get` and then rebuild with `fromGet`.
  have hget :
      Interpret.get
          (Interpret.comap (@block_swap _ σ τ η : SigMap ((σ ⨯ τ) ⨯ η) ((σ ⨯ η) ⨯ τ) )
            (⟨⟨xs, zs⟩, ys⟩ : ((σ ⨯ η) ⨯ τ).Interpret M))
        =
      Interpret.get (⟨⟨xs, ys⟩, zs⟩ : ((σ.prod τ).prod η).Interpret M) := by
    ext s v
    -- `get_comap` reduces this to computing `block_swap` on variables.
    rw [get_comap]
    -- Now unfold `block_swap` and split by the variable position.
    unfold block_swap
    cases v with
    | left vστ =>
        cases vστ with
        | left wσ =>
            simp only [Interpret.get, SigEquiv.trans, SigEquiv.Id]
            rfl
        | right wτ =>
            simp only [Interpret.get, SigEquiv.trans, SigEquiv.Id]
            rfl
    | right wη =>
        simp only [Interpret.get, SigEquiv.trans, SigEquiv.Id]; rfl
  have h' :=
      congrArg (Interpret.fromGet (S := Sorts) (α := M) (σ := (σ.prod τ).prod η)) hget
  -- `fromGet` is inverse to `get`.
  rw [get_fromGet] at h'
  simpa only [get_fromGet] using h'

@[simp]
lemma realize_reindex
    {σ τ : Signature Sorts}
    (g : Signature.SigMap σ τ)
    (φ : L.BoundedFormula α σ)
    (v : α →ₛ M)
    (xs : Signature.Interpret M τ) :
  (φ.reindex g).Realize v xs
    ↔
  φ.Realize v (Signature.Interpret.comap g xs) := by
  revert τ g xs
  induction φ with
  | falsum =>
      intro τ g xs
      simp only [reindex, Realize]
  | equal t₁ t₂ =>
      intro τ g xs
      -- Term.realize_comap is your commuting lemma
      rw[reindex, Realize, Realize, ←Term.realize_comap, ←Term.realize_comap]
  | rel R ts =>
      intro τ g xs
      rw[reindex, Realize, Realize, ←Term.realize_comap]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      intro τ g xs
      simp only [reindex, realize_imp, ih₁, ih₂, Realize]
  | all η ψ ih =>
      intro τ g xs
      -- After simp, goal becomes a ∀x statement. IH applies to ψ with g.extend_right.
      -- comap_extend_right rewrites comap along extend_right on (xs, x).
      simp only [reindex, realize_all, ih, comap_extend_right (g := g) (xs := xs), Realize]

/-- Realization commutes with `relabel`: relabeling free variables `α` to `β ⊕ τ.Idx`
and then evaluating is equivalent to evaluating with the relabeled variable assignment. -/
@[simp]
theorem realize_relabel {β : Fam Sorts} {τ σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (g : α →ₛ β ⊕ₛ τ.IdxFam)
    (v : β →ₛ M)
    (ys : M [^] τ)
    (xs : M [^] σ) :
    (φ.relabel g).Realize v (⟨ys, xs⟩ : (τ.prod σ).Interpret M) ↔
      φ.Realize (fun s a => Fam.sumElim v ys s (g s a)) xs := by
  rw [relabel]
  simp only [realize_subst, realize_rename, realize_reindex]
  congrm φ.Realize ?_ ?_
  · ext s x
    simp only [FamMap.comp_apply', FamMap.mk_apply, coeFun_apply]
    set zs : (β ⊕ₛ τ.IdxFam) s := g s x
    change _ = (Fam.sumElim v ys.get) s zs
    change
      realize (Fam.sumElim v (Interpret.get (ys, xs)))
          ((Fam.sumElim (varOf inl) { toFun := fun s v ↦ var s (Sum.inr (Idx.left v)) }) s zs)
          = _
    cases zs
    · simp_all only [sumElim_eval_l, realize_varOf]
      rfl
    · simp_all only [sumElim_eval_r, FamMap.mk_apply, realize_var, get_left]
  · ext s v_1 : 1
    simp_all only [get_comap, SigMap.incl_right_apply, get_right]
    rfl

theorem realize_openVars_aux
    (n : ℕ)
    {α : Fam.{u'} Sorts}
    {σ τ : Signature Sorts}
    (φ : L.BoundedFormula α (σ.prod τ))
    (hn : φ.size ≤ n)
    (v : α →ₛ M)
    (ys : M [^] τ)
    (xs : M [^] σ) :
    φ.openVars.Realize (Fam.sumElim v ys) xs ↔
      φ.Realize v (⟨xs, ys⟩ : (σ.prod τ).Interpret M) := by
  induction n generalizing α σ τ φ v ys xs with
  | zero =>
      -- size is always ≥ 1, so this case is vacuous
      cases φ <;> simp only [size, nonpos_iff_eq_zero, Nat.add_eq_zero_iff, one_ne_zero,
        false_and] at hn
  | succ n ih =>
      cases φ with
      | falsum => simp only [openVars, Realize]
      | equal t₁ t₂ =>
          simp only [openVars, Realize, realize_openVars]
      | rel R ts =>
          simp only [openVars, Realize, realize_openVars]
      | imp φ₁ φ₂ =>
          simp only [BoundedFormula.openVars, realize_imp, Realize]
          have h₁ := ih φ₁ (by simp only [size] at hn ⊢; omega) v ys xs
          have h₂ := ih φ₂ (by simp only [size] at hn ⊢; omega) v ys xs
          simp only [h₁, h₂]
      | all η ψ =>
          -- ψ : BoundedFormula α ((σ.prod τ).prod η)
          -- Reindex by block_swap so that τ is the right block, then openVars, then quantify η.
          simp only [BoundedFormula.openVars, realize_all, Realize]
          refine forall_congr' (fun x => ?_)
          -- x : M[^]η
          have hsize : (ψ.reindex (@block_swap _ σ τ η :
              SigMap ((σ ⨯ τ) ⨯ η) ((σ ⨯ η) ⨯ τ) )).size ≤ n := by
            rw [reindex_size]; simp only [size] at hn ⊢; omega
          have hrec := ih (ψ.reindex (@block_swap _ σ τ η :
              SigMap ((σ ⨯ τ) ⨯ η) ((σ ⨯ η) ⨯ τ) )) hsize v ys (xs, x)
          calc
            (((ψ.reindex (@block_swap _ σ τ η :
                SigMap ((σ ⨯ τ) ⨯ η) ((σ ⨯ η) ⨯ τ) )).openVars).Realize (Fam.sumElim v ys)
                (⟨xs, x⟩ : M[^](σ.prod η)))
                ↔ ((ψ.reindex (@block_swap _ σ τ η : SigMap ((σ ⨯ τ) ⨯ η) ((σ ⨯ η) ⨯ τ) )).Realize v
                    (⟨⟨xs, x⟩, ys⟩ : M[^]((σ ⨯ η) ⨯ τ))) := hrec
            _ ↔ ψ.Realize v
                  (Interpret.comap (@block_swap _ σ τ η : SigMap ((σ ⨯ τ) ⨯ η) ((σ ⨯ η) ⨯ τ) )
                    (⟨⟨xs, x⟩, ys⟩ : M[^]((σ ⨯ η) ⨯ τ))) := by
                  simp only [realize_reindex]
            _ ↔ ψ.Realize v (⟨⟨xs, ys⟩, x⟩ : ((σ.prod τ).prod η).Interpret M) := by
                  rw [comap_block_swap xs ys x]

@[simp]
theorem realize_openVars {σ τ : Signature Sorts}
    (φ : L.BoundedFormula α (σ.prod τ))
    (v : α →ₛ M)
    (ys : M [^] τ)
    (xs : M [^] σ) :
    φ.openVars.Realize (Fam.sumElim v ys) xs ↔
      φ.Realize v (⟨xs, ys⟩ : (σ.prod τ).Interpret M) :=
  realize_openVars_aux φ.size φ (le_refl _) v ys xs


/-- Realization commutes with `closeVars`: closing free variables `X` via `f : X →ₛ τ.Idx`
and evaluating at `(xs, ys)` is equivalent to substituting `ys` for the `X` variables. -/
@[simp]
theorem realize_closeVars {σ τ : Signature Sorts} {X : Fam Sorts}
    (f : X →ₛ τ.IdxFam)
    (φ : L.BoundedFormula (α ⊕ₛ X) σ)
    (v : α →ₛ M)
    (xs : M [^] σ)
    (ys : M [^] τ) :
    (φ.closeVars f).Realize v (⟨xs, ys⟩ : (σ.prod τ).Interpret M) ↔
      φ.Realize (Fam.sumElim v (fun s x => ys.get s (f s x))) xs := by
  rw[closeVars]
  rw[relabel]
  simp only [reindex_subst, reindex_rename, reindex_reindex, realize_subst, realize_rename,
    sumComp_elim, realize_reindex]
  congr!
  ext s x
  simp_all only [get_comap]
  rfl

/-- Realization commutes with `instantiate`: instantiating a term `t` for the rightmost
bound variables and then realizing is equivalent to realizing with `t.realize` substituted. -/
@[simp]
theorem realize_instantiate {σ τ : Signature Sorts}
    (φ : L.BoundedFormula α (σ.prod τ))
    (t : L.Term (α ⊕ₛ σ.IdxFam) τ)
    (v : α →ₛ M)
    (xs : M [^] σ) :
    (φ.instantiate t).Realize v xs ↔
      φ.Realize v (⟨xs, t.realize (Fam.sumElim v xs)⟩ : (σ.prod τ).Interpret M) := by
  let ys : M [^] τ := t.realize (Fam.sumElim v xs)
  let f : (α ⊕ₛ τ.IdxFam) →ₛ M := ⟨fun s a ↦
      realize (Fam.sumElim v (xs.get))
              (Fam.sumElim (varOf inl)
              ⟨fun s a ↦ t.getLeafTerm s a⟩ s a)⟩
  have hv :
    f
    =
    Fam.sumElim v ys := by
    ext s a
    cases a with
    | inl a =>
        simp_all only [sumElim_eval_l, f, ys]
        rfl
    | inr w =>
        simp_all only [sumElim_eval_r, FamMap.mk_apply, realize_getLeafTerm, f, ys]
  rw[instantiate]
  rw[realize_subst]
  change φ.openVars.Realize f xs ↔
  φ.Realize v (xs, realize (Fam.sumElim v (xs.get)) t)
  rw[hv]
  simp only [realize_openVars, ys]

open Lean.Parser.Tactic
syntax "elab_prod" (ppSpace location)? : tactic

macro_rules
  | `(tactic| elab_prod $[$loc]?) => `(tactic| simp only [Interpret] $[$loc]?)


/-



sorry

theorem realize_comap_of_eq {ξ σ : Signature Sorts} (h : ξ = σ) {h' : ξ ≤ σ}
    {φ : L.BoundedFormula α ξ}
    --note: annoying bit of coercion happens here to go from ξ = σ to ∀ s, ξ s = σ s
    {v : α →ₛ M} {xs : M [^] σ} :

    (φ.reindex h').Realize v xs
     ↔
    φ.Realize v (fun s => (xs s) ∘ Fin.cast (congr_fun (congr_arg DFunLike.coe h) s)) := by

  subst h
  simp only [reindex_rfl, cast_refl, Function.comp_id]

-/

theorem realize_mapTermRel_id [L'.MSStructure M] {φ : L.BoundedFormula α σ}
    (ft : ∀ σ ξ : Signature Sorts, L.Term (α ⊕ₛ σ.IdxFam) ξ →  L'.Term (β ⊕ₛ σ.IdxFam) ξ)
    (fr : ∀ σ, L.Relations σ → L'.Relations σ)
    {v' : β →ₛ M} {xs : M [^] σ}
    (h1 :
      ∀ (σ: Signature Sorts) (τ) (t : L.Term (α ⊕ₛ σ.IdxFam) τ) (xs : M [^] σ),
        (ft σ τ t).realize (Fam.sumElim v' xs) =
        t.realize (Fam.sumElim v xs))
    (h2 : ∀ (σ) (R : L.Relations σ) (x : M [^] σ), RelMap (fr σ R) x = RelMap R x) :
    (φ.mapTermRel ft fr fun _ _ => id).Realize v' xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | @equal σ τ t₁ _ =>
      let h := h1 σ τ t₁ xs
      simp_all only [mapTermRel, Realize, eq_iff_iff]
  | rel =>
    simp only [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, realize_imp, ih1, ih2, Realize]
  | all _ _ ih => simp only [mapTermRel, id_eq, realize_all, ih, Realize]

/-! ### Realization of restrictFreeVar -/

/-- Realization commutes with restricting free variables: if `f` maps the free variable type of `φ`
to `β`, then realizing `φ.restrictFreeVar f` at `v : β →ₛ M` is equivalent to realizing `φ` at
`v'` provided `v` and `v'` agree on the image of free variables under `f`. -/
theorem realize_restrictFreeVar [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (f : φ.freeVarType →ₛ β)
    (v : β →ₛ M)
    (v' : α →ₛ M)
    (hv : ∀ s (a : α s), (h : ⟨s, a⟩ ∈ freeVarFinset φ) → v s (f s ⟨a, h⟩) = v' s a)
    (xs : M [^] σ) :
    (φ.restrictFreeVar f).Realize v xs ↔ φ.Realize v' xs := by
  induction φ generalizing β with
  | falsum => simp only [restrictFreeVar, Realize]
  | @equal σ τ t₁ t₂ =>
    simp only [restrictFreeVar, Realize]
    -- For terms, we use realize_restrictVarLeft
    -- Need to show both sides equal
    have h1 : (t₁.restrictVarLeft ⟨fun {t} x =>
        f t ⟨x.1, Finset.mem_union.mpr (Or.inl x.2)⟩⟩).realize (Fam.sumElim v xs) =
        t₁.realize (Fam.sumElim v' xs) := by
      rw [realize_restrictVarLeft]
      · congr 1
      · intro s ⟨a, ha⟩
        simp_all only [freeVarFinset, Finset.mem_union, varFamLeft.eq_1, FamMap.mk_apply,
          sumElim_eval_l]
        apply hv
        simp_all only [varFamLeft]
        apply Or.inl
        exact ha
    have h2 : (t₂.restrictVarLeft ⟨fun {t} x =>
        f t ⟨x.1, Finset.mem_union.mpr (Or.inr x.2)⟩⟩).realize
        (Fam.sumElim v xs) =
        t₂.realize (Fam.sumElim v' xs) := by
      rw [realize_restrictVarLeft]
      · congr 1
      · intro s ⟨a, ha⟩
        simp_all only [freeVarFinset, Finset.mem_union, varFamLeft, FamMap.mk_apply, sumElim_eval_l]
        apply hv
        simp_all only [varFamLeft]
        apply Or.inr
        exact ha
    rw [h1, h2]
  | @rel σ τ R ts =>
    simp only [restrictFreeVar, Realize]
    congr!
    apply Interpret.ext
    intro s i
    rw [realize_restrictVarLeft]
    · simp_all only [freeVarFinset, freeVarFinset.eq_3]
      rfl
    · intro s_1 a
      simp_all only [freeVarFinset, FamMap.mk_apply, sumElim_eval_l, varFamLeft]
      apply hv
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [restrictFreeVar, realize_imp]
    let f₁ : φ₁.freeVarType →ₛ β := ⟨fun t x => f t ⟨x.1, Finset.mem_union.mpr (Or.inl x.2)⟩⟩
    let f₂ : φ₂.freeVarType →ₛ β := ⟨fun t x => f t ⟨x.1, Finset.mem_union.mpr (Or.inr x.2)⟩⟩
    have hv₁ : ∀ s (a : α s), (h : ⟨s, a⟩ ∈ freeVarFinset φ₁) → v s (f₁ s ⟨a, h⟩) = v' s a := by
      intro s a h
      simp only [f₁]
      exact hv s a (Finset.mem_union.mpr (Or.inl h))
    have hv₂ : ∀ s (a : α s), (h : ⟨s, a⟩ ∈ freeVarFinset φ₂) → v s (f₂ s ⟨a, h⟩) = v' s a := by
      intro s a h
      simp only [f₂]
      exact hv s a (Finset.mem_union.mpr (Or.inr h))
    rw [ih₁ f₁ v hv₁ xs, ih₂ f₂ v hv₂ xs]
  | @all σ τ φ ih =>
    simp only [restrictFreeVar, realize_all]
    apply forall_congr'
    intro x
    -- The free variables of (all τ φ) are the same as the free variables of φ
    -- So the restriction function is the same
    exact ih f v hv ⟨xs, x⟩

/-- A variant of `realize_restrictFreeVar` where we fix the valuation to be `v ∘ₛ f` composed
with the subtype coercion. This is useful when you want to restrict and then unrestrict. -/
theorem realize_restrictFreeVar' [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (v : α →ₛ M)
    (xs : M [^] σ) :
    (φ.restrictFreeVar ⟨fun _ x => x.1⟩).Realize v xs ↔ φ.Realize v xs := by
  apply realize_restrictFreeVar
  intro s a _
  rfl

end BoundedFormula


/-
--todo: when required
open Signature SigMap
theorem realize_mapTermRel_add_reindex
  [L'.MSStructure M] {σ τ ξ : Signature Sorts}

  {ft : ∀ (τ ξ : Signature Sorts),
      L.Term (α ⊕ₛ τ.IdxFam) ξ →
        L'.Term (β ⊕ₛ (σ.prod τ).IdxFam) ξ}

  {fr : ∀ τ : Signature Sorts, L.Relations τ → L'.Relations τ}
  {φ : L.BoundedFormula α τ}

  (v : ∀ {τ}, (σ.prod τ).Interpret M → α →ₛ M)
  {v' : β →ₛ M}

  (xs : (σ.prod τ).Interpret M)

  (h1 :
    ∀ (τ ξ) (t : L.Term (α ⊕ₛ τ.IdxFam) ξ) (xs' : (σ.prod τ).Interpret M),
      (ft τ ξ t).realize (Fam.sumElim v' (xs.get')) =
        t.realize (Fam.sumElim (v xs') (xs.get' ∘ₛ incl_right)))

  (h2 :
    ∀ (τ) (R : L.Relations τ) (x : M [^] τ),
      RelMap (fr τ R) x = RelMap R x)

  (hv :
    ∀ (τ η) (xs : (σ.prod τ).Interpret M) (x : M[^]η),
      @v (τ.prod η)
        (interpretEquiv M (PEquiv.assocL σ _ _ ) ((xs, x) :
        ((σ.prod τ).prod η).Interpret M)) = v xs) :

  (φ.mapTermRel ft fr (fun τ₀ η => reindex (L := L') (α := β) (SigMap.assocR σ τ₀ η))).Realize v' xs
    ↔
    φ.Realize (v xs) (fromGet (xs.get ∘ₛ incl_right (σ := τ))) := by
  induction φ with
  | falsum =>
      rfl
  | equal t₁ t₂ =>
      simp?[mapTermRel, Realize, h1]
  | rel =>
      simp?[mapTermRel, Realize, h1, h2]
  | imp _ _ ih₁ ih₂ =>
      simp?[mapTermRel, Realize, ih₁, ih₂]
  | all η f ih =>

      sorry

-/




namespace LHom

open BoundedFormula

@[simp]
theorem realize_onBoundedFormula [L'.MSStructure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    {σ : Signature Sorts} (ψ : L.BoundedFormula α σ) {v : α →ₛ M} {xs : M [^] σ} :
    (φ.onBoundedFormula ψ).Realize v xs ↔ ψ.Realize v xs := by
  induction ψ with
  | falsum => rfl
  | equal => simp only [onBoundedFormula, realize_bdEqual, realize_onTerm]; rfl
  | rel =>
    simp_all only [onBoundedFormula, realize_rel, realize_onTerm, map_onRelation]
    rfl
  | imp _ _ ih1 ih2 => simp only [onBoundedFormula, realize_imp, ih1, ih2]
  | all _ _ ih3 => simp only [onBoundedFormula, realize_all, ih3]

end LHom

namespace Formula

nonrec def Realize (φ : L.Formula α) (v : FamMap α M) : Prop :=
  φ.Realize v default

variable {φ ψ : L.Formula α} {v : α →ₛ M}

@[simp]
theorem realize_not : φ.not.Realize v ↔ ¬φ.Realize v :=
  Iff.rfl

@[simp]
theorem realize_bot : (⊥ : L.Formula α).Realize v ↔ False :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.Formula α).Realize v ↔ True :=
  BoundedFormula.realize_top

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v :=
  BoundedFormula.realize_inf

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v ↔ φ.Realize v → ψ.Realize v :=
  BoundedFormula.realize_imp

@[simp]
theorem realize_rel {ξ : Signature Sorts} {R : L.Relations ξ} {ts : L.Term α ξ} :
    (R.formula ts).Realize v ↔ RelMap (M := M) R (ts.realize v) := by
  refine BoundedFormula.realize_rel.trans ?_
  congr!
  simp_all only [PUnit.default_eq_unit, Term.mapVars, FamMap.mk_apply,
    Term.realize_bind, Term.realize_var]
  rfl

@[simp]
theorem realize_rel₁ {R : L.Relations ⦃s⦄} {t : L.Term α ⦃s⦄} :
    (R.formula₁ t).Realize v ↔ RelMap R (t.realize v) := by
  rw [Relations.formula₁, realize_rel, iff_eq_eq]

@[simp]
theorem realize_rel₂ {s₁ s₂} {R : L.Relations (⦃s₁⦄ ⨯ ⦃s₂⦄)} {t₁ : L.Term₁ α s₁}
    {t₂ : L.Term α ⦃s₂⦄} :
    (R.formula₂ t₁ t₂).Realize v ↔ RelMap R ((t₁.prod t₂).realize (L := L) (M := M) v) := by
  rw [Relations.formula₂, realize_rel, iff_eq_eq]




@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v :=
  BoundedFormula.realize_sup

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v ↔ (φ.Realize v ↔ ψ.Realize v) :=
  BoundedFormula.realize_iff

--Mathias: todo: need more simp lemmas like this one + for casted formulas
@[simp]
theorem realize_ex_root {α : Fam.{u'} Sorts} {φ : L.BoundedFormula α (⦃⦄ ⨯ ⦃s⦄)}
    {M : Fam.{w} Sorts} {v : α →ₛ M} [L.MSStructure M] :
    (Formula.Realize (BoundedFormula.ex ⦃s⦄ φ)) v ↔
    ∃ (x : M s), BoundedFormula.Realize φ v ⟨default, x⟩   := by
  simp only [Formula.Realize, BoundedFormula.ex, PUnit.default_eq_unit, Interpret.reduce_nil,
    BoundedFormula.realize_not, BoundedFormula.realize_all, not_forall, not_not]


@[simp]
theorem realize_all_root {α : Fam.{u'} Sorts} {φ : L.BoundedFormula α (⦃⦄ ⨯ ⦃s⦄)}
    {M : Fam.{w} Sorts} {v : α →ₛ M} [L.MSStructure M] :
    (Formula.Realize (BoundedFormula.all ⦃s⦄ φ)) v ↔
    ∀ (x : M s), BoundedFormula.Realize φ v ⟨default, x⟩   := by
  simp only [Formula.Realize, PUnit.default_eq_unit, Interpret.reduce_nil,
    BoundedFormula.realize_all]

/-
@[simp]
theorem realize_relabel {φ : L.Formula α} {g : α →ₛ β} {v : β →ₛ M} :
    (φ.relabel g).Realize v ↔ φ.Realize (v ∘ g) := by
  rw [Realize, Realize, relabel, BoundedFormula.realize_relabel, iff_eq_eq, Fin.castAdd_zero]
  exact congr rfl (funext finZeroElim)

theorem realize_relabel_sumInr (φ : L.Formula (Fin n)) {v : Empty → M} {x : M [^] σ} :
    (BoundedFormula.relabel Sum.inr φ).Realize v x ↔ φ.Realize x := by
  rw [BoundedFormula.realize_relabel, Formula.Realize, Sum.elim_comp_inr, Fin.castAdd_zero,
    cast_refl, Function.comp_id,
    Subsingleton.elim (x ∘ (natAdd n : Fin 0 → Fin n)) default]

@[deprecated (since := "2025-02-21")] alias realize_relabel_sum_inr := realize_relabel_sumInr
-/

@[simp]
theorem realize_equal {t₁ t₂ : L.Term α σ} {v : α →ₛ M} :
    (t₁.equal t₂).Realize v ↔ t₁.realize v = t₂.realize v := by
  rw [Formula.Realize, Term.equal, BoundedFormula.realize_bdEqual]
  simp_all only [PUnit.default_eq_unit, reduce_nil, Term.mapVars, Term.realize_bind,]
  rfl
/-- Realization of `Formula.graph`: the graph of a function symbol relates inputs to output.
The valuation `v` assigns values to the variables of type `(σ.prod (of s)).Idx`, which
represent both the input variables (from `σ`) and the output variable (from `of s`). -/
@[simp]
theorem realize_graph {f : L.Functions σ s} {v : (σ ⨯ ⦃s⦄).IdxFam →ₛ M} :
    (Formula.graph f).Realize v ↔
      v s (.right .var) = funMap f (fromGet ⟨fun t w => v t (.left w)⟩) := by
  rw [Formula.graph, realize_equal]
  simp only [Term.realize_var, Term.realize_func, Term.realize_mapVars, Term.realize_varterm]
  rfl

theorem boundedFormula_realize_eq_realize (φ : L.Formula α) (v : α →ₛ M) (ys : ⦃⦄.Interpret M) :
    BoundedFormula.Realize φ v ys ↔ φ.Realize v := by
  rw [Formula.Realize, iff_iff_eq, Unique.eq_default ys]

end Formula

namespace BoundedFormula
variable {v : α →ₛ M}

@[simp]
theorem realize_fully_instantiate {τ : Signature Sorts}
    (φ : L.BoundedFormula α τ)
    (t : L.Term (α ⊕ₛ ⦃⦄.IdxFam) τ)
    (v : α →ₛ M) :
    (φ.fully_instantiate t).Realize v ↔
      φ.Realize v (t.realize (Fam.sumElim v (default : M[^]⦃⦄))) := by
  unfold fully_instantiate Formula.Realize
  rw[realize_instantiate, PUnit.default_eq_unit, realize_reindex]
  congr!; ext; simp_all only [reduce_nil, get_comap]; rfl

@[simp]
theorem realize_boundedFormula {ξ : Signature Sorts} {xs : M [^] ξ}
    (φ : L.Formula σ.IdxFam) (ts : L.Term (α ⊕ₛ ξ.IdxFam) σ) :
    (φ.boundedFormula ts).Realize v xs =
    φ.Realize (M := M) (ts.realize (Fam.sumElim v xs)) := by
  rw [Formula.boundedFormula, Formula.Realize]
  simp_all only [realize_subst, realize_reindex, PUnit.default_eq_unit, eq_iff_iff]
  have : comap (default : SigMap ⦃⦄ ξ) xs = PUnit.unit := by simp
  rw[this]
  congr!
  rw[←Term.realize_getLeafTerm]
  rfl

@[simp]
theorem realize_boundedFormula₁ {ξ : Signature Sorts} {xs : ξ.Interpret M}
    (φ : L.Formula ⦃s⦄.IdxFam) (t : L.Term (α ⊕ₛ ξ.IdxFam) ⦃s⦄) :
    (φ.boundedFormula₁ t).Realize v xs = φ.Realize (M := M) (t.realize (Fam.sumElim v xs)) := by
  rw [Formula.boundedFormula₁]
  exact realize_boundedFormula φ t

@[simp]
theorem realize_boundedFormula₂ {s t : Sorts} {ξ : Signature Sorts} {xs : ξ.Interpret M}
    (φ : L.Formula (⦃s⦄.prod ⦃t⦄).IdxFam) (t₁ : L.Term (α ⊕ₛ ξ.IdxFam) ⦃s⦄)
    (t₂ : L.Term (α ⊕ₛ ξ.IdxFam) ⦃t⦄) :
    (φ.boundedFormula₂ t₁ t₂).Realize v xs = φ.Realize (M := M)
    ((t₁.prod t₂).realize (Fam.sumElim v xs)) := by
  rw [Formula.boundedFormula₂]
  exact realize_boundedFormula φ (t₁.prod t₂)

variable {ξ : Signature Sorts} {xs : ξ.Interpret M}


end BoundedFormula

@[simp]
theorem LHom.realize_onFormula [L'.MSStructure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Formula α) {v : α →ₛ M} : (φ.onFormula ψ).Realize v ↔ ψ.Realize v :=
  φ.realize_onBoundedFormula ψ

@[simp]
theorem LHom.setOf_realize_onFormula [L'.MSStructure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Formula α) : (setOf (φ.onFormula ψ).Realize : Set (FamMap α M)) = setOf ψ.Realize := by
  ext
  simp only [Set.mem_setOf_eq, realize_onFormula]

variable (M)

/-- A sentence can be evaluated as true or false in a MSStructure. -/
nonrec def Sentence.Realize (φ : L.Sentence) : Prop :=
  φ.Realize (default : Fam.EmptyFam →ₛ M)

-- input using \|= or \vDash, but not using \models
@[inherit_doc Sentence.Realize]
infixl:51 " ⊨ " => Sentence.Realize

instance varFreeAssignUnique {β : Fam Sorts} : Unique ((EmptyFam ⊕ₛ ⦃⦄.IdxFam) →ₛ β) := by
  letI : ∀ s : Sorts, IsEmpty ((EmptyFam ⊕ₛ ⦃⦄.IdxFam) s) := by
    intro s
    change IsEmpty (Empty ⊕ ⦃⦄.IdxFam s)
    infer_instance
  infer_instance

@[simp]
lemma varFreeAssign_eq_default {β : Fam Sorts} {v : (EmptyFam ⊕ₛ ⦃⦄.IdxFam) →ₛ β} : v = default :=
  by
    ext s x
    cases x with
    | inl e => cases e
    | inr u => cases u

@[simp]
theorem Sentence.realize_equals {t₁ t₂ : L.Term (EmptyFam ⊕ₛ ⦃⦄.IdxFam) σ} :
  M ⊨ t₁.bdEqual t₂ ↔ (t₁.realize (M:= M) default = t₂.realize default) := by
  simp only [Realize, Formula.Realize, PUnit.default_eq_unit, BoundedFormula.realize_bdEqual,
    varFreeAssign_eq_default]

@[simp]
theorem Sentence.realize_rel {r : L.Relations σ} {t : L.Term (EmptyFam ⊕ₛ ⦃⦄.IdxFam) σ} :
  M ⊨ BoundedFormula.rel r t ↔ RelMap (M:= M) r (t.realize default)  := by
  simp only [Realize, Formula.Realize, BoundedFormula.Realize, PUnit.default_eq_unit,
    varFreeAssign_eq_default]

@[simp]
theorem Sentence.realize_not {φ : L.Sentence} : M ⊨ φ.not ↔ ¬M ⊨ φ :=
  Iff.rfl

@[simp]
theorem Sentence.realize_bot : M ⊨ (⊥ : L.Sentence) ↔ False :=
  Iff.rfl

@[simp]
theorem Sentence.realize_top : M ⊨ (⊤ : L.Sentence) ↔ True := by
  -- Unfold Sentence.Realize -> Formula.Realize -> BoundedFormula.Realize
  simp only [Realize, Formula.Realize, PUnit.default_eq_unit, BoundedFormula.realize_top]

@[simp]
theorem Sentence.realize_inf {φ ψ : L.Sentence} : M ⊨ φ ⊓ ψ ↔ M ⊨ φ ∧ M ⊨ ψ := by
  simp only [Realize, Formula.Realize, PUnit.default_eq_unit, BoundedFormula.realize_inf]

@[simp]
theorem Sentence.realize_sup {φ ψ : L.Sentence} : M ⊨ φ ⊔ ψ ↔ M ⊨ φ ∨ M ⊨ ψ := by
  simp only [Realize, Formula.Realize, PUnit.default_eq_unit, BoundedFormula.realize_sup]

@[simp]
theorem Sentence.realize_imp {φ ψ : L.Sentence} : M ⊨ (φ ⟹ ψ) ↔ (M ⊨ φ → M ⊨ ψ) := by
  simp only [Realize, Formula.Realize, PUnit.default_eq_unit, BoundedFormula.realize_imp]

@[simp]
theorem Sentence.realize_iff {φ ψ : L.Sentence} : M ⊨ (φ ⇔ ψ) ↔ (M ⊨ φ ↔ M ⊨ ψ) := by
  simp only [Realize, Formula.Realize, PUnit.default_eq_unit, BoundedFormula.realize_iff]

section localize_formula

namespace BoundedFormula.LocalForm

variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
variable {σ : Signature Sorts} {φ : L.BoundedFormula α σ} (lf : φ.LocalForm)

/-- Pull a valuation back through the localization equivalence. -/
noncomputable def comap (M) (v : α →ₛ M) :
    lf.τ.IdxFam →ₛ M :=
    v ∘ₛ ⟨fun _ v => Subtype.val v⟩ ∘ₛ lf.e.invFun

/-- Build a tuple from a valuation, for use with `toBoundedFormula`.
  Only for `Formula` (σ = nil). -/
noncomputable def toTuple {φ : L.Formula α} (lf : φ.LocalForm) (M) (v : α →ₛ M) :
    M[^]lf.τ :=
    fromGet (lf.comap M v)

@[simp] lemma get_toTuple {φ : L.Formula α} (lf : φ.LocalForm) (M) (v : α →ₛ M) :
    Interpret.get (lf.toTuple M v) = lf.comap M v := by
  simp only [toTuple, fromGet_get]

/-- `toFormula` preserves realization when the valuation is transformed via `comap`. -/
@[simp] theorem realize_toFormula
  {M : Fam.{w} Sorts} [L.MSStructure M]
  (v : α →ₛ M)
  (xs : M [^] σ) :
  lf.toFormula.Realize (lf.comap M v) xs
    ↔
  φ.Realize v xs := by
  classical
  unfold toFormula comap
  apply realize_restrictFreeVar
  intro s a h
  change v s ((lf.e.invFun s (lf.e.toFun s ⟨a, h⟩)).1) = v s a
  simp_all only [MSEquiv.inv_to]

@[simp] lemma comap_fromGet {S : Type*} {X : Fam S} {σ τ : Signature S}
    (f : IdxFam τ →ₛ X) (g : SigMap σ τ) :
  (fromGet f).comap g = fromGet (f ∘ₛ g) := by
  ext s v : 1
  simp_all only [get_comap, fromGet_get, FamMap.comp_apply']
  rfl

/-
(nil, x) ==> (x : M [^] τ) ==>

@[simp] lemma fromGet_comap {M : Fam.{w} Sorts} [L.MSStructure M]
  {φ : L.Formula α} (lf : φ.LocalForm) (v : α →ₛ M) :
    (fromGet (comap lf M v ∘ₛ (SigEquiv.nilLeft lf.τ).toFun)) = sorry := by
  unfold comap
  sorry
-/







--lemma fromGet_get_nil_factor (a : M[^]⦃⦄ ⨯ σ) : a.2.get s x = a.get
--TODO: clean this proof up.
/-- Semantic correctness for `toBoundedFormula`. Only for `Formula` (σ = nil). -/
theorem realize_toBoundedFormula
  {M : Fam.{w} Sorts} [L.MSStructure M]
  {φ : L.Formula α} (lf : φ.LocalForm)
  (x : α →ₛ M) :
  φ.Realize x ↔
    lf.toBoundedFormula.Realize default (lf.toTuple M x) := by
    unfold toBoundedFormula toTuple;
    simp only [rename_rename, realize_reindex]
    rw[realize_closeVars, realize_rename, realize_restrictFreeVar (M:= M) (v':= x) ]
    · unfold Formula.Realize
      rw[PUnit.eq_punit default]
    · intro s a h
      simp_all only [comap_fromGet, FamMap.idₛ_apply', FamMap.comp_apply', FamMap.mk_apply,
        sumElim_eval_r]
      unfold comap
      simp only [fromGet_right, FamMap.comp_apply', SigMap.incl_right_apply]
      simp only [mk_apply, FamMap.mk_apply, coeFun_apply]
      change (x s (Subtype.val (lf.e.invFun s ((SigEquiv.nilLeft lf.τ).toFun s
        (lf.e.toFun s ⟨a, h⟩).right))) ) = x s a
      congr!
      unfold SigEquiv.nilLeft SigMap.nil_left
      simp only [FamMap.mk_apply, MSEquiv.inv_to]

/-- Semantic correctness for `toFormula` at the formula level (σ = nil). -/
theorem realize_toFormula_formula
  {M : Fam.{w} Sorts} [L.MSStructure M]
  {φ : L.Formula α} (lf : φ.LocalForm)
  (x : α →ₛ M) :
  φ.Realize x ↔
    Formula.Realize (lf.toFormula) (lf.comap M x) := by
    unfold toFormula Formula.Realize comap
    rw[φ.realize_restrictFreeVar]
    intro s a h
    change x s ((lf.e.invFun s (lf.e.toFun s ⟨a, h⟩)).1) = x s a
    simp_all only [MSEquiv.inv_to]

end BoundedFormula.LocalForm

namespace Formula
variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)]

/-- The realized equivalence for `toBoundedFormula`, as a clean lemma. -/
theorem realize_toBoundedFormula_iff (φ : L.Formula α) (v : α →ₛ M) :
    φ.Realize v ↔
      (φ.localize).toBoundedFormula.Realize default (φ.localize.toTuple M v) := by
  rw[φ.localize.realize_toBoundedFormula ]

/-- The realized equivalence for `toFormula`, as a clean lemma. -/
theorem realize_toFormula_iff (φ : L.Formula α) (v : α →ₛ M) :
    φ.Realize v ↔
      Formula.Realize (φ.localize).toFormula (φ.localize.comap M v) := by
    rw[φ.localize.realize_toFormula_formula ]

end Formula
end localize_formula

@[simp]
theorem LHom.realize_onSentence [L'.MSStructure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Sentence) : M ⊨ φ.onSentence ψ ↔ M ⊨ ψ :=
  φ.realize_onFormula ψ

variable (L)

/-- The complete theory of a MSStructure `M` is the set of all sentences `M` satisfies. -/
def completeTheory : L.Theory :=
  { φ | M ⊨ φ }

variable (N)

/-- Two MSStructures are elementarily equivalent when they satisfy the same sentences. -/
def ElementarilyEquivalent : Prop :=
  L.completeTheory M = L.completeTheory N

@[inherit_doc MSFirstOrder.MSLanguage.ElementarilyEquivalent]
scoped[MSFirstOrder]
  notation:25 A " ≅[" L "] " B:50 => MSFirstOrder.MSLanguage.ElementarilyEquivalent L A B

variable {L} {M} {N}

@[simp]
theorem mem_completeTheory {φ : Sentence L} : φ ∈ L.completeTheory M ↔ M ⊨ φ :=
  Iff.rfl

theorem elementarilyEquivalent_iff : M ≅[L] N ↔ ∀ φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ := by
  simp only [ElementarilyEquivalent, Set.ext_iff, completeTheory, Set.mem_setOf_eq]

variable (M)

/-- A model of a theory is a structure in which every sentence is realized as true. -/
class Theory.Model (T : L.Theory) : Prop where
  realize_of_mem : ∀ φ ∈ T, M ⊨ φ

-- input using \|= or \vDash, but not using \models
@[inherit_doc Theory.Model]
infixl:51 " ⊨ " => Theory.Model

variable {M} (T : L.Theory)

@[simp default - 10]
theorem Theory.model_iff : M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ :=
  ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩

theorem Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.Sentence} (h : φ ∈ T) : M ⊨ φ :=
  Theory.Model.realize_of_mem φ h

@[simp]
theorem LHom.onTheory_model [L'.MSStructure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (T : L.Theory) :
    M ⊨ φ.onTheory T ↔ M ⊨ T := by simp only [onTheory, Theory.model_iff, Set.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, realize_onSentence]

variable {T}

instance model_empty : M ⊨ (∅ : L.Theory) :=
  ⟨fun φ hφ => (Set.notMem_empty φ hφ).elim⟩

namespace Theory

theorem Model.mono {T' : L.Theory} (_h : M ⊨ T') (hs : T ⊆ T') : M ⊨ T :=
  ⟨fun _φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩

theorem Model.union {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T') : M ⊨ T ∪ T' := by
  simp only [model_iff, Set.mem_union] at *
  exact fun φ hφ => hφ.elim (h _) (h' _)

@[simp]
theorem model_union_iff {T' : L.Theory} : M ⊨ T ∪ T' ↔ M ⊨ T ∧ M ⊨ T' :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[simp]
theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by
  simp only [model_iff, Set.mem_singleton_iff, forall_eq]

theorem model_insert_iff {φ : L.Sentence} : M ⊨ insert φ T ↔ M ⊨ φ ∧ M ⊨ T := by
  rw [Set.insert_eq, model_union_iff, model_singleton_iff]

theorem model_iff_subset_completeTheory : M ⊨ T ↔ T ⊆ L.completeTheory M :=
  T.model_iff

theorem completeTheory.subset [MT : M ⊨ T] : T ⊆ L.completeTheory M :=
  model_iff_subset_completeTheory.1 MT

end Theory

instance model_completeTheory : M ⊨ L.completeTheory M :=
  Theory.model_iff_subset_completeTheory.2 (subset_refl _)

variable (M N)

theorem realize_iff_of_model_completeTheory [N ⊨ L.completeTheory M] (φ : L.Sentence) :
    N ⊨ φ ↔ M ⊨ φ := by
  refine ⟨fun h => ?_, (L.completeTheory M).realize_sentence_of_mem⟩
  contrapose! h
  rw [← Sentence.realize_not] at *
  exact (L.completeTheory M).realize_sentence_of_mem (mem_completeTheory.2 h)

variable {M N}

namespace BoundedFormula

variable {σ : Signature Sorts}

@[simp]
theorem realize_alls {σ : Signature Sorts} {φ : L.BoundedFormula α σ} {v : α →ₛ M} :
    φ.alls.Realize v ↔ ∀ xs : M [^] σ, φ.Realize v xs := by
  induction σ with
  | nil =>
    simp_all only [reduce_nil, PUnit.default_eq_unit, forall_const]
    rfl
  | of s =>
    simp only [Formula.Realize, alls, Signature.SigEquiv.symm, Signature.Interpret, reduce_nil,
      PUnit.default_eq_unit, realize_all, realize_reindex]
    rfl
  | prod σ₁ σ₂ ih₁ ih₂ =>
    simp_all only [Formula.Realize, Signature.Interpret, reduce_nil, PUnit.default_eq_unit, alls,
      realize_all, Prod.forall]

@[simp]
theorem realize_exs {σ : Signature Sorts} {φ : L.BoundedFormula α σ} {v : α →ₛ M} :
    φ.exs.Realize v ↔ ∃ xs : M [^] σ, φ.Realize v xs := by
  induction σ with
  | nil =>
    simp_all only [reduce_nil, PUnit.default_eq_unit, exists_const]
    rfl
  | of s =>
    simp only [Formula.Realize, exs, Signature.SigEquiv.symm, Signature.Interpret, reduce_nil,
      PUnit.default_eq_unit, realize_ex, realize_reindex]
    rfl
  | prod σ₁ σ₂ ih₁ ih₂ =>
    simp_all  only [Formula.Realize, Signature.Interpret, reduce_nil, PUnit.default_eq_unit, exs,
      realize_ex, Prod.exists]

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iAlls
    [Finite (Sigma β)] {φ : L.Formula (α ⊕ₛ β)} {v : α →ₛ M} :
    (φ.iAlls β).Realize v ↔
      ∀ (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
  simp only [Formula.iAlls, realize_alls, Prod.forall]
  simp only [Formula.Realize, PUnit.default_eq_unit]
  let σ := (Signature.famToSignature β).fst
  let e : β ≃ₛ σ.IdxFam := (Signature.famToSignature β).snd
  simp only [realize_relabel φ]
  apply Iff.intro
  · intro h v'
    let h' := h (Interpret.fromGet (v' ∘ₛ e.symm )) PUnit.unit
    apply realize_eq_val h'
    ext s w
    cases w
    case inl =>
      simp_all only [fromGet_get, sumElim_eval_l, σ, e]
      rfl
    case inr u =>
      simp only [fromGet_get, sumElim_eval_r, sumMap_inr_apply, coeFun_apply, FamMap.comp_apply']
      exact congrArg (fun x => v' s x) (MSEquiv.symm_toFun_toFun e s u)
  · intro h xs b
    simp_all only [reduce_nil, PUnit.default_eq_unit]
    have h':  ⟨fun s a ↦ (Fam.sumElim v xs.get) s
            ((sumMap FamMap.idₛ (famToSignature β).snd.toFun) s a)⟩
             = Fam.sumElim v (xs.get ∘ₛ (famToSignature β).snd.toFun) := by
      ext s w
      simp_all only [Fam.sumElim, sumMap, FamMap.idₛ, FamMap.mk_apply]
      cases w
      case inl => simp_all only [Sum.map_inl, id_eq, Sum.elim_inl]
      case inr => simp_all only [Sum.map_inr, Sum.elim_inr, FamMap.comp_apply']
    change Realize φ ⟨fun s a ↦ (Fam.sumElim v xs.get) s
        ((sumMap FamMap.idₛ (famToSignature β).snd.toFun) s a)⟩  PUnit.unit
    rw[h']
    apply h

@[simp]
theorem realize_iAlls [Finite (Sigma β)] {φ : L.Formula (α ⊕ₛ β)} {v : α →ₛ M}
    {xs : ⦃⦄.Interpret M} : BoundedFormula.Realize (φ.iAlls β) v xs ↔
      ∀ (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
  rw [← Formula.realize_iAlls, iff_iff_eq, Formula.Realize]

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iExs
    [Finite (Sigma β)] {φ : L.Formula (α ⊕ₛ β)} {v : α →ₛ M} :
    (φ.iExs β).Realize v ↔
      ∃ (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
  simp only [Formula.iExs, realize_exs, Prod.exists]
  simp only [Formula.Realize, PUnit.default_eq_unit]
  rcases (famToSignature β) with ⟨σ, e⟩
  simp only [Formula] at φ
  constructor
  · rintro ⟨a, ⟨b, hab⟩⟩
    refine ⟨a.get ∘ₛ e, ?_⟩
    simp_all only [PUnit.eq_punit]
    rw[realize_relabel] at hab
    simp only [FamMap.mk_apply] at hab
    apply realize_eq_val hab
    ext s v
    cases v
    · simp_all only [coeFun_apply, Sum.map_inl, id_eq, sumElim_eval_l]
    · simp_all only [coeFun_apply, Sum.map_inr, sumElim_eval_r, FamMap.comp_apply']
      rfl
  · rintro ⟨i, hi⟩
    refine ⟨Interpret.fromGet (i ∘ₛ e.symm), ?_⟩
    use default
    simp_all only [PUnit.eq_punit]
    rw[realize_relabel]
    apply realize_eq_val hi
    ext s v
    cases v
    · simp_all only [sumElim_eval_l, fromGet_get, FamMap.mk_apply, coeFun_apply, Sum.map_inl,
      id_eq]
    case inr a =>
      simp_all only [sumElim_eval_r, fromGet_get, FamMap.mk_apply, coeFun_apply,
        Sum.map_inr, FamMap.comp_apply']
      rw[← MSEquiv.inv_to e s a]
      congr!
      simp only [MSEquiv.inv_to]


@[simp]
theorem realize_iExs
    [Finite (Sigma β)] {φ : L.Formula (α ⊕ₛ β)} {v : α →ₛ M}
    {xs : ⦃⦄.Interpret M} :
    BoundedFormula.Realize (φ.iExs β) v xs ↔
      ∃ (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
    rw[←Formula.realize_iExs]
    simp only [reduce_nil, PUnit.default_eq_unit, Formula.Realize]

/-
@[simp]
theorem realize_toFormula (φ : L.BoundedFormula α σ) (v : (α ⊕ₛ σ.IdxFam) →ₛ M) :
    φ.toFormula.Realize v ↔ φ.Realize (v ∘ₛ Fam.Sum_inl)
    (sorted_tupleFromFam (v ∘ₛ Fam.Sum_inr)) := by
  induction φ with
  | falsum => rfl
  | equal => simp?[BoundedFormula.Realize]
  | rel => simp?[BoundedFormula.Realize]
  | imp _ _ ih1 ih2 =>
    rw [toFormula, Formula.Realize, realize_imp, ← Formula.Realize, ih1, ← Formula.Realize, ih2,
      realize_imp]
  | all _ ih3 =>
    rw [toFormula, Formula.Realize, realize_all, realize_all]
    refine forall_congr' fun a => ?_
    have h := ih3 (Sum.elim (v ∘ Sum.inl) (snoc (v ∘ Sum.inr) a))
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    rw [← h, realize_relabel, Formula.Realize, iff_iff_eq]
    simp only [Function.comp_def]
    congr with x
    · rcases x with _ | x
      · simp?
      · refine Fin.lastCases ?_ ?_ x
        · rw [Sum.elim_inr, Sum.elim_inr,
            finSumFinEquiv_symm_last, Sum.map_inr, Sum.elim_inr]
          simp?[Fin.snoc]
        · simp only [castSucc, Sum.elim_inr,
            finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, Sum.elim_inl]
          rw [← castSucc]
          simp?
    · exact Fin.elim0 x
-/





/-! ### Semantic lemmas for additional syntactic operations -/

/-
/-- Realization of `substFreeVars`: substituting only the free variables that occur in the formula.
This relates to `realize_subst` but handles the restriction to occurring variables.
-/
theorem realize_substFreeVars [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {φ : L.BoundedFormula α σ}
    (f : ∀ (s), {x : α s // ⟨s, x⟩ ∈ freeVarFinset φ} → L.Term (β ⊕ₛ σ.IdxFam) ⦃s⦄)
    {v : β →ₛ M} {xs : M [^] σ} :
    (φ.substFreeVars f).Realize v xs ↔
      φ.Realize (fun s a => (f s ⟨a, sorry⟩).realize (Fam.sumElim v xs)) xs := by
  -- Proof: unfold substFreeVars as restrictFreeVar followed by subst,
  -- then use realize_restrictFreeVar and realize_subst

  sorry
-/

/-- Realization of `mapTermRelEquiv`: mapping terms and relations via equivalences preserves
  satisfaction when the equivalences preserve realization. -/
theorem realize_mapTermRelEquiv
    {L' : MSLanguage.{u, v, z} Sorts}
    {β : Fam Sorts}
    (ft : ∀ (ξ τ : Signature Sorts), L.Term (α ⊕ₛ ξ.IdxFam) τ ≃ L'.Term (β ⊕ₛ ξ.IdxFam) τ)
    (fr : ∀ ξ, L.Relations ξ ≃ L'.Relations ξ)
    [L'.MSStructure M]
    {φ : L.BoundedFormula α σ} {v : α →ₛ M} {w : β →ₛ M} {xs : M [^] σ}
    (hft : ∀ ξ τ (t : L.Term (α ⊕ₛ ξ.IdxFam) τ) (ys : ξ.Interpret M),
      (ft ξ τ t).realize (Fam.sumElim w ys) =
        t.realize (Fam.sumElim v ys))
    (hfr : ∀ ξ (R : L.Relations ξ) (ys : ξ.Interpret M), RelMap (fr ξ R) ys ↔ RelMap R ys) :
    ((mapTermRelEquiv ft fr) φ).Realize w xs ↔ φ.Realize v xs := by
  simp only [mapTermRelEquiv, Equiv.coe_fn_mk]
  exact realize_mapTermRel_id (fun ξ τ => ft ξ τ) (fun ξ => fr ξ)
    (fun ξ τ t ys => hft ξ τ t ys) (fun ξ R ys => propext (hfr ξ R ys))

/-- Realization of `relabelEquiv`: renaming free variables via an equivalence preserves
  satisfaction. TODO: rename `relabelEquiv` to `renameEquiv` ? -/
@[simp]
theorem realize_relabelEquiv {β : Fam Sorts} (e : α ≃ₛ β) {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ) {v : β →ₛ M} {xs : M [^] σ} :
    (relabelEquiv e φ).Realize v xs ↔ φ.Realize (v ∘ₛ e.toFun) xs := by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  refine realize_mapTermRel_id _ _ (fun σ ξ t xs => ?_) fun _ _ _ => rfl
  simp only [Term.mapVarsEquiv_apply, Term.realize_mapVars]
  refine congr (congr rfl ?_) rfl
  ext _ x
  cases x <;> rfl


/-- Realization of `constantsVarsEquiv`: translating constants to variables preserves satisfaction
when constants are interpreted as the given valuation. -/
@[simp]
theorem realize_constantsVarsEquiv {γ : Fam Sorts}
    [L[[γ]].MSStructure M] [(lhomWithConstants L γ).IsExpansionOn M]
    {φ : (L[[γ]]).BoundedFormula α σ} {v : α →ₛ M} {xs : M [^] σ} :
    (constantsVarsEquiv φ).Realize (Fam.sumElim ⟨fun s a => (L.con s a : M s)⟩ v) xs ↔
    φ.Realize v xs := by
  refine realize_mapTermRel_id _ _ (fun σ ξ t xs => Term.realize_constantsVarsEquivLeft)
    (fun σ R xs => ?_)
  erw [← (lhomWithConstants L γ).map_onRelation
      (Equiv.sumEmpty (L.Relations σ) ((constantsOn α).Relations σ) R) xs]
  rcongr
  obtain - | R := R
  · simp only [constantsOn_Relations, lhomWithConstants_onRelation]
    rfl
  · exact isEmptyElim R

/-- Realization of `bigAnd`: conjunction of a list of formulas. -/
@[simp]
theorem realize_bigAnd (l : List (L.BoundedFormula α σ)) {v : α →ₛ M} {xs : M [^] σ} :
    (bigAnd l).Realize v xs ↔ ∀ φ ∈ l, φ.Realize v xs := by
  simp only [bigAnd, realize_foldr_inf]

/-- Realization of `bigOr`: disjunction of a list of formulas. -/
@[simp]
theorem realize_bigOr (l : List (L.BoundedFormula α σ)) {v : α →ₛ M} {xs : M [^] σ} :
    (bigOr l).Realize v xs ↔ ∃ φ ∈ l, φ.Realize v xs := by
  simp only [bigOr, realize_foldr_sup]

@[simp]
theorem realize_iSup {X}
    [Finite X] {ξ : Signature Sorts} {f : X → L.BoundedFormula α ξ}
    {v : α →ₛ M} {xs : ξ.Interpret M} :
    (BoundedFormula.iSup f).Realize v xs ↔ ∃ b, (f b).Realize v xs := by
  rw [iSup, realize_bigOr]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, exists_exists_eq_and]

@[simp]
theorem realize_iInf {X}
    [Finite X] {ξ : Signature Sorts} {f : X → L.BoundedFormula α ξ}
    {v : α →ₛ M} {xs : ξ.Interpret M} :
    (BoundedFormula.iInf f).Realize v xs ↔ ∀ b, (f b).Realize v xs := by
  rw [iInf, realize_bigAnd]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]


@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iSup {X} [Finite X] {f : X → L.Formula α}
    {v : α →ₛ M} : (Formula.iSup f).Realize v ↔ ∃ b, (f b).Realize v := by
  simp only [Formula.Realize, Formula.iSup, PUnit.default_eq_unit, BoundedFormula.realize_iSup]

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iInf {X} [Finite X] {f : X → L.Formula α}
    {v : α →ₛ M} : (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v := by
  simp only [Formula.Realize, Formula.iInf, PUnit.default_eq_unit, BoundedFormula.realize_iInf]


theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iExsUnique {X : Fam Sorts} [Finite (Sigma X)]
    {φ : L.Formula (α ⊕ₛ X)} {v : α →ₛ M} : (φ.iExsUnique X).Realize v ↔
      ∃! (i : X →ₛ M), φ.Realize (Fam.sumElim v i) := by
  rw [Formula.iExsUnique, ExistsUnique]
  simp only [Formula.Realize, PUnit.default_eq_unit, realize_iExs, realize_inf, realize_iAlls,
    realize_imp, realize_rename, realize_iInf]
  refine exists_congr (fun i => and_congr_right' (forall_congr' (fun y => ?_)))
  apply Iff.intro
  · intro h h'
    ext s a
    have : Realize φ (Fam.sumElim (Fam.sumElim v i) y ∘ₛ Fam.sumElim (inl ∘ₛ inl) inr) PUnit.unit :=
      by
      apply realize_eq_val h'
      ext s w
      cases w
      · simp_all only [sumElim_eval_l, FamMap.comp_apply']
        rfl
      · simp_all only [sumElim_eval_r, FamMap.comp_apply']
        rfl
    let h'' := h this ⟨s, a⟩
    simp[Term.equal, Fam.sumElim, Interpret.get, Fam.inl] at h''
    simp[h'']
  · intro hi h sx
    simp only [Term.equal, Term.mapVars, Term.bind, inl, FamMap.mk_apply, Fam.sumElim,
      realize_bdEqual, Interpret.get, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    rw[hi]
    apply realize_eq_val h
    ext s w
    cases w <;>
    simp_all only [FamMap.comp_apply', sumElim_eval_l]
    <;> obtain ⟨fst, snd⟩ := sx <;> rfl

@[simp]
theorem realize_iExsUnique
    [Finite (Sigma β)] {φ : L.Formula (α ⊕ₛ β)} {v : α →ₛ M} {xs : ⦃⦄.Interpret M} :
    BoundedFormula.Realize (φ.iExsUnique β) v xs ↔
      ∃! (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
  -- same pattern as your `realize_iAlls` / `realize_iExs`
  rw [← Formula.realize_iExsUnique (L := L) (M := M) (φ := φ) (v := v),
      iff_iff_eq, Formula.Realize]


end BoundedFormula

namespace Formula

variable (M)

@[simp]
theorem realize_equivSentence_symm_con [L[[α]].MSStructure M]
    [(L.lhomWithConstants α).IsExpansionOn M] (φ : L[[α]].Sentence) :
    ((equivSentence.symm φ).Realize ⟨fun s a => (L.con s a : M s)⟩) ↔ φ.Realize M := by
  simp only [equivSentence, _root_.Equiv.symm_symm, Equiv.coe_trans, Realize,
    BoundedFormula.realize_relabelEquiv, Function.comp]
  refine _root_.trans ?_ BoundedFormula.realize_constantsVarsEquiv
  rw [iff_iff_eq]
  congr with s x
  · cases x
    case inl a => rfl
    case inr v => exact isEmptyElim v


@[simp]
theorem realize_equivSentence [L[[α]].MSStructure M] [(L.lhomWithConstants α).IsExpansionOn M]
    (φ : L.Formula α) : (equivSentence φ).Realize M ↔ φ.Realize ⟨fun s a => (L.con s a : M s)⟩ := by
  rw [← realize_equivSentence_symm_con M (equivSentence φ), _root_.Equiv.symm_apply_apply]


theorem realize_equivSentence_symm (φ : L[[α]].Sentence) (v : FamMap α M) :
    (equivSentence.symm φ).Realize v ↔
      @Sentence.Realize Sorts _  M
      (@MSLanguage.withConstantsStructure Sorts L M _ α (constantsOn.structure v))
        φ :=
  letI := constantsOn.structure v
  realize_equivSentence_symm_con M φ


end Formula

namespace StrongHomClass

variable {F : Type*} [StrongEquivHomClass L F M N] (g : F)

@[simp]
theorem realize_boundedFormula {σ} (φ : L.BoundedFormula α σ) {v : α →ₛ M}
    {xs : M [^] σ} : φ.Realize ((g : M →ₛ N) ∘ₛ v) (g <$>ₛ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [BoundedFormula.Realize, get_map, ← Fam.sumComp_elim, HomClass.realize_term]
    refine Function.Injective.eq_iff
      (Function.HasLeftInverse.injective ⟨Interpret.map (StrongEquivHomClass.inv g), ?_⟩)
    intro ys
    have hmap :
        StrongEquivHomClass.inv g <$>ₛ (g <$>ₛ ys)
          = (((StrongEquivHomClass.inv g) ∘ₛ (g : M →ₛ N)) <$>ₛ ys) := by
      simpa using
        (Interpret.comp_map (φ := (g : M →ₛ N)) (ψ := StrongEquivHomClass.inv g) (xs := ys)).symm
    calc
      StrongEquivHomClass.inv g <$>ₛ (g <$>ₛ ys)
          = (((StrongEquivHomClass.inv g) ∘ₛ (g : M →ₛ N)) <$>ₛ ys) := hmap
      _ = (Fam.FamMap.idₛ <$>ₛ ys) := by
          simp only [StrongEquivHomClass.inv_comp, map_id]
      _ = ys := by
          simp only [map_id]
  | rel =>
    rename_i σ' σ R ts
    simp only [BoundedFormula.Realize, get_map, ← Fam.sumComp_elim, HomClass.realize_term]
    exact StrongHomClass.map_rel g _ _
  | imp _ _ ih₁ ih₂ =>
    simpa [BoundedFormula.Realize] using (Iff.imp ih₁ ih₂)
  | all η φ ih =>
    simp only [BoundedFormula.Realize]
    constructor
    · intro h ys
      have h' := h (g <$>ₛ ys)
      have h'' : φ.Realize ((g : M →ₛ N) ∘ₛ v) (g <$>ₛ (xs, ys)) := by
        simpa [Interpret.map_prod] using h'
      exact (ih (xs := (xs, ys))).1 h''
    · intro h ys
      have h' := h (StrongEquivHomClass.inv g <$>ₛ ys)
      have h'' : φ.Realize ((g : M →ₛ N) ∘ₛ v) (g <$>ₛ (xs, StrongEquivHomClass.inv g <$>ₛ ys)) :=
        by
        exact (ih (xs := (xs, StrongEquivHomClass.inv g <$>ₛ ys))).2 h'
      have h''' : φ.Realize ((g : M →ₛ N) ∘ₛ v)
          ((g : M →ₛ N) <$>ₛ xs,
            (g : M →ₛ N) <$>ₛ (StrongEquivHomClass.inv g) <$>ₛ ys) := by
        rw[←Interpret.map_prod]
        simpa only [mapClass_eq_map] using h''
      have hy : (g : M →ₛ N) <$>ₛ ((StrongEquivHomClass.inv g) <$>ₛ ys) = ys := by
        have hmap :
            g <$>ₛ (StrongEquivHomClass.inv g <$>ₛ ys)
              = (((g : M →ₛ N) ∘ₛ (StrongEquivHomClass.inv g)) <$>ₛ ys) := by
          simpa using
            (Interpret.comp_map (φ := StrongEquivHomClass.inv g)
            (ψ := (g : M →ₛ N)) (xs := ys)).symm
        calc
          g <$>ₛ (StrongEquivHomClass.inv g <$>ₛ ys)
              = (((g : M →ₛ N) ∘ₛ (StrongEquivHomClass.inv g)) <$>ₛ ys) := hmap
          _ = (Fam.FamMap.idₛ <$>ₛ ys) := by
              simp only [StrongEquivHomClass.comp_inv, mapClass_eq_map]
          _ = ys := by
              simp only [map_id]
      rw[←hy]
      simp_all only [mapClass_eq_map, Prod.forall]
      exact h'''


@[simp]
theorem realize_formula (φ : L.Formula α) {v : α →ₛ M} :
    φ.Realize ((g : M →ₛ N) ∘ₛ v) ↔ φ.Realize v := by
  rw [Formula.Realize, Formula.Realize, ← realize_boundedFormula g φ, iff_eq_eq,
    Unique.eq_default ((g : M →ₛ N) <$>ₛ (default : M [^] ⦃⦄))]
include g

theorem realize_sentence (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize, Sentence.Realize, ← realize_formula g]
  refine Eq.to_iff ?_
  congr
  ext s a
  exact Empty.elim a

theorem theory_model [M ⊨ T] : N ⊨ T :=
  ⟨fun φ hφ => (realize_sentence g φ).1 (Theory.realize_sentence_of_mem T hφ)⟩

theorem elementarilyEquivalent : M ≅[L] N :=
  elementarilyEquivalent_iff.2 (realize_sentence g)

end StrongHomClass

namespace Relations

open BoundedFormula

variable {s : Sorts} {r : L.Relations (⦃s⦄ ⨯ ⦃s⦄)}

@[simp]
theorem realize_reflexive : M ⊨ r.reflexive ↔ Reflexive fun x y : M s => i.RelMap r ⟨x, y⟩ :=
  forall_congr' fun _ => realize_rel₂

@[simp]
theorem realize_irreflexive : M ⊨ r.irreflexive ↔ Std.Irrefl fun x y : M s => i.RelMap r ⟨x, y⟩ :=
  (forall_congr' fun _ => not_congr realize_rel₂).trans ⟨fun h => ⟨h⟩, fun h => h.irrefl⟩

@[simp]
theorem realize_symmetric : M ⊨ r.symmetric ↔ Symmetric fun x y : M s => i.RelMap r ⟨x, y⟩ := by
  rw [Relations.symmetric, Sentence.Realize, Formula.Realize]
  constructor
  · intro h a y a_1
    apply h
    simp_all only [PUnit.default_eq_unit, reduce_nil, realize_reindex, realize_rel₂,
      Signature.get_comap, Signature.SigMap.extend_right, Term.realize_prod, Term.realize_var]
    exact a_1
  · intro h a
    simp_all only [reindex, SigMap.extend_right, SigEquiv.symm, PUnit.default_eq_unit, reduce_nil,
      realize_all, realize_imp, realize_reindex, realize_rel₂, get_comap, FamMap.mk_apply,
      Term.realize_prod, Term.realize_var, sumElim_eval_r, coeFun_apply]
    intro a_1 a_2
    apply h
    simp_all only [reduce_nil]

@[simp]
theorem realize_antisymmetric :
    M ⊨ r.antisymmetric ↔ Std.Antisymm fun x y : M s => i.RelMap r ⟨x, y⟩ :=  by
  rw [Relations.antisymmetric, Sentence.Realize, Formula.Realize]
  constructor
  · intro h
    constructor
    intro a b hab hba
    apply h
    · simp_all only [PUnit.default_eq_unit, realize_reindex, realize_rel₂, get_comap,
        Term.realize_prod, Term.realize_var, sumElim_eval_r, coeFun_apply]
      exact hab
    · simp_all only [PUnit.default_eq_unit, realize_reindex, realize_rel₂, get_comap,
        Term.realize_prod, Term.realize_var, sumElim_eval_r, coeFun_apply]
      exact hba
  · intro h a
    simp_all only [PUnit.default_eq_unit, realize_reindex]
    intro b hba hab
    simp only [SigEquiv.nilLeft, SigMap.nil_left, SigMap.nil_left_inv]
    exact h.antisymm b a hba hab


@[simp]
theorem realize_transitive : M ⊨ r.transitive ↔ IsTrans _ fun x y : M s => i.RelMap r ⟨x, y⟩ := by
  rw [Relations.transitive, Sentence.Realize, Formula.Realize, isTrans_def]
  constructor
  · intro h a y a_1; apply h
  · intro h a
    simp_all only [PUnit.default_eq_unit, reduce_nil, realize_reindex]
    intro a_1 a_2
    apply h

@[simp]
theorem realize_total : M ⊨ r.total ↔ Std.Total fun x y : M s => i.RelMap r ⟨x, y⟩ := by
  rw [Relations.total, Sentence.Realize, Formula.Realize]
  constructor
  · intro h
    constructor
    intro a b
    simp only [Realize, Interpret, reduce_nil, PUnit.default_eq_unit, realize_reindex, realize_rel₂,
      Term.realize_prod, Term.realize_var] at h
    simp only [Interpret.get] at h
    tauto
  · intro h a
    simp only [Interpret, reduce_nil, PUnit.default_eq_unit, realize_reindex, Realize, realize_rel₂,
      Term.realize_prod, Term.realize_var, imp_false]
    simp only [Interpret.get]
    intro x h'
    let h'' := h.total x a
    tauto

end Relations

section Cardinality

variable (L)

open Signature Interpret

@[simp] lemma realize_distinct_from
  (v : α →ₛ M)
  (xs : (σ ⨯ ⦃s⦄).Interpret M)
  (hσ : OneSort s σ) :
  (BoundedFormula.distinct_from (L := L) (α := α) (s := s) (σ := σ) hσ).Realize v xs
    ↔
    ∀ v : σ.Idx s,
      -- “the i-th left variable value” ≠ “the new rightmost value”
      (xs.1.get s v) ≠ xs.2
      := by
  induction hσ with
  | nil =>
    simp only [BoundedFormula.distinct_from,
      BoundedFormula.realize_top, reduce_nil, PUnit.default_eq_unit, ne_eq, IsEmpty.forall_iff]
  | of =>
    simp only [BoundedFormula.distinct_from, Term.bdEqual, eq_mp_eq_cast, cast_eq, eq_mpr_eq_cast,
      BoundedFormula.realize_not, BoundedFormula.Realize, Term.realize_var, ne_eq]
    constructor
    · intro h w; cases w; exact h
    · intro h ; exact h (Idx.var)
  | @prod σ τ hσ hτ ihσ ihτ =>
    rcases xs with ⟨⟨x, y⟩ , z⟩
    simp only [BoundedFormula.distinct_from, BoundedFormula.realize_inf,
      BoundedFormula.realize_reindex, Interpret.get, ne_eq, ihσ, ihτ]
    constructor
    · intro ⟨hL, hR⟩ w
      cases w with
      | left wσ =>
        have hL' := hL wσ
        simp only [Interpret.comap, Interpret.fromGet, Interpret.get, SigMap.extend_right,
          SigMap.incl_left] at hL'
        simp_all only [ne_eq, Prod.forall, SigMap.extend_right, SigMap.incl_left_apply,
          SigMap.incl_right_apply,  FamMap.mk_apply, id_eq, fromGet_get, not_false_eq_true]
      | right wτ =>
        have hR' := hR wτ
        simp only [Interpret.comap, Interpret.fromGet, Interpret.get, SigMap.extend_right,
          SigMap.incl_right] at hR'
        simp_all only [ne_eq, Prod.forall, SigMap.extend_right, SigMap.incl_left_apply,
          SigMap.incl_right_apply, FamMap.mk_apply, id_eq, fromGet_get, not_false_eq_true]
    · intro h
      constructor
      · intro w
        have h' := h (.left w)
        simp only [Interpret.comap, Interpret.fromGet, Interpret.get, SigMap.extend_right,
          SigMap.incl_left]
        simp_all only [ne_eq, Prod.forall, FamMap.mk_apply, id_eq,
          SigMap.incl_left_apply, fromGet_get, not_false_eq_true]
      · intro w
        have h' := h (.right w)
        simp only [Interpret.comap, Interpret.fromGet, Interpret.get, SigMap.extend_right,
          SigMap.incl_right]
        simp_all only [ne_eq, Prod.forall, FamMap.mk_apply, id_eq, SigMap.incl_right_apply,
          fromGet_get, not_false_eq_true]

/-- Realization of `BoundedFormula.distinct`: the formula holds iff all the bound variables
    (interpreted as elements of `M s`) are pairwise distinct. -/
@[simp] lemma realize_distinct {n : ℕ}
  (v : α →ₛ M)
  (xs : (Signature.repeat n s).Interpret M) :
  (BoundedFormula.distinct (L := L) (α := α) s n).Realize v xs
    ↔
  Function.Injective (fun i : (Signature.repeat n s).Idx s => xs.get s i) := by
  induction n with
  | zero =>
    rw [BoundedFormula.distinct, BoundedFormula.realize_top, true_iff]
    intro i
    exact IsEmpty.elim (IdxNilEmpty (s := s)) i
  | succ n ih =>
    rw [BoundedFormula.distinct, BoundedFormula.realize_inf, BoundedFormula.realize_reindex]
    rw [FamMap.mk_apply, Interpret.comap]
    simp only [SigMap.incl_left]
    rw [ih]
    rcases xs with ⟨xs', x⟩
    simp only [Signature.repeat, realize_distinct_from L v (xs', x), fromGet_get, FamMap.mk_apply]
    constructor
    · intro ⟨hDistinct, hFresh⟩ i j hij
      cases i with
      | left iL =>
        cases j with
        | left jL =>
          congr
          apply hDistinct
          simp only
          congr
        | right jR =>
          cases jR
          have hFresh' : xs'.get s iL ≠ x := hFresh iL
          exact (hFresh' hij).elim
      | right iR =>
        cases j with
        | left jL =>
          cases iR
          have hFresh' : xs'.get s jL ≠ x := hFresh jL
          exact (hFresh' hij.symm).elim
        | right jR =>
          cases iR; cases jR; rfl
    · intro hInj
      refine ⟨?_, ?_⟩
      · intro i j hij
        have := @hInj (.left i) (.left j)
        simp only [Idx.left.injEq] at this
        exact this hij
      · intro i hEq
        have := @hInj (.left i) (.right .var) hEq
        simp only [reduceCtorEq] at this

@[simp]
theorem Sentence.realize_cardGe (n : Nat) : M ⊨ Sentence.cardGe L s n ↔ ↑n ≤ #(M s) := by
  rw [Sentence.cardGe, Sentence.Realize]
  apply Iff.intro
  · intro h
    rw[BoundedFormula.realize_exs] at h
    rcases h with ⟨x, hx⟩
    simp only [realize_distinct] at hx
    have hx': Function.Injective fun (i : (Signature.repeat n s).IdxFam s) => x.get s i := by
      exact hx
    have h_var_card: #((Signature.repeat n s).IdxFam s) = n := by
      let h := OneSort.mk_IdxFam_eq_length (σ := Signature.repeat n s) (s:= s) (oneSort_repeat s n)
      simp[IdxFam] at h
      simp_all only [mk_fintype]
    have h_lift := congr_arg Cardinal.lift.{w} h_var_card
    rw [Cardinal.lift_natCast] at h_lift
    apply Cardinal.lift_le.{z}.mp
    simp only [lift_natCast, ge_iff_le]
    rw[←h_lift]
    exact Cardinal.lift_mk_le_lift_mk_of_injective hx'
  · intro h
    let fin_inj : Fin n ↪ M s := by
      let hn :=congr_arg Cardinal.lift.{w} (Cardinal.mk_fin n)
      rw [Cardinal.lift_natCast] at hn
      rw [←hn, ← Cardinal.mk_uLift, Cardinal.le_def] at h
      let i:= Classical.choice h
      exact Equiv.ulift.symm.toEmbedding.trans i
    let varEquiv := OneSort.SigEquivFin (s:= s) (σ := Signature.repeat n s) (oneSort_repeat s n)
    rw[repeat_length] at varEquiv
    let h : (Signature.repeat n s).Idx s ≃ Fin n := by
          let h' := (OneSort.SigEquivFin (oneSort_repeat s n))
          rw[repeat_length n s ] at h'; exact h'
    let g := (OneSort.fibredMapEquiv (α := M) (oneSort_repeat s n)).symm
    let f : (Signature.repeat n s).Idx s ↪ M s:=
      h.toEmbedding.trans fin_inj
    let xs := Interpret.fromGet ((OneSort.fibredMapEquiv (oneSort_repeat s n)).symm f)
    rw[BoundedFormula.realize_exs]
    use xs
    simp only [realize_distinct]
    intro v w h
    simp only [OneSort.fibredMapEquiv, Equiv.coe_fn_symm_mk, fromGet_get, OneSort.extend, xs] at h
    rename_i h_2
    simp_all only [eq_mp_eq_cast, Function.Embedding.trans_apply, _root_.Equiv.coe_toEmbedding,
      Equiv.ulift_symm_apply, FamMap.mk_apply, EmbeddingLike.apply_eq_iff_eq, ULift.up.injEq, f,
      h_2, fin_inj]


@[simp]
theorem model_infiniteTheory_iff : M ⊨ L.infiniteTheory s ↔ Infinite (M s) := by
  simp only [infiniteTheory, Theory.model_iff, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, Sentence.realize_cardGe, infinite_iff, aleph0_le]

instance model_infiniteTheory [h : Infinite (M s)] : M ⊨ L.infiniteTheory s :=
  L.model_infiniteTheory_iff.2 h

@[simp]
theorem model_nonemptyTheory_iff : M ⊨ L.nonemptyTheory s ↔ Nonempty (M s):= by
  rw [nonemptyTheory, Theory.model_singleton_iff, Sentence.realize_cardGe, Nat.cast_one]
  exact Cardinal.one_le_iff_ne_zero.trans Cardinal.mk_ne_zero_iff

instance model_nonempty [h : Nonempty (M s)] : M ⊨ L.nonemptyTheory s :=
  L.model_nonemptyTheory_iff.2 h

theorem model_distinctConstantsAtSortTheory {M : Fam Sorts} [L[[α]].MSStructure M] (S : Set (α s)) :
    M ⊨ L.distinctConstantsAtSortTheory s S ↔ Set.InjOn (fun i : α s => (L.con s i : M s)) S := by
  simp only [distinctConstantsAtSortTheory, Theory.model_iff, Set.mem_image,
    Prod.exists, forall_exists_index, and_imp]
  refine ⟨fun h a as b bs ab => ?_, ?_⟩
  · contrapose! ab
    have h' := h _ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal,
      Term.realize_constants] at h'
    exact h'
  · rintro h φ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal, Term.realize_constants]
    exact fun contra => ab (h as bs contra)

theorem card_le_of_model_distinctConstantsAtSortTheory (S : Set (α s)) (M : Fam.{w} Sorts)
    [L[[α]].MSStructure M] [h : M ⊨ L.distinctConstantsAtSortTheory s S] :
     Cardinal.lift.{w} #S ≤ Cardinal.lift.{u'} #(M s) :=
  lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsAtSortTheory S).1 h)⟩⟩

theorem model_distinctConstantsTheory {M : Fam Sorts} [L[[α]].MSStructure M] (S : DepSet α) :
    M ⊨ L.distinctConstantsTheory S ↔
      ∀ t, Set.InjOn (fun i : α t => (L.con t i : M t)) (S t) := by
  constructor
  · intro h t
    have ht : M ⊨ L.distinctConstantsAtSortTheory t (S t) := by
      refine h.mono ?_
      intro φ hφ
      exact Set.mem_iUnion.mpr ⟨t, hφ⟩
    exact (L.model_distinctConstantsAtSortTheory (s := t) (M := M) (S := S t)).1 ht
  · intro h
    rw [Theory.model_iff]
    intro φ hφ
    rcases Set.mem_iUnion.mp hφ with ⟨t, hφt⟩
    have ht : M ⊨ L.distinctConstantsAtSortTheory t (S t) :=
      (L.model_distinctConstantsAtSortTheory (s := t) (M := M) (S := S t)).2 (h t)
    exact ht.realize_of_mem φ hφt

theorem card_le_of_model_distinctConstantsTheory (S : DepSet α) (M : Fam.{w} Sorts)
    [L[[α]].MSStructure M] [h : M ⊨ L.distinctConstantsTheory S] :
    Cardinal.lift.{max w z} #S ≤ Cardinal.lift.{max u' z} #(Σ t, M t) := by
  let f : S ↪ (Σ t, M t) := by
    refine ⟨fun x => ⟨x.1.1, (L.con x.1.1 x.1.2 : M x.1.1)⟩, ?_⟩
    intro x y hxy
    apply Subtype.ext
    rcases x with ⟨⟨sx, ax⟩, hx⟩
    rcases y with ⟨⟨sy, ay⟩, hy⟩
    change (⟨sx, ax⟩ : Sigma α) = ⟨sy, ay⟩
    have hs : sx = sy := by
      simpa using congrArg Sigma.fst hxy
    subst hs
    have hx' : ax ∈ S sx := by simpa [DepSet.mem_sigma] using hx
    have hy' : ay ∈ S sx := by simpa [DepSet.mem_sigma] using hy
    have hcon : (L.con sx ax : M sx) = (L.con sx ay : M sx) := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hxy
    have haxay : ax = ay :=
      ((L.model_distinctConstantsTheory (M := M) (S := S)).1 h sx) hx' hy' hcon
    simp only [haxay]
  exact Cardinal.lift_mk_le'.2 ⟨f⟩


end Cardinality


namespace ElementarilyEquivalent

@[symm]
nonrec theorem symm (h : M ≅[L] N) : N ≅[L] M :=
  h.symm

@[trans]
nonrec theorem trans (MN : M ≅[L] N) (NP : N ≅[L] P) : M ≅[L] P :=
  MN.trans NP

theorem completeTheory_eq (h : M ≅[L] N) : L.completeTheory M = L.completeTheory N :=
  h

theorem realize_sentence (h : M ≅[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  (elementarilyEquivalent_iff.1 h) φ

theorem theory_model_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T := by
  rw [Theory.model_iff_subset_completeTheory, Theory.model_iff_subset_completeTheory,
    h.completeTheory_eq]

theorem theory_model [MT : M ⊨ T] (h : M ≅[L] N) : N ⊨ T :=
  h.theory_model_iff.1 MT

theorem nonempty_iff (h : M ≅[L] N) : (∀ s, Nonempty (M s) ↔ Nonempty (N s)) := by
  intro s
  exact (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans
    (model_nonemptyTheory_iff L))

theorem nonempty [Mn : Nonempty (M s)] (h : M ≅[L] N) : Nonempty (N s) :=
  (h.nonempty_iff s).1 Mn

theorem infinite_iff (h : M ≅[L] N) : Infinite (M s) ↔ Infinite (N s) :=
  (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))

theorem infinite [Mi : Infinite (M s)] (h : M ≅[L] N) : Infinite (N s):=
  h.infinite_iff.1 Mi

end ElementarilyEquivalent

end MSLanguage


end MSFirstOrder
