import ProdExpr.Syntax

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

## References

For the Flypitch project:
- [J. Han, F. van Doorn, A formal proof of the independence of the continuum hypothesis]
  [flypitch_cpp]
- [J. Han, F. van Doorn, A formalization of forcing and the unprovability of
  the continuum hypothesis][flypitch_itp]
-/


universe u v w z u' v' w'

namespace Signature
open MSFirstOrder

end Signature

namespace MSFirstOrder

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
  {M : Sorts → Type w} {N P : Sorts → Type*}
  [i : L.MSStructure M] [L.MSStructure N] [L.MSStructure P]
  {α : Sorts → Type u'} {β : Sorts → Type v'} {γ : Sorts → Type*}
  {s : Sorts} {t : Sorts}
  {σ η τ : Signature Sorts}

namespace MSLanguage
open MSFirstOrder Cardinal

open MSStructure MSLanguage Fin Finsupp Fam Signature
open Interpret

namespace Term

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
def realize {σ : Signature Sorts} (v : α →ₛ M) : L.Term α σ → M[^]σ
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
theorem realize_var (v : α →ₛ M) (k) : realize v (var t k : L.Term α ⦃t⦄) = v t k := rfl

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
  simp only [varOf, realize_var]

@[simp] lemma realize_bind {σ : Signature Sorts}
  (v : β →ₛ M)
  (t : L.Term α σ)
  (f : ∀ s, α s → L.Term β ⦃s⦄) :
  (t.bind f).realize v =
  t.realize (fun s a => (f s a).realize v) :=  by
  induction t <;> simp_all only [bind, realize]

/-- Realize commutes with mapVars: -/
@[simp]
lemma realize_mapVars
    {α β : Sorts → Type u'} {σ : Signature Sorts}
    (f : α →ₛ β) (v : β →ₛ M) (t : Term L α σ) :
    realize v (mapVars f t) =
    realize (v ∘ₛ f) t := by
  induction t <;> simp_all [mapVars]

@[simp]
theorem realize_varterm {σ : Signature Sorts} (v : σ.Idx →ₛ M) :
  (varTerm σ).realize (L:= L) (M:= M) v  = fromGet v  := by
  induction σ with
  | nil => rfl
  | of s => rfl
  | prod σ₁ σ₂ ih₁ ih₂ =>
    rw [varTerm, realize_prod, realize_mapVars, realize_mapVars, ih₁, ih₂, fromGet]
    rfl

@[simp]
theorem realize_function_term {σ} (v : σ.Idx →ₛ M) (f : L.Functions σ t) :
    f.term.realize v = funMap f (fromGet v) := by
  induction σ with
  | nil => rfl
  | of s => rfl
  | prod σ τ ih₁ ih₂ => simp[Functions.term, realize_func]

open Signature

/-- Realizing a term at a reindexed tuple is equivalent to relabelling the term
  and then realizing at the original tuple.
-/
lemma realize_comap
    {σ τ ξ : Signature Sorts}
    (g : SigMap σ τ)
    (t : L.Term (α ⊕ₛ σ.Idx) ξ)
    (v : α →ₛ M)
    (xs : M [^] τ) :
  t.realize (Fam.sumElim v (xs.comap g))
    =
  (t.reindex g).realize (Fam.sumElim v xs) := by
  unfold Fam.sumElim reindex
  rw[realize_mapVars (M:= M) _ _ t]
  rw[Interpret.comap]
  have h:  (fun s ↦ Sum.elim (v s) fun w ↦ xs.get s (g s w))
          =(fun t ↦ Sum.elim (v t) (xs.get t) ∘ Sum.map id (g t)) := by
    ext s t
    rw[Function.comp_apply]
    cases t with
    | inl val => simp_all only [Sum.elim_inl, Sum.map_inl, id_eq]
    | inr val_1 => simp_all only [Sum.elim_inr, Sum.map_inr]
  simp[h]

@[simp]
theorem realize_constants {c : L.Constants t} {v : α →ₛ M} :  (c.term.realize v) = (c : M t) :=
  funMap_eq_coe_constants

/-- Renaming the left (named) variables in a term commutes with realization. -/
@[simp]
theorem realize_rename {β : Sorts → Type*} {γ : Signature Sorts} {σ : Signature Sorts}
    (t : L.Term (α ⊕ₛ γ.Idx) σ) (g : α →ₛ β) (v : β →ₛ M) (xs : γ.Interpret M) :
    (t.rename g).realize (Fam.sumElim v xs) =
    t.realize (Fam.sumElim (v ∘ₛ g) xs) := by
  simp only [rename, mapVars, realize_bind, realize_var]
  congr!
  rename_i x_1
  cases x_1 with
  | inl val => simp_all only [Sum.map_inl, Sum.elim_inl, Function.comp_apply]
  | inr val_1 => simp_all only [Sum.map_inr, id_eq, Sum.elim_inr]

@[simp] lemma realize_reindex
  (v : (α ⊕ₛ η.Idx) →ₛ M)
  (g : SigMap τ η)
  (t : L.Term (α ⊕ₛ τ.Idx) σ) :
  realize v (t.reindex g)
    =
  realize (Fam.sumElim (fun s a => v s (Sum.inl a))
                       (fun s x => v s (Sum.inr (g s x)))) t := by
  simp only [reindex, mapVars, realize_bind, realize_var]
  congr!
  rename_i x_1
  cases x_1 with
  | inl val => simp_all only [Sum.map_inl, id_eq, Sum.elim_inl]
  | inr val_1 => simp_all only [Sum.map_inr, Sum.elim_inr]

theorem realize_functions_apply₁ {f : L.Functions ⦃s⦄ t} {g : L.Term α ⦃s⦄} {v : α →ₛ M} :
    (f.apply₁ g).realize v = funMap f (g.realize v) := by rw [Functions.apply₁, Term.realize]

@[simp]
theorem realize_functions_apply₂ {s s₁ s₂ : Sorts}
    {f : L.Functions (⦃s₁⦄ ⨯ ⦃s₂⦄) s} {t₁ : L.Term₁ α s₁}
    {t₂ : L.Term₁ α s₂} {v : α →ₛ M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ⟨t₁.realize v, t₂.realize v⟩  := by
  rw [Functions.apply₂, Term.realize]
  simp_all only [realize_prod]


theorem realize_con {A : (s : Sorts) → Set (M s)} {s : Sorts} {a : A s}
    {v : α →ₛ M} : (L.con (α := M) s a).term.realize v = (a : M s) :=
  rfl


@[simp]
theorem realize_subst {β : Sorts → Type _} {σ τ : Signature Sorts}
    (t : L.Term (α ⊕ₛ σ.Idx) τ)
    (f : ∀ s, α s → L.Term (β ⊕ₛ σ.Idx) ⦃s⦄)
    (v : β →ₛ M)
    (xs : M [^] σ) :
    (t.subst f).realize (Fam.sumElim v xs) =
      t.realize (Fam.sumElim (fun s a => (f s a).realize (Fam.sumElim v xs)) xs) := by
  unfold subst
  simp only [realize_bind]
  congr!
  rename_i x_1
  cases x_1 with
  | inl val => simp_all only [Sum.elim_inl]
  | inr val_1 =>
    simp_all only [Sum.elim_inr]
    rfl

@[simp]
theorem realize_openVars {τ η σ : Signature Sorts}
    (t : L.Term (α ⊕ₛ (η.prod τ).Idx) σ)
    (v : α →ₛ M)
    (ys : M [^] τ)
    (xs : M [^] η) :
    (t.openVars).realize (Fam.sumElim (Fam.sumElim v ys) xs) =
      t.realize (Fam.sumElim v (⟨xs, ys⟩ : M[^](η.prod τ))) := by
  induction t with
  | nil => rfl
  | var s x =>
      cases x with
      | inl a => simp_all only [realize_var, Sum.elim_inl]; rfl
      | inr w =>
          cases w with
          | left w =>  simp [Term.openVars,Fam.sumElim, Interpret.get]
          | right w => simp [Term.openVars,Fam.sumElim, Interpret.get]
  | func g ts ih =>
      unfold Term.openVars at *
      simp only [bind, realize_func, realize, ih]
  | prod t₁ t₂ ih₁ ih₂ =>
      unfold Term.openVars at *
      simp only [bind, realize_prod, ih₁, ih₂]

open Interpret

@[simp]
theorem realize_getLeafTerm {σ : Signature Sorts}
    (t : L.Term α σ)
    (v : α →ₛ M)
    (s : Sorts)
    (w : σ.Idx s) :
    (t.getLeafTerm s w).realize v =
    (t.realize v).get s w := by
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
        simp only [getLeafTerm, ih₁, realize_prod]
        rfl
      | right w =>
        simp only [getLeafTerm, ih₂, realize_prod]
        rfl

@[simp]
theorem realize_instantiate {η ρ σ : Signature Sorts}
    (t : L.Term (α ⊕ₛ (σ.prod η).Idx) ρ)
    (u : L.Term (α ⊕ₛ σ.Idx) η)
    (v : α →ₛ M)
    (xs : M [^] σ) :
    (t.instantiate u).realize (Fam.sumElim v xs) =
      t.realize (Fam.sumElim v (⟨xs, u.realize (Fam.sumElim v xs)⟩ : M[^](σ.prod η))) := by
  induction t with
  | nil => rfl
  | var s x =>
      cases x with
      | inl a => simp_all only [realize_var, Sum.elim_inl]; rfl
      | inr w =>
          cases w with
          | left w =>
            simp [Term.instantiate, Term.bind, Fam.sumElim]
          | right w =>
              simp [Term.instantiate, Term.bind, Fam.sumElim, realize_getLeafTerm]
  | func g ts ih =>
      rw[instantiate] at *
      simp_all only [bind, realize_func]
  | prod t₁ t₂ ih₁ ih₂ =>
      rw[instantiate] at *
      simp_all only [bind, realize_prod]

theorem realize_restrictVar
  [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
  {σ : Signature Sorts} {t : L.Term α σ}
  (f : ∀ {s}, {x : α s // ⟨s, x⟩ ∈ Term.varFinset t} → β s)
  {v : β →ₛ M} (v' : α →ₛ M)
  (hv' :
    ∀ {s} (a : {x : α s // ⟨s, x⟩ ∈ Term.varFinset t}),
      v s (f a) = v' s a.1) :
  (t.restrictVar (β := β) f).realize v = t.realize v' := by
  induction t with
| var => apply @hv'
| func =>
   simp_all[realize, restrictVar]
| prod t₁ t₂ ih₁ ih₂ =>
  rw [realize_prod, restrictVar, realize,Prod.mk.injEq]
  rw [ih₁, ih₂]
  constructor
  · rfl
  · rfl
  · simp only [varFinset, hv', implies_true]
  · simp only [varFinset, hv', implies_true]
| nil => simp_all only [varFinset, Subtype.forall, Finset.notMem_empty, IsEmpty.forall_iff,
  implies_true, reduce_nil, PUnit.default_eq_unit]

/-- A special case of `realize_restrictVar`, included because we can add the `simp` attribute
to it -/
@[simp] theorem realize_restrictVar'
  [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
  {σ : Signature Sorts} {t : L.Term α σ}
  {S : ∀ s, Set (α s)}
  (h : ∀ {s} {x : α s}, ⟨s, x⟩ ∈ Term.varFinset t → x ∈ S s)
  {v : α →ₛ M} :
  (t.restrictVar (β := fun s => {x : α s // x ∈ S s})
      (fun {_} a => ⟨a.1, h a.2⟩)
    ).realize
      (fun s x => v s x.1)
  =
  t.realize v := by simp only [Subtype.forall, realize_restrictVar]

theorem realize_restrictVarLeft
  [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
  {σ : Signature Sorts} {γ : Sorts → Type*}
  {t : L.Term (α ⊕ₛ γ) σ}
  (f : ∀ {s}, {x : α s // ⟨s, x⟩ ∈ Term.varFinsetLeft t} → β s)
  {xs : (β ⊕ₛ γ) →ₛ M}
  (xs' : α →ₛ M)
  (hxs' :
    ∀ {s} (a : {x : α s // ⟨s, x⟩ ∈ Term.varFinsetLeft t}),
      xs s (Sum.inl (f a)) = xs' s a.1) :
  (t.restrictVarLeft (β := β) (γ := γ) f).realize xs
    =
  t.realize (Fam.sumElim xs' (fun s g => xs s (Sum.inr g))) := by
induction t with
| var =>
  rename_i a
  simp_all only [Subtype.forall, realize_var]
  cases a with
  | inl val => apply hxs'
  | inr
    val_1 =>
    simp_all only [varFinsetLeft, Finset.notMem_empty, varFinsetLeft.eq_2,
      IsEmpty.forall_iff, implies_true, Sum.elim_inr]
    rfl
| func =>
   simp_all[realize, restrictVarLeft]
| @prod σ₁ σ₂ t₁ t₂ ih₁ ih₂ =>
  simp only [realize_prod, restrictVarLeft]
  rw [ih₁, ih₂] <;> simp only [varFinsetLeft, hxs', implies_true]
| nil => simp_all only [varFinsetLeft, Subtype.forall, Finset.notMem_empty,
  IsEmpty.forall_iff, implies_true, reduce_nil,  PUnit.default_eq_unit]


/-- A special case of `realize_restrictVarLeft`, included because we can add the `simp` attribute
to it -/
@[simp] theorem realize_restrictVarLeft'
  [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
  {σ : Signature Sorts} {γ : Sorts → Type*}
  {t : L.Term (α ⊕ₛ γ) σ}
  {S : ∀ s, Set (α s)}
  (h : ∀ {s} {x : α s}, ⟨s, x⟩ ∈ Term.varFinsetLeft t → x ∈ S s)
  {v : α →ₛ M} {xs : γ →ₛ M} :
  (t.restrictVarLeft
      (β := fun s => {x : α s // x ∈ S s})
      (γ := γ)
      (fun {_} a => ⟨a.1, h a.2⟩)
    ).realize
      (Fam.sumElim (fun s x => v s x.1) xs)
    =
  t.realize (Fam.sumElim v xs) := by
  simp only [Sum.elim_inl, Subtype.forall, realize_restrictVarLeft, Sum.elim_inr]


@[simp]
theorem realize_constantsToVars
  [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
  {σ : Signature Sorts} {t : L[[α]].Term β σ} {v : β →ₛ M} :
  t.constantsToVars.realize
      (Fam.sumElim (fun s a => (L.con (s := s) a : M s)) v)
    =
  t.realize v := by
  induction t with
  | nil => simp
  | var => simp
  | @func σ s f t ih  =>
    cases f
    case inl v =>
      simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
      rw [withConstants_funMap_sumInl]
    case inr v =>
      cases σ
      case nil =>
        simp_all only [reduce_nil, PUnit.default_eq_unit,
          constantsToVars, realize_var, Sum.elim_inl,
          constantsOn_Functions, constantsOnFunc,
          realize_func]
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
  t.realize (Fam.sumElim (fun s a => (L.con (s := s) a : M s)) v) := by
  induction t with
  | nil =>
      simp [Term.realize, Term.varsToConstants]
  | prod t₁ t₂ ih₁ ih₂ =>
      simp [Term.realize, Term.varsToConstants, ih₁, ih₂]
  | var s ab =>
      -- ab : (α ⊕ₛ β) s  i.e. Sum (α s) (β s)
      cases ab with
      | inl a =>
          simp [Term.varsToConstants, Term.realize, Fam.sumElim]
          rfl
      | inr b =>
          simp [Term.varsToConstants, Term.realize, Fam.sumElim]
  | @func σ' s f ts ih =>
      simp only [Term.realize, Term.varsToConstants, ih]
      rw [withConstants_funMap_sumInl]

theorem realize_constantsVarsEquivLeft
  [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
  {σ τ : Signature Sorts}
  {t : L[[α]].Term (β ⊕ₛ σ.Idx) τ} {v : β →ₛ M} {xs : M [^] σ} :
  (constantsVarsEquivLeft t).realize
      (Fam.sumElim
        (Fam.sumElim (fun s a => (L.con (s := s) a : M s)) v)
        (xs.get))
    =
  t.realize (Fam.sumElim v (xs.get)) := by
  simp only [constantsVarsEquivLeft, Equiv.trans_apply, constantsVarsEquiv_apply,
    mapVarsEquiv_symm_apply, mapVars, realize_bind, realize_var]
  refine _root_.trans ?_ (realize_constantsToVars (t := t) (v := (Fam.sumElim v (xs.get))))
  rcongr s v s' x
  -- v : ((α ⊕ₛ β) ⊕ₛ σ.Idx) s, so split into the three cases
  cases x with
  | inl ab =>
      simp_all only [Sum.elim_inl]
      rfl
  | inr w =>
      simp_all only [Sum.elim_inr]
      cases w with
      | inl val =>
        simp_all only [Sum.elim_inl]
        rfl
      | inr val_1 =>
        simp_all only [Sum.elim_inr]
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
theorem HomClass.realize_term {F : Type*} [DFunLike F Sorts (fun t => M t → N t)] [HomClass L F M N]
    (g : F) {t : L.Term α σ} {v : α →ₛ M} :
    t.realize (g ∘ₛ v) = g <$>ₛ (t.realize v) := by
  induction t with
  | nil => rfl
  | var => rfl
  | func _ _ ih =>
    rw [Term.realize, ih, Term.realize, Interpret.map, HomClass.map_fun]
  | prod _ _ ih₁ ih₂ => simp only [Term.realize_prod, ih₁, ih₂, Interpret.map]
namespace BoundedFormula

open Term Interpret
/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def Realize : ∀ {ξ} (_φ : L.BoundedFormula α ξ) (_v : α →ₛ M) (_xs : ξ.Interpret M), Prop
  | _, falsum, _v, _xs => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Fam.sumElim v xs)
      = t₂.realize (Fam.sumElim v xs)
  | _, rel R ts, v, xs => RelMap R (ts.realize (Fam.sumElim v xs))
  | _, imp φ₁ φ₂, v, xs => Realize φ₁ v xs → Realize φ₂ v xs
  | _, all σ φ, v, xs => ∀ x : M[^]σ, Realize φ v ⟨xs, x⟩

variable {ξ η : Signature Sorts} {φ ψ : L.BoundedFormula α ξ} {θ : L.BoundedFormula α (ξ.prod η)}
variable {v : α →ₛ M} {xs : ξ.Interpret M}

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormula α ξ).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_not : φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_bdEqual (t₁ t₂ : L.Term (α ⊕ₛ ξ.Idx) σ) :
    (t₁.bdEqual t₂).Realize v xs ↔ t₁.realize (Fam.sumElim v xs) = t₂.realize (Fam.sumElim v xs) :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormula α ξ).Realize v xs ↔ True := by simp [Top.top]

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp [Realize]

@[simp]
theorem realize_foldr_inf {σ} (l : List (L.BoundedFormula α σ))
    (v : famMap α M) (xs : M [^] σ) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ ∀ φ ∈ l, φ.Realize v xs := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs := by
  simp only [Realize]

/-- List.foldr on BoundedFormula.imp gives a big "And" of input conditions. -/
theorem realize_foldr_imp {η : Signature Sorts} (l : List (L.BoundedFormula α η))
    (f : L.BoundedFormula α η) :
    ∀ (v : famMap α M) xs,
      (l.foldr BoundedFormula.imp f).Realize v xs =
      ((∀ i ∈ l, i.Realize v xs) → f.Realize v xs) := by
  intro v xs
  induction l
  next => simp
  next f' _ _ => by_cases f'.Realize v xs <;> simp [*]

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
theorem realize_foldr_sup (l : List (L.BoundedFormula α σ))
    (v : famMap α M) (xs : M [^] σ) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp
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
theorem realize_rename {β : Sorts → Type*} {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (f : α →ₛ β)
    (v : β →ₛ M)
    (xs : M [^] σ) :
    (φ.rename f).Realize v xs ↔ φ.Realize (v ∘ₛ f) xs := by
  induction φ with
  | falsum =>
      simp [BoundedFormula.rename, BoundedFormula.mapTermRel]
      rfl
  | equal t₁ t₂ =>
    simp[Realize, rename, mapTermRel]
  | rel R ts =>
      simp [BoundedFormula.rename, BoundedFormula.mapTermRel, Realize]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [rename, mapTermRel, realize_imp, Realize] at *
      simp only [ih₁ xs, ih₂ xs]
  | all η φ ih =>
      simp only [rename, mapTermRel, realize_all] at *
      simp only [ih]

open Signature SigEquiv Interpret

/-- Realization commutes with substitution of free variables by terms. -/
@[simp]
theorem realize_subst {β : Sorts → Type*} {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (f : ∀ s, α s → L.Term (β ⊕ₛ σ.Idx) ⦃s⦄)
    (v : β →ₛ M)
    (xs : M [^] σ) :
    (φ.subst f).Realize v xs ↔
      φ.Realize (fun s a => (f s a).realize (Fam.sumElim v xs)) xs := by
  induction φ with
  | falsum => simp [BoundedFormula.subst, Realize]
  | equal t₁ t₂ =>
      simp only [BoundedFormula.subst, Realize, Term.realize_subst]
  | rel R ts =>
      simp only [BoundedFormula.subst, Realize, Term.realize_subst]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [BoundedFormula.subst, realize_imp]
      rw [ih₁, ih₂]
  | @all σ' τ φ ih =>
      simp only [BoundedFormula.subst, realize_all]
      -- f' s a = (f s a).reindex incl_left has type Term (β ⊕ₛ (σ'.prod τ).Idx) ⦃s⦄
      -- ih : (φ.subst f').Realize v xs' ↔
      --   φ.Realize (fun s a => (f' s a).realize (sumElim v xs')) xs'
      -- for xs' : (σ'.prod τ).Interpret M
      -- We need: reindexed term at (xs, x) equals original term at xs
      have hval : ∀ (x : M[^]τ),
        (fun s a => ((f s a).reindex SigMap.incl_left).realize
            (Fam.sumElim v (Interpret.get (⟨xs , x⟩ : (σ'.prod τ).Interpret M) ))) =
          (fun s a => (f s a).realize (Fam.sumElim v xs)) := by
        intro x
        funext s a
        simp only [Term.reindex, Term.realize_mapVars]
        congr 1
        funext s' b
        cases b with
        | inl b' => simp [Fam.sumElim]
        | inr w =>
            simp only [Fam.sumElim, Function.comp_apply, Interpret.get]
            rfl
      refine forall_congr' (fun x => ?_)
      rw [ih, hval]

@[simp]
lemma comap_extend_right {x : M [^] η}
    (g : SigMap σ ξ) : Interpret.comap g.extend_right (xs, x) = (xs.comap g, x) := by
    have hget :
      Interpret.get (Interpret.comap  g.extend_right (xs, x))
        = fun s v =>
            match v with
            | Idx.left  wσ => xs.get s (g s wσ)
            | Idx.right wη => x.get s wη := by
          funext s v
          cases v with
          | left wσ =>
            rw[get_comap]; unfold SigMap.extend_right; simp[Interpret.get]
          | right wη =>
            rw[get_comap]; unfold SigMap.extend_right; simp[Interpret.get]
    have hget_rhs :
      Interpret.get (xs.comap g, x)
        = fun s (v : (σ.prod η).Idx s) =>
            match v with
            | .left w => xs.get s (g s w)
            | .right w => x.get s w := by
      funext s v
      cases v with
      | left wσ =>
          simp [Interpret.comap, Interpret.get]
      | right wη =>
          simp [Interpret.get]
    have h :
    Interpret.get (Interpret.comap g.extend_right (xs, x))
      = Interpret.get (xs.comap g, x) := by
        funext s v; rw[hget, hget_rhs];
    have h':= congrArg (Interpret.fromGet (S := Sorts) (α := M) (σ := σ.prod η)) h
    rw[get_fromGet] at h'
    simp[h']


@[simp]
lemma comap_block_swap
    {σ τ η : Signature Sorts}
    (xs : M [^] σ) (ys : M [^] τ) (zs : M [^] η) :
    Interpret.comap (@block_swap _ σ τ η)
        (⟨⟨xs, zs⟩, ys⟩ : ((σ ⨯ η) ⨯ τ).Interpret M)
      = (⟨⟨xs, ys⟩, zs⟩ : ((σ.prod τ).prod η).Interpret M) := by
  -- Prove by extensionality on `Interpret.get` and then rebuild with `fromGet`.
  have hget :
      Interpret.get
          (Interpret.comap (@block_swap _ σ τ η)
            (⟨⟨xs, zs⟩, ys⟩ : ((σ ⨯ η) ⨯ τ).Interpret M))
        =
      Interpret.get (⟨⟨xs, ys⟩, zs⟩ : ((σ.prod τ).prod η).Interpret M) := by
    funext s v
    -- `get_comap` reduces this to computing `block_swap` on variables.
    rw [get_comap]
    -- Now unfold `block_swap` and split by the variable position.
    unfold block_swap
    cases v with
    | left vστ =>
        cases vστ with
        | left wσ =>
            simp [Interpret.get]
            rfl
        | right wτ =>
            simp [Interpret.get]
            rfl
    | right wη =>
        simp [Interpret.get]; rfl
  have h' :=
      congrArg (Interpret.fromGet (S := Sorts) (α := M) (σ := (σ.prod τ).prod η)) hget
  -- `fromGet` is inverse to `get`.
  rw [get_fromGet] at h'
  simpa using h'

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
      simp [BoundedFormula.reindex, BoundedFormula.Realize]
  | equal t₁ t₂ =>
      intro τ g xs
      -- Term.realize_comap is your commuting lemma
      rw[reindex, Realize, Realize, ←Term.realize_comap, ←Term.realize_comap]
  | rel R ts =>
      intro τ g xs
      rw[reindex, Realize, Realize, ←Term.realize_comap]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      intro τ g xs
      simp [BoundedFormula.reindex, BoundedFormula.Realize, ih₁, ih₂]
  | all η ψ ih =>
      intro τ g xs
      -- After simp, goal becomes a ∀x statement. IH applies to ψ with g.extend_right.
      -- comap_extend_right rewrites comap along extend_right on (xs, x).
      simp [BoundedFormula.reindex, BoundedFormula.Realize, ih,
        comap_extend_right (g := g) (xs := xs)]

/-- Realization commutes with `relabel`: relabeling free variables `α` to `β ⊕ τ.Idx`
and then evaluating is equivalent to evaluating with the relabeled variable assignment. -/
@[simp]
theorem realize_relabel {β : Sorts → Type*} {τ σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (g : α →ₛ β ⊕ₛ τ.Idx)
    (v : β →ₛ M)
    (ys : M [^] τ)
    (xs : M [^] σ) :
    (φ.relabel g).Realize v (⟨ys, xs⟩ : (τ.prod σ).Interpret M) ↔
      φ.Realize (fun s a => Fam.sumElim v ys s (g s a)) xs := by
  rw [relabel]
  simp only [realize_subst, realize_rename, realize_reindex]
  congrm φ.Realize ?_ ?_
  · ext s x
    let zs : β s ⊕ τ.Idx s := g s x
    change realize (Fam.sumElim v (Interpret.get (ys, xs)))
      (Fam.sumElim (varOf inl) (fun s v ↦ var s (Sum.inr v.left)) s zs) =
      Fam.sumElim v (ys.get) s zs
    cases zs
    · simp_all only [Sum.elim_inl, realize_varOf]
      rfl
    · simp_all only [Sum.elim_inr, realize_var]
      rfl
  · ext s v_1 : 1
    simp_all only [get_comap]
    rfl

theorem realize_openVars_aux
    (n : ℕ)
    {α : Sorts → Type u'}
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
      cases φ <;> simp [BoundedFormula.size] at hn
  | succ n ih =>
      cases φ with
      | falsum => simp [BoundedFormula.openVars, Realize]
      | equal t₁ t₂ =>
          simp [BoundedFormula.openVars, Realize, Term.realize_openVars]
      | rel R ts =>
          simp [BoundedFormula.openVars, Realize, Term.realize_openVars]
      | imp φ₁ φ₂ =>
          simp only [BoundedFormula.openVars, realize_imp, Realize]
          have h₁ := ih φ₁ (by simp [BoundedFormula.size] at hn ⊢; omega) v ys xs
          have h₂ := ih φ₂ (by simp [BoundedFormula.size] at hn ⊢; omega) v ys xs
          simp only [h₁, h₂]
      | all η ψ =>
          -- ψ : BoundedFormula α ((σ.prod τ).prod η)
          -- Reindex by block_swap so that τ is the right block, then openVars, then quantify η.
          simp only [BoundedFormula.openVars, realize_all, Realize]
          refine forall_congr' (fun x => ?_)
          -- x : M[^]η
          have hsize : (ψ.reindex (@block_swap _ σ τ η)).size ≤ n := by
            rw [reindex_size]; simp [BoundedFormula.size] at hn ⊢; omega
          have hrec := ih (ψ.reindex (@block_swap _ σ τ η)) hsize v ys (xs, x)
          calc
            (((ψ.reindex (@block_swap _ σ τ η)).openVars).Realize (Fam.sumElim v ys)
                (⟨xs, x⟩ : M[^](σ.prod η)))
                ↔ ((ψ.reindex (@block_swap _ σ τ η)).Realize v
                    (⟨⟨xs, x⟩, ys⟩ : M[^]((σ ⨯ η) ⨯ τ))) := hrec
            _ ↔ ψ.Realize v
                  (Interpret.comap (@block_swap _ σ τ η)
                    (⟨⟨xs, x⟩, ys⟩ : M[^]((σ ⨯ η) ⨯ τ))) := by
                  simp
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
theorem realize_closeVars {σ τ : Signature Sorts} {X : Sorts → Type*}
    (f : X →ₛ τ.Idx)
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
  simp_all only [get_comap, Function.comp_apply]
  rfl

/-- Realization commutes with `instantiate`: instantiating a term `t` for the rightmost
bound variables and then realizing is equivalent to realizing with `t.realize` substituted. -/
@[simp]
theorem realize_instantiate {σ τ : Signature Sorts}
    (φ : L.BoundedFormula α (σ.prod τ))
    (t : L.Term (α ⊕ₛ σ.Idx) τ)
    (v : α →ₛ M)
    (xs : M [^] σ) :
    (φ.instantiate t).Realize v xs ↔
      φ.Realize v (⟨xs, t.realize (Fam.sumElim v xs)⟩ : (σ.prod τ).Interpret M) := by
  let ys : M[^]τ := t.realize (Fam.sumElim v xs)
  let f := fun s a ↦
      realize (Fam.sumElim v (xs.get))
              (Fam.sumElim (varOf inl) (fun s a ↦ t.getLeafTerm s a) s a)
  have hv :
    f
    =
    Fam.sumElim v ys := by
    funext s a
    cases a with
    | inl a =>
        simp [ys, Fam.sumElim, f, varOf, Fam.inl]
    | inr w =>
        simp [f, ys, Fam.sumElim, Term.realize_getLeafTerm]
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

theorem realize_comap_of_eq {ξ σ : Signature Sorts} (h : ξ = σ)
    {h' : ξ ≤ σ} {φ : L.BoundedFormula α ξ}
    --note: annoying bit of coercion happens here to go from ξ = σ to ∀ s, ξ s = σ s
    {v : α →ₛ M} {xs : M[^]σ} :

    (φ.reindex h').Realize v xs
     ↔
    φ.Realize v (fun s => (xs s) ∘ Fin.cast (congr_fun (congr_arg DFunLike.coe h) s)) := by

  subst h
  simp only [reindex_rfl, cast_refl, Function.comp_id]

-/

theorem realize_mapTermRel_id [L'.MSStructure M] {φ : L.BoundedFormula α σ}
    (ft : ∀ σ ξ : Signature Sorts, L.Term (α ⊕ₛ σ.Idx) ξ →  L'.Term (β ⊕ₛ σ.Idx) ξ)
    (fr : ∀ σ, L.Relations σ → L'.Relations σ)
    {v' : β →ₛ M} {xs : M[^]σ}
    (h1 :
      ∀ (σ: Signature Sorts) (τ) (t : L.Term (α ⊕ₛ σ.Idx) τ) (xs : M[^]σ),
        (ft σ τ t).realize (Fam.sumElim v' xs) =
        t.realize (Fam.sumElim v xs))
    (h2 : ∀ (σ) (R : L.Relations σ) (x : M[^]σ), RelMap (fr σ R) x = RelMap R x) :
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
  | falsum => simp [restrictFreeVar, Realize]
  | @equal σ τ t₁ t₂ =>
    simp only [restrictFreeVar, Realize]
    -- For terms, we use realize_restrictVarLeft
    -- Need to show both sides equal
    have h1 : (t₁.restrictVarLeft fun {t} x => f t ⟨x.1, Finset.mem_union.mpr (Or.inl x.2)⟩).realize
        (Fam.sumElim v xs) =
        t₁.realize (Fam.sumElim v' xs) := by
      rw [realize_restrictVarLeft]
      · congr 1
      · intro s ⟨a, ha⟩
        simp only [Fam.sumElim, Sum.elim_inl]
        exact hv s a (Finset.mem_union.mpr (Or.inl ha))
    have h2 : (t₂.restrictVarLeft fun {t} x => f t ⟨x.1, Finset.mem_union.mpr (Or.inr x.2)⟩).realize
        (Fam.sumElim v xs) =
        t₂.realize (Fam.sumElim v' xs) := by
      rw [realize_restrictVarLeft]
      · congr 1
      · intro s ⟨a, ha⟩
        simp only [Fam.sumElim, Sum.elim_inl]
        exact hv s a (Finset.mem_union.mpr (Or.inr ha))
    rw [h1, h2]
  | @rel σ τ R ts =>
    simp only [restrictFreeVar, Realize]
    congr!
    apply Interpret.ext
    intro s i
    rw [realize_restrictVarLeft]
    · simp_all only [freeVarFinset, freeVarFinset.eq_3, Sum.elim_inr]
      rfl
    · intro s_1 a
      simp_all only [freeVarFinset, Sum.elim_inl]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [restrictFreeVar, realize_imp]
    let f₁ : φ₁.freeVarType →ₛ β := fun t x => f t ⟨x.1, Finset.mem_union.mpr (Or.inl x.2)⟩
    let f₂ : φ₂.freeVarType →ₛ β := fun t x => f t ⟨x.1, Finset.mem_union.mpr (Or.inr x.2)⟩
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
    (φ.restrictFreeVar (fun _ x => x.1)).Realize v xs ↔ φ.Realize v xs := by
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
      L.Term (α ⊕ₛ τ.Idx) ξ →
        L'.Term (β ⊕ₛ (σ.prod τ).Idx) ξ}

  {fr : ∀ τ : Signature Sorts, L.Relations τ → L'.Relations τ}
  {φ : L.BoundedFormula α τ}

  (v : ∀ {τ}, (σ.prod τ).Interpret M → α →ₛ M)
  {v' : β →ₛ M}

  (xs : (σ.prod τ).Interpret M)

  (h1 :
    ∀ (τ ξ) (t : L.Term (α ⊕ₛ τ.Idx) ξ) (xs' : (σ.prod τ).Interpret M),
      (ft τ ξ t).realize (Fam.sumElim v' (xs.get')) =
        t.realize (Fam.sumElim (v xs') (xs.get' ∘ₛ incl_right)))

  (h2 :
    ∀ (τ) (R : L.Relations τ) (x : M[^]τ),
      RelMap (fr τ R) x = RelMap R x)

  (hv :
    ∀ (τ η) (xs : (σ.prod τ).Interpret M) (x : M[^]η),
      @v (τ.prod η)
        (interpretEquiv M (PEquiv.assocL σ _ _)
          ((xs, x) : ((σ.prod τ).prod η).Interpret M)) = v xs) :

  (φ.mapTermRel ft fr (fun τ₀ η => reindex (L := L') (α := β) (SigMap.assocR σ τ₀ η))).Realize v' xs
    ↔
    φ.Realize (v xs) (fromGet (xs.get ∘ₛ incl_right (σ := τ))) := by
  induction φ with
  | falsum =>
      rfl
  | equal t₁ t₂ =>
      simp [mapTermRel, Realize, h1]
  | rel =>
      simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih₁ ih₂ =>
      simp [mapTermRel, Realize, ih₁, ih₂]
  | all η f ih =>

      sorry

-/




namespace LHom

open BoundedFormula

@[simp]
theorem realize_onBoundedFormula [L'.MSStructure M] (φ : L →ᴸ L')
    [φ.IsExpansionOn M] {σ : Signature Sorts}
    (ψ : L.BoundedFormula α σ) {v : α →ₛ M} {xs : M [^] σ} :
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

nonrec def Realize (φ : L.Formula α) (v : famMap α M) : Prop :=
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
  simp_all only [PUnit.default_eq_unit, reduce_nil, Term.mapVars, Term.realize_bind,
                    Term.realize_var, Sum.elim_inl]

@[simp]
theorem realize_rel₁ {R : L.Relations ⦃s⦄} {t : L.Term α ⦃s⦄} :
    (R.formula₁ t).Realize v ↔ RelMap R (t.realize v) := by
  rw [Relations.formula₁, realize_rel, iff_eq_eq]


@[simp]
theorem realize_rel₂ {s₁ s₂} {R : L.Relations (⦃s₁⦄ ⨯ ⦃s₂⦄)}
    {t₁ : L.Term₁ α s₁} {t₂ : L.Term α ⦃s₂⦄} :
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
theorem realize_ex_root {α : Sorts → Type u'} {φ : L.BoundedFormula α (⦃⦄ ⨯ ⦃s⦄)}
    {M : Sorts → Type w} {v : α →ₛ M} [L.MSStructure M] :
    (Formula.Realize (BoundedFormula.ex ⦃s⦄ φ)) v ↔
    ∃ (x : M s), BoundedFormula.Realize φ v ⟨default, x⟩   := by
  simp only [Formula.Realize, BoundedFormula.ex, PUnit.default_eq_unit, Interpret.reduce_nil,
    BoundedFormula.realize_not, BoundedFormula.realize_all, not_forall, not_not]


@[simp]
theorem realize_all_root {α : Sorts → Type u'} {φ : L.BoundedFormula α (⦃⦄ ⨯ ⦃s⦄)}
    {M : Sorts → Type w} {v : α →ₛ M} [L.MSStructure M] :
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

theorem realize_relabel_sumInr (φ : L.Formula (Fin n)) {v : Empty → M} {x : M[^]σ} :
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
  simp_all only [PUnit.default_eq_unit, reduce_nil, Term.mapVars,
    Term.realize_bind, Term.realize_var, Sum.elim_inl]

/-- Realization of `Formula.graph`: the graph of a function symbol relates inputs to output.
The valuation `v` assigns values to the variables of type `(σ.prod (of s)).Idx`, which
represent both the input variables (from `σ`) and the output variable (from `of s`). -/
@[simp]
theorem realize_graph {f : L.Functions σ s} {v : (σ ⨯ ⦃s⦄).Idx →ₛ M} :
    (Formula.graph f).Realize v ↔
      v s (.right .var) = funMap f (fromGet (fun t w => v t (.left w))) := by
  rw [Formula.graph, realize_equal]
  simp only [Term.realize_var, Term.realize_func,
    Term.realize_mapVars, Term.realize_varterm]
  rfl

theorem boundedFormula_realize_eq_realize (φ : L.Formula α)
    (v : α →ₛ M) (ys : Signature.nil.Interpret M) :
    BoundedFormula.Realize φ v ys ↔ φ.Realize v := by
  rw [Formula.Realize, iff_iff_eq, Unique.eq_default ys]

open BoundedFormula

@[simp]
theorem realize_fully_instantiate {τ : Signature Sorts}
    (φ : L.BoundedFormula α τ)
    (t : L.Term (α ⊕ₛ Signature.nil.Idx) τ)
    (v : α →ₛ M) :
    (φ.fully_instantiate t).Realize v ↔
      φ.Realize v (t.realize (Fam.sumElim v (default : M[^]Signature.nil))) := by
  unfold fully_instantiate Formula.Realize
  rw[realize_instantiate, PUnit.default_eq_unit, realize_reindex]
  congr!; ext; simp_all only [reduce_nil, get_comap]; rfl

end Formula

@[simp]
theorem LHom.realize_onFormula [L'.MSStructure M] (φ : L →ᴸ L')
    [φ.IsExpansionOn M] (ψ : L.Formula α)
    {v : α →ₛ M} :
    (φ.onFormula ψ).Realize v ↔ ψ.Realize v :=
  φ.realize_onBoundedFormula ψ

@[simp]
theorem LHom.setOf_realize_onFormula [L'.MSStructure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Formula α) : (setOf (φ.onFormula ψ).Realize : Set (famMap α M)) = setOf ψ.Realize := by
  ext
  simp

variable (M)

/-- A sentence can be evaluated as true or false in a MSStructure. -/
nonrec def Sentence.Realize (φ : L.Sentence) : Prop :=
  φ.Realize (fun s a => (Empty.elim a : M s))

-- input using \|= or \vDash, but not using \models
@[inherit_doc Sentence.Realize]
infixl:51 " ⊨ " => Sentence.Realize

@[simp]
theorem Sentence.realize_not {φ : L.Sentence} : M ⊨ φ.not ↔ ¬M ⊨ φ :=
  Iff.rfl

@[simp]
theorem Sentence.realize_bot : M ⊨ (⊥ : L.Sentence) ↔ False :=
  Iff.rfl

@[simp]
theorem Sentence.realize_top : M ⊨ (⊤ : L.Sentence) ↔ True := by
  -- Unfold Sentence.Realize -> Formula.Realize -> BoundedFormula.Realize
  simp [Sentence.Realize, Formula.Realize, BoundedFormula.realize_top]

@[simp]
theorem Sentence.realize_inf {φ ψ : L.Sentence} : M ⊨ φ ⊓ ψ ↔ M ⊨ φ ∧ M ⊨ ψ := by
  simp [Sentence.Realize, Formula.Realize, BoundedFormula.realize_inf]

@[simp]
theorem Sentence.realize_sup {φ ψ : L.Sentence} : M ⊨ φ ⊔ ψ ↔ M ⊨ φ ∨ M ⊨ ψ := by
  simp [Sentence.Realize, Formula.Realize, BoundedFormula.realize_sup]

@[simp]
theorem Sentence.realize_imp {φ ψ : L.Sentence} : M ⊨ (φ ⟹ ψ) ↔ (M ⊨ φ → M ⊨ ψ) := by
  simp [Sentence.Realize, Formula.Realize, BoundedFormula.realize_imp]

@[simp]
theorem Sentence.realize_iff {φ ψ : L.Sentence} : M ⊨ (φ ⇔ ψ) ↔ (M ⊨ φ ↔ M ⊨ ψ) := by
  simp [Sentence.Realize, Formula.Realize, BoundedFormula.realize_iff]

section localize_formula

namespace BoundedFormula.LocalForm

variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
variable {σ : Signature Sorts} {φ : L.BoundedFormula α σ} (lf : φ.LocalForm)

/-- Pull a valuation back through the localization equivalence. -/
noncomputable def comap (M) (v : α →ₛ M) :
    lf.τ.Idx →ₛ M :=
    fun s i => v s ((lf.e.invFun s i).1)

/-- Build a tuple from a valuation, for use with `toBoundedFormula`.
Only for `Formula` (σ = nil). -/
noncomputable def toTuple {φ : L.Formula α} (lf : φ.LocalForm) (M) (v : α →ₛ M) :
    M[^]lf.τ :=
    fromGet (lf.comap M v)

@[simp] lemma get_toTuple {φ : L.Formula α} (lf : φ.LocalForm) (M) (v : α →ₛ M) :
    Interpret.get (lf.toTuple M v) = lf.comap M v := by
  simp [toTuple]

/-- `toFormula` preserves realization when the valuation is transformed via `comap`. -/
@[simp] theorem realize_toFormula
  {M : Sorts → Type w} [L.MSStructure M]
  (v : α →ₛ M)
  (xs : M [^] σ) :
  lf.toFormula.Realize (lf.comap M v) xs
    ↔
  φ.Realize v xs := by
  classical
  unfold toFormula comap
  apply realize_restrictFreeVar
  intro s a h
  simp only [MSEquiv.inv_to]

--TODO: clean this proof up.
/-- Semantic correctness for `toBoundedFormula`. Only for `Formula` (σ = nil). -/
theorem realize_toBoundedFormula
  {M : Sorts → Type w} [L.MSStructure M]
  {φ : L.Formula α} (lf : φ.LocalForm)
  (x : α →ₛ M) :
  φ.Realize x ↔
    lf.toBoundedFormula.Realize default (lf.toTuple M x) := by
    unfold toBoundedFormula toTuple comap;
    rw[realize_reindex, realize_closeVars, realize_rename, realize_rename,
      realize_restrictFreeVar (M:= M) (v':= x) ]
    · unfold Formula.Realize
      congr!
    · intro s a h
      simp_all only  [Pi.default_def, Fam.id, id_eq, Sum.elim_comp_inr, Function.comp_apply]
      unfold Interpret.comap
      simp only [fromGet, reduce_nil, PUnit.default_eq_unit, SigEquiv.nilLeft, SigMap.nil_left,
        fromGet_get, MSEquiv.inv_to]

/-- Semantic correctness for `toFormula` at the formula level (σ = nil). -/
theorem realize_toFormula_formula
  {M : Sorts → Type w} [L.MSStructure M]
  {φ : L.Formula α} (lf : φ.LocalForm)
  (x : α →ₛ M) :
  φ.Realize x ↔
    Formula.Realize (lf.toFormula) (lf.comap M x) := by
    unfold toFormula Formula.Realize comap
    rw[φ.realize_restrictFreeVar]
    intro s a h
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


namespace Formula

/-
@[simp]
theorem realize_equivSentence_symm_con [L[[α]].MSStructure M]
    [(L.lhomWithConstants α).IsExpansionOn M] (φ : L[[α]].Sentence) :
    ((equivSentence.symm φ).Realize fun a => (L.con a : M)) ↔ φ.Realize M := by
  simp only [equivSentence, _root_.Equiv.symm_symm, Equiv.coe_trans, Realize,
    BoundedFormula.realize_relabelEquiv, Function.comp]
  refine _root_.trans ?_ BoundedFormula.realize_constantsVarsEquiv
  rw [iff_iff_eq]
  congr with (_ | a)
  · simp
  · cases a

@[simp]
theorem realize_equivSentence [L[[α]].MSStructure M] [(L.lhomWithConstants α).IsExpansionOn M]
    (φ : L.Formula α) : (equivSentence φ).Realize M ↔ φ.Realize fun a => (L.con a : M) := by
  rw [← realize_equivSentence_symm_con M (equivSentence φ), _root_.Equiv.symm_apply_apply]

theorem realize_equivSentence_symm (φ : L[[α]].Sentence) (v : famMap α M) :
    (equivSentence.symm φ).Realize v ↔
      @Sentence.Realize _ M
        (@MSLanguage.withConstantsMSStructure L M _ α
          (constantsOn.MSStructure v))
        φ :=
  letI := constantsOn.MSStructure v
  realize_equivSentence_symm_con M φ
-/
end Formula



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
    M ⊨ φ.onTheory T ↔ M ⊨ T := by simp [Theory.model_iff, LHom.onTheory]

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
theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by simp

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
    φ.alls.Realize v ↔ ∀ xs : M[^]σ, φ.Realize v xs := by
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
    φ.exs.Realize v ↔ ∃ xs : M[^]σ, φ.Realize v xs := by
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
    (φ.iAlls β : L.Formula α).Realize v ↔
      ∀ (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
  simp only [Formula.iAlls, realize_alls, Prod.forall, reduce_nil, PUnit.default_eq_unit,
    forall_const]
  simp only [reduce_nil, Formula.Realize, PUnit.default_eq_unit]
  let σ := (Signature.famToSignature β).fst
  let e : β ≃ₛ σ.Idx := (Signature.famToSignature β).snd
  change (∀ (a : M[^]σ),
    (relabel (fun s a ↦ Sum.map id (e s) a) φ).Realize v (a, PUnit.unit)) ↔
  ∀ (v' : β →ₛ M), Realize φ (Fam.sumElim v v') PUnit.unit
  simp only [Formula] at φ
  apply Iff.intro
  · intro h v'
    let h' := h (Interpret.fromGet (v' ∘ₛ e.symm ))
    rw[realize_relabel] at h'
    simp[Fam.sumElim, Sum.elim_map, Function.comp_assoc, MSEquiv.symm] at h'
    simp_all only [reduce_nil, σ, e]
  · intro h xs
    rw[realize_relabel]
    simp[Fam.sumElim, Sum.elim_map]
    simp_all only [reduce_nil]

@[simp]
theorem realize_iAlls [Finite (Sigma β)]
    {φ : L.Formula (α ⊕ₛ β)} {v : α →ₛ M}
    {xs : Signature.nil.Interpret M} :
    BoundedFormula.Realize (φ.iAlls β) v xs ↔
      ∀ (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
  rw [← Formula.realize_iAlls, iff_iff_eq, Formula.Realize]

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iExs
    [Finite (Sigma β)] {φ : L.Formula (α ⊕ₛ β)} {v : α →ₛ M} :
    (φ.iExs β).Realize v ↔
      ∃ (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
  simp only [Formula.iExs, realize_exs, Prod.exists, reduce_nil, PUnit.default_eq_unit,
    exists_const]
  simp only [reduce_nil, Formula.Realize, PUnit.default_eq_unit]
  let σ := (Signature.famToSignature β).fst
  let e : β ≃ₛ σ.Idx := (Signature.famToSignature β).snd
  change
    (∃ (a : Signature.Interpret M σ),
        (relabel (fun s a ↦ Sum.map id (e s) a) φ).Realize v (a, PUnit.unit))
      ↔
    ∃ (i : β →ₛ M), Realize φ (Fam.sumElim v i) PUnit.unit
  simp [Formula] at φ
  constructor
  · rintro ⟨a, ha⟩
    rw [realize_relabel] at ha
    refine ⟨a.get ∘ₛ e, ?_⟩
    simp only [Fam.sumElim, Sum.elim_map, CompTriple.comp_eq, reduce_nil] at ha
    exact ha
  · rintro ⟨i, hi⟩
    refine ⟨Interpret.fromGet (i ∘ₛ e.symm), ?_⟩
    rw [realize_relabel]
    simp only [Fam.sumElim, MSEquiv.symm, fromGet_get, Sum.elim_map, CompTriple.comp_eq,
      Function.comp_assoc, MSEquiv.inv_comp, reduce_nil]
    exact hi

@[simp]
theorem realize_iExs
    [Finite (Sigma β)] {φ : L.Formula (α ⊕ₛ β)} {v : α →ₛ M}
    {xs : Signature.nil.Interpret M} :
    BoundedFormula.Realize (φ.iExs β) v xs ↔
      ∃ (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
    rw[←Formula.realize_iExs]
    simp only [reduce_nil, PUnit.default_eq_unit, Formula.Realize]

/-
@[simp]
theorem realize_toFormula (φ : L.BoundedFormula α σ) (v : (α ⊕ₛ σ.Idx) →ₛ M) :
    φ.toFormula.Realize v ↔
      φ.Realize (v ∘ₛ Fam.Sum_inl) (sorted_tupleFromFam (v ∘ₛ Fam.Sum_inr)) := by
  induction φ with
  | falsum => rfl
  | equal => simp [BoundedFormula.Realize]
  | rel => simp [BoundedFormula.Realize]
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
      · simp
      · refine Fin.lastCases ?_ ?_ x
        · rw [Sum.elim_inr, Sum.elim_inr,
            finSumFinEquiv_symm_last, Sum.map_inr, Sum.elim_inr]
          simp [Fin.snoc]
        · simp only [castSucc, Sum.elim_inr,
            finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, Sum.elim_inl]
          rw [← castSucc]
          simp
    · exact Fin.elim0 x
-/

@[simp]
theorem realize_iSup {X}
    [Finite X] {ξ : Signature Sorts} {f : X → L.BoundedFormula α ξ}
    {v : α →ₛ M} {xs : ξ.Interpret M} :
    (BoundedFormula.iSup f).Realize v xs ↔ ∃ b, (f b).Realize v xs := by
  simp [BoundedFormula.iSup, realize_foldr_sup]

@[simp]
theorem realize_iInf {X}
    [Finite X] {ξ : Signature Sorts} {f : X → L.BoundedFormula α ξ}
    {v : α →ₛ M} {xs : ξ.Interpret M} :
    (BoundedFormula.iInf f).Realize v xs ↔ ∀ b, (f b).Realize v xs := by
  simp [BoundedFormula.iInf, realize_foldr_inf]

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iSup {X} [Finite X] {f : X → L.Formula α}
    {v : α →ₛ M} : (Formula.iSup f).Realize v ↔ ∃ b, (f b).Realize v := by
  simp [Formula.iSup, Formula.Realize]

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iInf {X} [Finite X] {f : X → L.Formula α}
    {v : α →ₛ M} : (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v := by
  simp [Formula.iInf, Formula.Realize]

theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iExsUnique {X} [Finite (Sigma X)]
    {φ : L.Formula (α ⊕ₛ X)} {v : α →ₛ M} : (φ.iExsUnique X).Realize v ↔
      ∃! (i : X →ₛ M), φ.Realize (Fam.sumElim v i) := by
  rw [Formula.iExsUnique, ExistsUnique]
  simp only [Formula.Realize, PUnit.default_eq_unit, reduce_nil, realize_iExs, realize_inf,
    realize_iAlls, realize_imp, realize_rename, realize_iInf]
  refine exists_congr (fun i => and_congr_right' (forall_congr' (fun y => ?_)))
  rw [sumComp_elim]
  congr!
  apply Iff.intro
  · intro h
    ext s a
    let h' := h ⟨s, a⟩
    simp only [Term.equal, Term.mapVars, Term.bind, reduce_nil, realize_bdEqual, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr] at h'
    simp only [h']
  · intro a_1 b
    subst a_1
    obtain ⟨fst, snd⟩ := b
    simp_all only [reduce_nil]
    rfl

@[simp]
theorem realize_iExsUnique
    [Finite (Sigma β)] {φ : L.Formula (α ⊕ₛ β)} {v : α →ₛ M} {xs : Signature.nil.Interpret M} :
    BoundedFormula.Realize (φ.iExsUnique β) v xs ↔
      ∃! (i : β →ₛ M), φ.Realize (Fam.sumElim v i) := by
  -- same pattern as your `realize_iAlls` / `realize_iExs`
  rw [← Formula.realize_iExsUnique (L := L) (M := M) (φ := φ) (v := v),
      iff_iff_eq, Formula.Realize]


/-! ### Semantic lemmas for additional syntactic operations -/

/-
/-- Realization of `substFreeVars`: substituting only the free variables that occur in the formula.
This relates to `realize_subst` but handles the restriction to occurring variables.
-/
theorem realize_substFreeVars [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {φ : L.BoundedFormula α σ}
    (f : ∀ (s), {x : α s // ⟨s, x⟩ ∈ freeVarFinset φ} → L.Term (β ⊕ₛ σ.Idx) ⦃s⦄)
    {v : β →ₛ M} {xs : M[^]σ} :
    (φ.substFreeVars f).Realize v xs ↔
      φ.Realize (fun s a => (f s ⟨a, sorry⟩).realize (Fam.sumElim v xs)) xs := by
  -- Proof: unfold substFreeVars as restrictFreeVar followed by subst,
  -- then use realize_restrictFreeVar and realize_subst

  sorry
-/

/-- Realization of `mapTermRelEquiv`: mapping terms and relations
via equivalences preserves satisfaction when the equivalences
preserve realization. -/
theorem realize_mapTermRelEquiv
    {L' : MSLanguage.{u, v, z} Sorts}
    {β : Sorts → Type*}
    (ft : ∀ (ξ τ : Signature Sorts), L.Term (α ⊕ₛ ξ.Idx) τ ≃ L'.Term (β ⊕ₛ ξ.Idx) τ)
    (fr : ∀ ξ, L.Relations ξ ≃ L'.Relations ξ)
    [L'.MSStructure M]
    {φ : L.BoundedFormula α σ} {v : α →ₛ M} {w : β →ₛ M} {xs : M [^] σ}
    (hft : ∀ ξ τ (t : L.Term (α ⊕ₛ ξ.Idx) τ) (ys : ξ.Interpret M),
      (ft ξ τ t).realize (Fam.sumElim w (ys : ξ.Idx →ₛ M)) =
        t.realize (Fam.sumElim v (ys : ξ.Idx →ₛ M)))
    (hfr : ∀ ξ (R : L.Relations ξ) (ys : ξ.Interpret M), RelMap (fr ξ R) ys ↔ RelMap R ys) :
    ((mapTermRelEquiv ft fr) φ).Realize w xs ↔ φ.Realize v xs := by
  simp only [mapTermRelEquiv, Equiv.coe_fn_mk]
  exact realize_mapTermRel_id (fun ξ τ => ft ξ τ) (fun ξ => fr ξ)
    (fun ξ τ t ys => hft ξ τ t ys) (fun ξ R ys => propext (hfr ξ R ys))

/-- Realization of `bigAnd`: conjunction of a list of formulas. -/
@[simp]
theorem realize_bigAnd (l : List (L.BoundedFormula α σ))
    {v : α →ₛ M} {xs : M [^] σ} :
    (bigAnd l).Realize v xs ↔ ∀ φ ∈ l, φ.Realize v xs := by
  simp [bigAnd]

/-- Realization of `bigOr`: disjunction of a list of formulas. -/
@[simp]
theorem realize_bigOr (l : List (L.BoundedFormula α σ))
    {v : α →ₛ M} {xs : M [^] σ} :
    (bigOr l).Realize v xs ↔ ∃ φ ∈ l, φ.Realize v xs := by
  simp [bigOr]

end BoundedFormula

namespace StrongHomClass

variable {F : Type*} [DFunLike F Sorts (fun t => M t → N t)]
variable [PerSortEquivLike F M N] [StrongHomClass L F M N] (g : F)

@[simp]
theorem realize_boundedFormula {σ} (φ : L.BoundedFormula α σ) {v : α →ₛ M}
    {xs : M [^] σ} : φ.Realize (g ∘ₛ v) (g <$>ₛ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal =>
    rw [BoundedFormula.Realize, BoundedFormula.Realize, Interpret.get_map,
      ← Fam.sumComp_elim, HomClass.realize_term, HomClass.realize_term]
    refine Function.Injective.eq_iff (Function.HasLeftInverse.injective ⟨?_,?_⟩ )
    · exact Interpret.map (PerSortEquivLike.inv g)
    · rw [Function.leftInverse_iff_comp]
      funext xs
      rw [Function.comp, ←  Interpret.comp_map, Function.id_def]
      have : (fun t ↦ PerSortEquivLike.inv g t ∘ g t) = fun _ => id := by
        funext t
        rw [← Function.leftInverse_iff_comp]
        apply PerSortEquivLike.left_inv g
      simp [this]
  | rel =>
    rename_i σ' σ R ts
    rw [BoundedFormula.Realize, BoundedFormula.Realize, Interpret.get_map,
         ← Fam.sumComp_elim g, HomClass.realize_term]
    exact StrongHomClass.map_rel g _ _
  | imp _ _ ih₁ ih₂ => rw [BoundedFormula.Realize, ih₁, ih₂, BoundedFormula.Realize]
  | all η φ ih₃ =>
    rw [BoundedFormula.Realize, BoundedFormula.Realize]
    constructor
    · intro h ys
      have h' := h (g <$>ₛ ys)
      rw [← Interpret.map_prod, ih₃] at h'
      exact h'
    · intro h ys
      have h' := h (PerSortEquivLike.inv g <$>ₛ ys)
      rw [← ih₃, Interpret.map_prod, ← Interpret.comp_map,
        PerSortEquivLike.apply_inv_apply_fun g, map_id] at h'
      exact h'

@[simp]
theorem realize_formula (φ : L.Formula α) {v : α →ₛ M} :
    φ.Realize (g ∘ₛ v) ↔ φ.Realize v := by
  rw [Formula.Realize, Formula.Realize, ← realize_boundedFormula g φ, iff_eq_eq]
include g

theorem realize_sentence (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize, Sentence.Realize, ← realize_formula g]
  refine Eq.to_iff ?_
  congr
  funext _ a
  exact Empty.elim a

theorem theory_model [M ⊨ T] : N ⊨ T :=
  ⟨fun φ hφ => (realize_sentence g φ).1 (Theory.realize_sentence_of_mem T hφ)⟩

theorem elementarilyEquivalent : M ≅[L] N :=
  elementarilyEquivalent_iff.2 (realize_sentence g)

end StrongHomClass
end MSLanguage
end MSFirstOrder
