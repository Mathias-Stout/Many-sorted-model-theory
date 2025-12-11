import ProdExpr.Syntax

/-
Based on the corresponding Mathlib file
Mathlib\ModelTheory\Semantics.lean
which was authored by 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn,
and is released under the Apache 2.0 license.

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/



universe u v w z u' v'

namespace ProdExpr
open MSFirstOrder

/-- Notation for constructing ProdExprs, similar to the one for vectors -/
syntax (name := ProdExprNotation) "!ₚ[" term,* "]" : term

macro_rules
  | `(!ₚ[$term:term, $terms:term,*]) => `(ProdExpr.prod (ProdExpr.of $term) !ₚ[$terms,*])
  | `(!ₚ[$term:term]) => `(ProdExpr.of $term)
  | `(!ₚ[]) => `(ProdExpr.nil)

example : ProdExpr (Fin 2) := !ₚ[0,0,0]

example : (ProdExpr.of 0) = !ₚ[0] := rfl
example : (ProdExpr.of 0).prod (ProdExpr.of 0) = !ₚ[0,0] := rfl

--TODO: replace this by some metaprogramming
abbrev fromList {S : Type*} : (List S) → ProdExpr S
    | [] => .nil
    | [a] => .of a
    | a :: (b :: r) => .prod (.of a) (fromList (b :: r))

instance instCoeFromList {S : Type*} : Coe (List S) (ProdExpr S) := ⟨fromList⟩

end ProdExpr

namespace MSFirstOrder

namespace MSLanguage

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
  {M : Sorts → Type w} {N P : Sorts → Type*} [L.MSStructure M] [L.MSStructure N] [L.MSStructure P]
  {α : Sorts → Type u'} {β : Sorts → Type v'} {γ : Sorts → Type*}
  {s : Sorts} {t : Sorts} {σ : ProdExpr Sorts}

open MSFirstOrder Cardinal

open MSStructure MSLanguage Fin Finsupp Fam SortedTuple



namespace Term

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
def realize {σ : ProdExpr Sorts} (v : α →ₛ M) : L.Term α σ → σ.Interpret M
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
theorem realize_func (v : α →ₛ M) {σ : ProdExpr Sorts} (f : L.Functions σ t) (ts) :
    realize v (func f ts) = funMap (M:= M) f (realize v ts) := rfl

@[simp]
theorem realize_prod (v : α →ₛ M) {σ₁ σ₂ : ProdExpr Sorts} (t₁ : L.Term α σ₁) (t₂ : L.Term α σ₂) :
    realize v (prod t₁ t₂) = ⟨ realize v t₁, realize v t₂⟩ := rfl

theorem realize_relabel' {t : L.Term α σ} {g : α →ₛ β} {v : β →ₛ M} :
    (t.relabel g).realize v = t.realize (v ∘ₛ g) := by
  induction t <;> simp_all[relabel]

/-- Realize commutes with relabel: -/
@[simp]
lemma realize_relabel
    {α β : Sorts → Type u'} {σ : ProdExpr Sorts}
    (f : α →ₛ β) (v : β →ₛ M) (t : Term L α σ) :
    realize v (relabel f t) =
    realize (v ∘ₛ f) t := by
  induction t <;> simp_all [relabel]

@[simp]
theorem realize_varterm {σ} (v : σ.indVar →ₛ M) :
  realize v (L.varTerm σ) = fromGet v  := by
  induction σ with
  | nil => rfl
  | of s => rfl
  | prod σ₁ σ₂ ih₁ ih₂ =>
    rw [varTerm, realize_prod, realize_relabel, realize_relabel, ih₁, ih₂, fromGet]
    rfl


@[simp]
theorem realize_function_term {σ} (v : σ.indVar →ₛ M) (f : L.Functions σ t) :
    f.term.realize v = funMap f (fromGet v) := by
  induction σ with
  | nil => rfl
  | of s => rfl
  | prod σ τ ih₁ ih₂ => simp[Functions.term, realize_func]

open ProdExpr

/-- Realizing a term at a reindexed tuple is equivalent to relabelling the term
  and then realizing at the original tuple.
-/
lemma realize_relabel_right
    {σ τ ξ : ProdExpr Sorts}
    (g : VarMap σ τ)
    (t : L.Term (α ⊕ₛ σ.indVar) ξ)
    (v : α →ₛ M)
    (xs : τ.Interpret M) :
  t.realize (Fam.sumElim v (xs.reindex g))
    =
  (t.relabel_right g).realize (Fam.sumElim v xs) := by
  unfold Fam.sumElim relabel_right
  rw[realize_relabel (M:= M) _ _ t]
  rw[Interpret.reindex]
  have h:  (fun s ↦ Sum.elim (v s) fun w ↦ SortedTuple.get xs s (g s w))
          =(fun t ↦ Sum.elim (v t) (SortedTuple.get xs t) ∘ Sum.map id (g t)) := by
    ext s t
    rw[Function.comp_apply]
    cases t with
    | inl val => simp_all only [Sum.elim_inl, Sum.map_inl, id_eq]
    | inr val_1 => simp_all only [Sum.elim_inr, Sum.map_inr]
  simp[h]



/-
@[simp]
theorem realize_liftAt {σ τ ρ: ProdExpr Sorts} (σ'  : ProdExpr Sorts)
{t : L.Term (α ⊕ₛ σ.indVar) ξ} {v : (α ⊕ₛ (σ.prod τ).indVar ) →ₛ M} :
    (t.liftAt ξ η).realize v =
      t.realize ( fun s => (v s) ∘ Sum.map id fun i : Fin (σ s) =>
        if ↑i < (η s) then Fin.castAdd (ξ s) i else Fin.addNat i (ξ s)) :=
  realize_relabel
-/

@[simp]
theorem realize_constants {c : L.Constants t} {v : α →ₛ M} :  (c.term.realize v) = (c : M t) :=
  funMap_eq_coe_constants

theorem realize_functions_apply₁ {f : L.Functions !ₚ[s] t} {g : L.Term α !ₚ[s]} {v : α →ₛ M} :
    (f.apply₁ g).realize v = funMap f (g.realize v) := by rw [Functions.apply₁, Term.realize]

@[simp]
theorem realize_functions_apply₂ {s s₁ s₂ : Sorts} {f : L.Functions !ₚ[s₁, s₂] s}
    {t₁ : L.Term α !ₚ[s₁]} {t₂ : L.Term α !ₚ[s₂]} {v : α →ₛ M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ⟨t₁.realize v, t₂.realize v⟩  := by
  rw [Functions.apply₂, Term.realize]
  simp_all only [realize_prod]


theorem realize_con {A : (s : Sorts) → Set (M s)} {s : Sorts} {a : A s}
    {v : α →ₛ M} : (L.con (α := M) s a).term.realize v = (a : M s) :=
  rfl

/- def subst {σ} : L.Term α σ → ((s : Sorts) → α s → (L.Term β (of s))) → L.Term β σ -/
/- fun s a => (tf s a).realize v -/
@[simp]
theorem realize_subst {σ} {t : L.Term α σ} {tf : (s : Sorts) → α s → L.Term β !ₚ[s]} {v : β →ₛ M} :
    (t.subst tf).realize v = t.realize (fun s a => ((tf s a).realize v)) := by
  induction t with
  | nil => rfl
  | var _ _ => rfl
  | func _ _ ih => simp [ih]
  | prod _ _ ih₁ ih₂ => simp [ih₁, ih₂]

--todo after porting more of syntax
/-
theorem realize_restrictVar [DecidableEq α] {t : L.Term α} {f : t.varFinset → β}
    {v : β →ₛ M} (v' : α →ₛ M) (hv' : ∀ a, v (f a) = v' a) :
    (t.restrictVar f).realize v = t.realize v' := by
  induction t with
  | var => simp [restrictVar, hv']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i ((by simp [Function.comp_apply, hv'])))

/-- A special case of `realize_restrictVar`, included because we can add the `simp` attribute
to it -/
@[simp]
theorem realize_restrictVar' [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset ⊆ s)
    {v : α →ₛ M} : (t.restrictVar (Set.inclusion h)).realize (v ∘ (↑)) = t.realize v :=
  realize_restrictVar _ (by simp)

theorem realize_restrictVarLeft [DecidableEq α] {γ : Type*} {t : L.Term (α ⊕ γ)}
    {f : t.varFinsetLeft → β}
    {xs : β ⊕ γ → M} (xs' : α →ₛ M) (hxs' : ∀ a, xs (Sum.inl (f a)) = xs' a) :
    (t.restrictVarLeft f).realize xs = t.realize (Sum.elim xs' (xs ∘ Sum.inr)) := by
  induction t with
  | var a => cases a <;> simp [restrictVarLeft, hxs']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i (by simp [hxs']))

/-- A special case of `realize_restrictVarLeft`, included because we can add the `simp` attribute
to it -/
@[simp]
theorem realize_restrictVarLeft' [DecidableEq α] {γ : Type*} {t : L.Term (α ⊕ γ)} {s : Set α}
    (h : ↑t.varFinsetLeft ⊆ s) {v : famMap α M} {xs : γ → M} :
    (t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ (↑)) xs) =
      t.realize (Sum.elim v xs) :=
  realize_restrictVarLeft _ (by simp)

@[simp]
theorem realize_constantsToVars [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L[[α]].Term β} {v : famMap β M} :
    t.constantsToVars.realize (Sum.elim (fun a => ↑(L.con a)) v) = t.realize v := by
  induction t with
  | var => simp
  | @func n f ts ih =>
    cases n
    · cases f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · simp only [realize, constantsToVars, Sum.elim_inl, funMap_eq_coe_constants]
        rfl
    · obtain - | f := f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · exact isEmptyElim f

@[simp]
theorem realize_varsToConstants [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L.Term (α ⊕ β)} {v : famMap β M} :
    t.varsToConstants.realize v = t.realize (Sum.elim (fun a => ↑(L.con a)) v) := by
  induction t with
  | var ab => rcases ab with a | b <;> simp [MSLanguage.con]
  | func f ts ih =>
    simp only [realize, constantsOn, constantsOnFunc, ih, varsToConstants]
    -- Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sumInl]

theorem realize_constantsVarsEquivLeft [L[[α]].MSStructure M]
    [(lhomWithConstants L α).IsExpansionOn M] {n} {t : L[[α]].Term (β ⊕ (Fin n))} {v : famMap β M}
    {xs : σ.Interpret M} :
    (constantsVarsEquivLeft t).realize (Sum.elim (Sum.elim (fun a => ↑(L.con a)) v) xs) =
      t.realize (Sum.elim v xs) := by
  simp only [constantsVarsEquivLeft, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constantsVarsEquiv_apply, relabelEquiv_symm_apply]
  refine _root_.trans ?_ realize_constantsToVars
  rcongr x
  rcases x with (a | (b | i)) <;> simp
-/
end Term

namespace LHom


@[simp]
theorem realize_onTerm {σ : ProdExpr Sorts} [L'.MSStructure M] (φ : L →ᴸ L')
  [φ.IsExpansionOn M] (t : L.Term α σ) (v : α →ₛ M) :
  (φ.onTerm t).realize v = t.realize v := by
  induction t with
  | nil => rfl
  | var => rfl
  | func _ _ ih => simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]
  | prod _ _ ih₁ ih₂ => simp only [onTerm, Term.realize_prod, ih₁, ih₂]

end LHom
variable {σ : ProdExpr Sorts}


@[simp]
theorem HomClass.realize_term {F : Type*} [DFunLike F Sorts (fun t => M t → N t)] [HomClass L F M N]
    (g : F) {t : L.Term α σ} {v : famMap α M} :
    t.realize (g ∘ₛ v) = g <$>ₛ (t.realize v) := by
  induction t with
  | nil => rfl
  | var => rfl
  | func _ _ ih =>
    rw [Term.realize, ih, Term.realize, SortedTuple.map, HomClass.map_fun]
  | prod _ _ ih₁ ih₂ => simp only [Term.realize_prod, ih₁, ih₂, SortedTuple.map]
namespace BoundedFormula

open Term SortedTuple
/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def Realize : ∀ {ξ} (_φ : L.BoundedFormula α ξ) (_v : α →ₛ M) (_xs : ξ.Interpret M), Prop
  | _, falsum, _v, _xs => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Fam.sumElim v xs)
      = t₂.realize (Fam.sumElim v xs)
  | _, rel R ts, v, xs => RelMap R (ts.realize (Fam.sumElim v xs))
  | _, imp φ₁ φ₂, v, xs => Realize φ₁ v xs → Realize φ₂ v xs
  | _, all σ φ, v, xs => ∀ x : σ.Interpret M, Realize φ v ⟨xs, x⟩

variable {ξ η : ProdExpr Sorts} {φ ψ : L.BoundedFormula α ξ} {θ : L.BoundedFormula α (ξ.prod η)}
variable {v : famMap α M} {xs : ξ.Interpret M}

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormula α ξ).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_not : φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_bdEqual (t₁ t₂ : L.Term (α ⊕ₛ ξ.indVar) σ) :
    (t₁.bdEqual t₂).Realize v xs ↔ t₁.realize (Fam.sumElim v xs) = t₂.realize (Fam.sumElim v xs) :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormula α ξ).Realize v xs ↔ True := by simp [Top.top]

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp [Realize]

@[simp]
theorem realize_foldr_inf {σ} (l : List (L.BoundedFormula α σ))
  (v : famMap α M) (xs : σ.Interpret M) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ ∀ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs := by
  simp only [Realize]

/-- List.foldr on BoundedFormula.imp gives a big "And" of input conditions. -/
theorem realize_foldr_imp {η : ProdExpr Sorts} (l : List (L.BoundedFormula α η))
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
theorem realize_rel₁ {s : Sorts} {R : L.Relations !ₚ[s]} {t : L.Term _ !ₚ[s]} :
    (R.boundedFormula₁ t).Realize v xs ↔ RelMap R (t.realize (Fam.sumElim v xs)) := by
  rw [Relations.boundedFormula₁, realize_rel, iff_eq_eq]

@[simp]
theorem realize_rel₂ {s₁ s₂ : Sorts} {R : L.Relations !ₚ[s₁, s₂]}
    {t₁ : L.Term _ !ₚ[s₁]} {t₂ : L.Term _ !ₚ[s₂]} :
    (R.boundedFormula₂ t₁ t₂).Realize v xs ↔
    RelMap R ((t₁.prod t₂).realize (Fam.sumElim v xs)) := by
  rw [Relations.boundedFormula₂, realize_rel, iff_eq_eq]


@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [max]
  tauto

@[simp]
theorem realize_foldr_sup (l : List (L.BoundedFormula α σ)) (v : famMap α M) (xs : σ.Interpret M) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
      exists_eq_left]

@[simp]
theorem realize_all : (all η θ).Realize v xs ↔ ∀ a : η.Interpret M , θ.Realize v ⟨xs, a⟩ :=
  Iff.rfl

@[simp]
theorem realize_ex : (θ.ex η).Realize v xs ↔ ∃ a : η.Interpret M, θ.Realize v ⟨xs, a⟩  := by
  rw [BoundedFormula.ex, realize_not, realize_all, not_forall]
  simp only [realize_not, Classical.not_not]

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormula.iff, realize_inf, realize_imp, ← iff_def]

open ProdExpr VarEquiv Interpret

open Lean.Parser.Tactic
syntax "elab_prod" (ppSpace location)? : tactic

macro_rules
  | `(tactic| elab_prod $[$loc]?) => `(tactic| simp only [Interpret] $[$loc]?)


@[simp]
lemma reindex_extend_right {x : η.Interpret M}
    (g : VarMap σ ξ) : Interpret.reindex g.extend_right (xs, x) = (xs.reindex g, x) := by
    have hget :
      SortedTuple.get (reindex g.extend_right (xs, x))
        = fun s v =>
            match v with
            | indVar.left  wσ => SortedTuple.get xs s (g s wσ)
            | indVar.right wη => SortedTuple.get x  s wη := by
          funext s v
          cases v with
          | left wσ =>
            rw[get_reindex]; unfold VarMap.extend_right; simp[SortedTuple.get]
          | right wη =>
            rw[get_reindex]; unfold VarMap.extend_right; simp[SortedTuple.get]
    have hget_rhs :
      SortedTuple.get (xs.reindex g, x)
        = fun s (v : (σ.prod η).indVar s) =>
            match v with
            | .left w => SortedTuple.get xs s (g s w)
            | .right w => SortedTuple.get x  s w := by
      funext s v
      cases v with
      | left wσ =>
          simp [Interpret.reindex, SortedTuple.get]
      | right wη =>
          simp [SortedTuple.get]
    have h :
    SortedTuple.get (reindex g.extend_right (xs, x))
      = SortedTuple.get (xs.reindex g, x) := by
        funext s v; rw[hget, hget_rhs]
    have h':= congrArg (SortedTuple.fromGet (S := Sorts) (α := M) (σ := σ.prod η)) h
    rw[get_fromGet] at h'
    simp[h']


/-- Reindexing a sorted tuple along a VarMap commutes with casting the formula along the VarMap -/
lemma realize_castLE
    {σ τ : ProdExpr Sorts}
    (g : VarMap σ τ)
    (φ : L.BoundedFormula α σ)
    (v : α →ₛ M)
    (xs : τ.Interpret M) :
  (φ.castLE g).Realize v xs
    ↔
  φ.Realize v (xs.reindex g) := by
  induction φ generalizing τ with
  | falsum => simp_all only [castLE]; rfl
  | equal t₁ t₂ =>
    unfold castLE Realize
    simp only [realize_relabel_right, realize_relabel_right]
  | rel r t =>
    unfold castLE Realize
    simp only [realize_relabel_right, realize_relabel_right]
  | imp  => simp_all only [castLE, realize_imp]
  | all η ψ ih =>
    have ih' := ih (g.extend_right (η := η))
    unfold castLE Realize; simp[ih']

/-
sorry

theorem realize_castLE_of_eq {ξ σ : ProdExpr Sorts} (h : ξ = σ) {h' : ξ ≤ σ}
  {φ : L.BoundedFormula α ξ}
    --note: annoying bit of coercion happens here to go from ξ = σ to ∀ s, ξ s = σ s
    {v : famMap α M} {xs : σ.Interpret M} :

    (φ.castLE h').Realize v xs
     ↔
    φ.Realize v (fun s => (xs s) ∘ Fin.cast (congr_fun (congr_arg DFunLike.coe h) s)) := by

  subst h
  simp only [castLE_rfl, cast_refl, Function.comp_id]
-/

theorem realize_mapTermRel_id [L'.MSStructure M] {φ : L.BoundedFormula α σ}
    (ft : ∀ σ ξ : ProdExpr Sorts, L.Term (α ⊕ₛ σ.indVar) ξ →  L'.Term (β ⊕ₛ σ.indVar) ξ)
    (fr : ∀ σ, L.Relations σ → L'.Relations σ)
    {v' : β →ₛ M} {xs : σ.Interpret M}
    (h1 :
      ∀ (σ) (τ) (t : L.Term (α ⊕ₛ σ.indVar) τ) (xs : σ.Interpret M),
        (ft σ τ t).realize (Fam.sumElim v' (SortedTuple.get xs)) =
        t.realize (Fam.sumElim v (SortedTuple.get xs)))
    (h2 : ∀ (σ) (R : L.Relations σ) (x : σ.Interpret M), RelMap (fr σ R) x = RelMap R x) :
    (φ.mapTermRel ft fr fun _ _ => id).Realize v' xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | @equal σ τ t₁ _ =>
    have h:= h1 σ τ t₁ xs
    simp_all only [mapTermRel, Realize, eq_iff_iff]
  | rel => simp only [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, realize_imp, ih1, ih2, Realize]
  | all _ _ ih => simp only [mapTermRel, id_eq, realize_all, ih, Realize]


/-
--todo: when required
open ProdExpr VarMap
theorem realize_mapTermRel_add_castLE
  [L'.MSStructure M] {σ τ ξ : ProdExpr Sorts}

  {ft : ∀ (τ ξ : ProdExpr Sorts),
      L.Term (α ⊕ₛ τ.indVar) ξ →
        L'.Term (β ⊕ₛ (σ.prod τ).indVar) ξ}

  {fr : ∀ τ : ProdExpr Sorts, L.Relations τ → L'.Relations τ}
  {φ : L.BoundedFormula α τ}

  (v : ∀ {τ}, (σ.prod τ).Interpret M → α →ₛ M)
  {v' : β →ₛ M}

  (xs : (σ.prod τ).Interpret M)

  (h1 :
    ∀ (τ ξ) (t : L.Term (α ⊕ₛ τ.indVar) ξ) (xs' : (σ.prod τ).Interpret M),
      (ft τ ξ t).realize (Fam.sumElim v' (SortedTuple.get xs')) =
        t.realize (Fam.sumElim (v xs') (SortedTuple.get xs' ∘ₛ incl_right)))

  (h2 :
    ∀ (τ) (R : L.Relations τ) (x : τ.Interpret M),
      RelMap (fr τ R) x = RelMap R x)

  (hv :
    ∀ (τ η) (xs : (σ.prod τ).Interpret M) (x : η.Interpret M),
      @v (τ.prod η)
        (interpretEquiv M (PEquiv.assocL σ _ _ ) ((xs, x) :
        ((σ.prod τ).prod η).Interpret M)) = v xs) :

  (φ.mapTermRel ft fr (fun τ₀ η => castLE (L := L') (α := β) (VarMap.assocR σ τ₀ η))).Realize v' xs
    ↔
    φ.Realize (v xs) (fromGet (SortedTuple.get xs ∘ₛ incl_right (σ := τ))) := by
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






/-
@[simp]
theorem realize_relabel {m n : ℕ} {φ : L.BoundedFormula α n}
{g : famMap α β ⊕ (Fin m)} {v : famMap β M}
    {xs : Fin (m + n) → M} :
    (φ.relabel g).Realize v xs ↔
      φ.Realize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
  apply realize_mapTermRel_add_castLe <;> simp

theorem realize_liftAt {n n' m : ℕ} {φ : L.BoundedFormula α n}
 {v : famMap α M} {xs : Fin (n + n') → M}
    (hmn : m + n' ≤ n + 1) :
    (φ.liftAt n' m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') := by
  rw [liftAt]
  induction φ with
  | falsum => simp [mapTermRel, Realize]
  | equal => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | rel => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, Realize, ih1 hmn, ih2 hmn]
  | @all k _ ih3 =>
    have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
    simp only [mapTermRel, Realize, realize_castLE_of_eq h, ih3 (hmn.trans k.succ.le_succ)]
    refine forall_congr' fun x => iff_eq_eq.mpr (congr rfl (funext (Fin.lastCases ?_ fun i => ?_)))
    · simp only [Function.comp_apply, val_last, snoc_last]
      refine (congr rfl (Fin.ext ?_)).trans (snoc_last _ _)
      split_ifs <;> dsimp; omega
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      refine (congr rfl (Fin.ext ?_)).trans (snoc_castSucc _ _ _)
      simp only [coe_castSucc, coe_cast]
      split_ifs <;> simp

theorem realize_liftAt_one {n m : ℕ} {φ : L.BoundedFormula α n}
{v : famMap α M} {xs : Fin (n + 1) → M}
    (hmn : m ≤ n) :
    (φ.liftAt 1 m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then castSucc i else i.succ) := by
  simp [realize_liftAt (add_le_add_right hmn 1), castSucc]

@[simp]
theorem realize_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : famMap α M}
    {xs : Fin (n + 1) → M} : (φ.liftAt 1 n).Realize v xs ↔ φ.Realize v (xs ∘ castSucc) := by
  rw [realize_liftAt_one (refl n), iff_eq_eq]
  refine congr rfl (congr rfl (funext fun i => ?_))
  rw [if_pos i.is_lt]

@[simp]
theorem realize_subst {φ : L.BoundedFormula α n} {tf : α → L.Term β}
 {v : famMap β M} {xs : σ.Interpret M} :
    (φ.subst tf).Realize v xs ↔ φ.Realize (fun a => (tf a).realize v) xs :=
  realize_mapTermRel_id
    (fun n t x => by
      rw [Term.realize_subst]
      rcongr a
      cases a
      · simp only [Sum.elim_inl, Function.comp_apply, Term.realize_relabel, Sum.elim_comp_inl]
      · rfl)
    (by simp)

theorem realize_restrictFreeVar [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n}
    {f : φ.freeVarFinset → β} {v : famMap β M} {xs : σ.Interpret M}
    (v' : famMap α M) (hv' : ∀ a, v (f a) = v' a) :
    (φ.restrictFreeVar f).Realize v xs ↔ φ.Realize v' xs := by
  induction φ with
  | falsum => rfl
  | equal =>
    simp only [Realize, restrictFreeVar, freeVarFinset.eq_2]
    rw [realize_restrictVarLeft v' (by simp [hv']), realize_restrictVarLeft v' (by simp [hv'])]
    simp
  | rel =>
    simp only [Realize, freeVarFinset.eq_3, Finset.biUnion_val, restrictFreeVar]
    congr!
    rw [realize_restrictVarLeft v' (by simp [hv'])]
    simp
  | imp _ _ ih1 ih2 =>
    simp only [Realize, restrictFreeVar, freeVarFinset.eq_4]
    rw [ih1, ih2] <;> simp [hv']
  | all _ ih3 =>
    simp only [restrictFreeVar, Realize]
    refine forall_congr' (fun _ => ?_)
    rw [ih3]; simp [hv']

/-- A special case of `realize_restrictFreeVar`, included because we can add the `simp` attribute
to it -/
@[simp]
theorem realize_restrictFreeVar' [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n} {s : Set α}
    (h : ↑φ.freeVarFinset ⊆ s) {v : famMap α M} {xs : σ.Interpret M} :
    (φ.restrictFreeVar (Set.inclusion h)).Realize (v ∘ (↑)) xs ↔ φ.Realize v xs :=
  realize_restrictFreeVar _ (by simp)

theorem realize_constantsVarsEquiv [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {φ : L[[α]].BoundedFormula β n} {v : famMap β M} {xs : σ.Interpret M} :
    (constantsVarsEquiv φ).Realize (Sum.elim (fun a => ↑(L.con a)) v) xs ↔ φ.Realize v xs := by
  refine realize_mapTermRel_id (fun n t xs => realize_constantsVarsEquivLeft) fun n R xs => ?_
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [← (lhomWithConstants L α).map_onRelation
      (Equiv.sumEmpty (L.Relations n) ((constantsOn α).Relations n) R) xs]
  rcongr
  obtain - | R := R
  · simp
  · exact isEmptyElim R

@[simp]
theorem realize_relabelEquiv {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : famMap β M}
    {xs : Fin k → M} : (relabelEquiv g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  refine realize_mapTermRel_id (fun n t xs => ?_) fun _ _ _ => rfl
  simp only [relabelEquiv_apply, Term.realize_relabel]
  refine congr (congr rfl ?_) rfl
  ext (i | i) <;> rfl

variable [Nonempty M]

theorem realize_all_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : famMap α M}
    {xs : σ.Interpret M} : (φ.liftAt 1 n).all.Realize v xs ↔ φ.Realize v xs := by
  inhabit M
  simp only [realize_all, realize_liftAt_one_self]
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · refine (congr rfl (funext fun i => ?_)).mp (h default)
    simp
  · refine (congr rfl (funext fun i => ?_)).mp h
    simp
-/
end BoundedFormula

namespace LHom

open BoundedFormula

@[simp]
theorem realize_onBoundedFormula [L'.MSStructure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    {σ : ProdExpr Sorts} (ψ : L.BoundedFormula α σ) {v : famMap α M} {xs : σ.Interpret M} :
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

/-- A formula can be evaluated as true or false by giving values to each free variable. -/
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
theorem realize_rel {ξ : ProdExpr Sorts} {R : L.Relations ξ} {ts : L.Term α ξ} :
    (R.formula ts).Realize v ↔ RelMap (M := M) R (ts.realize v) := by
  refine BoundedFormula.realize_rel.trans ?_
  -- Note, realize_relabel does not work, Lean gets stuck at solving universe constraints
  rw [ts.realize_relabel']
  rfl



@[simp]
theorem realize_rel₁ {R : L.Relations !ₚ[s]} {t : L.Term α !ₚ[s]} :
    (R.formula₁ t).Realize v ↔ RelMap R (t.realize v) := by
  rw [Relations.formula₁, realize_rel, iff_eq_eq]


@[simp]
theorem realize_rel₂ {s₁ s₂} {R : L.Relations !ₚ[s₁, s₂]} {t₁ : L.Term α !ₚ[s₁]}
  {t₂ : L.Term α !ₚ[s₂]} :
    (R.formula₂ t₁ t₂).Realize v ↔ RelMap R ((t₁.prod t₂).realize (L := L) (M := M) v) := by
  rw [Relations.formula₂, realize_rel, iff_eq_eq]


@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v :=
  BoundedFormula.realize_sup

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v ↔ (φ.Realize v ↔ ψ.Realize v) :=
  BoundedFormula.realize_iff

/-
@[simp]
theorem realize_relabel {φ : L.Formula α} {g : α →ₛ β} {v : β →ₛ M} :
    (φ.relabel g).Realize v ↔ φ.Realize (v ∘ g) := by
  rw [Realize, Realize, relabel, BoundedFormula.realize_relabel, iff_eq_eq, Fin.castAdd_zero]
  exact congr rfl (funext finZeroElim)

theorem realize_relabel_sumInr (φ : L.Formula (Fin n)) {v : Empty → M} {x : σ.Interpret M} :
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
  simp [Term.realize_relabel']


/-
@[simp]
theorem realize_graph {σ} {f : L.Functions σ s} {x : σ.Interpret M} {y : M s} :
    (Formula.graph f).Realize (Fin.cons y x : _ → M) ↔ funMap f x = y := by
  simp only [Formula.graph, Term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  rw [eq_comm]
-/

theorem boundedFormula_realize_eq_realize (φ : L.Formula α) (v : α →ₛ M)
    (ys : ProdExpr.nil.Interpret M) : BoundedFormula.Realize φ v ys ↔ φ.Realize v := by
  rw [Formula.Realize, iff_iff_eq, Unique.eq_default ys]


end Formula

@[simp]
theorem LHom.realize_onFormula [L'.MSStructure M] (φ : L →ᴸ L')
    [φ.IsExpansionOn M] (ψ : L.Formula α) {v : famMap α M} :
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
      @Sentence.Realize _ M (@MSLanguage.withConstantsMSStructure L M _ α
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

variable {σ : ProdExpr Sorts}
/-
@[simp]
theorem realize_alls {φ : L.BoundedFormula α σ} {v : α →ₛ M} :
    φ.alls.Realize v ↔ ∀ xs : σ.Interpret M, φ.Realize v xs := by
  induction n with
  | zero => exact Unique.forall_iff.symm
  | succ n ih =>
    simp only [alls, ih, Realize]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩

@[simp]
theorem realize_exs {φ : L.BoundedFormula α n} {v : famMap α M} :
    φ.exs.Realize v ↔ ∃ xs : σ.Interpret M, φ.Realize v xs := by
  induction n with
  | zero => exact Unique.exists_iff.symm
  | succ n ih =>
    simp only [BoundedFormula.exs, ih, realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      rw [← Fin.snoc_init_self xs] at h
      exact ⟨_, _, h⟩

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iAlls
    [Finite β] {φ : L.Formula (α ⊕ β)} {v : famMap α M} : (φ.iAlls β).Realize v ↔
      ∀ (i : famMap β M), φ.Realize (fun a => Sum.elim v i a) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  rw [Formula.iAlls]
  simp only [Nat.add_zero, realize_alls, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
theorem realize_iAlls [Finite β] {φ : L.Formula (α ⊕ β)} {v : famMap α M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iAlls β) v v' ↔
      ∀ (i : famMap β M), φ.Realize (fun a => Sum.elim v i a) := by
  rw [← Formula.realize_iAlls, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iExs
    [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : famMap α M} : (φ.iExs γ).Realize v ↔
      ∃ (i : γ → M), φ.Realize (Sum.elim v i) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iExs]
  simp only [Nat.add_zero, realize_exs, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.exists_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
theorem realize_iExs [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : famMap α M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iExs γ) v v' ↔
      ∃ (i : γ → M), φ.Realize (Sum.elim v i) := by
  rw [← Formula.realize_iExs, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
theorem realize_toFormula (φ : L.BoundedFormula α σ) (v : (α ⊕ₛ σ.indVar) →ₛ M) :
    φ.toFormula.Realize v ↔ φ.Realize (v ∘ₛ Fam.Sum_inl)
    (sorted_tupleFromFam (v ∘ₛ Fam.Sum_inr)) := by
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

@[simp]
theorem realize_iSup [Finite β] {f : β → L.BoundedFormula α n}
    {v : famMap α M} {v' : σ.Interpret M} :
    (iSup f).Realize v v' ↔ ∃ b, (f b).Realize v v' := by
  simp only [iSup, realize_foldr_sup, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    exists_exists_eq_and]

@[simp]
theorem realize_iInf [Finite β] {f : β → L.BoundedFormula α n}
    {v : famMap α M} {v' : σ.Interpret M} :
    (iInf f).Realize v v' ↔ ∀ b, (f b).Realize v v' := by
  simp only [iInf, realize_foldr_inf, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iSup [Finite β] {f : β → L.Formula α}
    {v : famMap α M} : (Formula.iSup f).Realize v ↔ ∃ b, (f b).Realize v := by
  simp [Formula.iSup, Formula.Realize]

@[simp]
theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iInf [Finite β] {f : β → L.Formula α}
    {v : famMap α M} : (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v := by
  simp [Formula.iInf, Formula.Realize]

theorem _root_.MSFirstOrder.MSLanguage.Formula.realize_iExsUnique [Finite γ]
    {φ : L.Formula (α ⊕ γ)} {v : famMap α M} : (φ.iExsUnique γ).Realize v ↔
      ∃! (i : γ → M), φ.Realize (Sum.elim v i) := by
  rw [Formula.iExsUnique, ExistsUnique]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_relabel]
  simp only [Formula.Realize, Function.comp_def, Term.equal, Term.relabel, realize_iInf,
    realize_bdEqual, Term.realize_var, Sum.elim_inl, Sum.elim_inr, funext_iff]
  refine exists_congr (fun i => and_congr_right' (forall_congr' (fun y => ?_)))
  rw [iff_iff_eq]; congr with x
  cases x <;> simp

@[simp]
theorem realize_iExsUnique [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : famMap α M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iExsUnique γ) v v' ↔
      ∃! (i : γ → M), φ.Realize (Sum.elim v i) := by
  rw [← Formula.realize_iExsUnique, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]
-/
end BoundedFormula

namespace StrongHomClass

variable {F : Type*} [DFunLike F Sorts (fun t => M t → N t)]
variable [PerSortEquivLike F M N] [StrongHomClass L F M N] (g : F)

@[simp]
theorem realize_boundedFormula {σ} (φ : L.BoundedFormula α σ) {v : α →ₛ M}
    {xs : σ.Interpret M} : φ.Realize (g ∘ₛ v) (g <$>ₛ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal =>
    rw [BoundedFormula.Realize, BoundedFormula.Realize, SortedTuple.get_map,
      ← Fam.sumComp_elim, HomClass.realize_term, HomClass.realize_term]
    refine Function.Injective.eq_iff (Function.HasLeftInverse.injective ⟨?_,?_⟩ )
    · exact SortedTuple.map (PerSortEquivLike.inv g)
    · rw [Function.leftInverse_iff_comp]
      funext xs
      rw [Function.comp, ←  SortedTuple.comp_map, Function.id_def]
      have : (fun t ↦ PerSortEquivLike.inv g t ∘ g t) = fun _ => id := by
        funext t
        rw [← Function.leftInverse_iff_comp]
        apply PerSortEquivLike.left_inv g
      simp [this]
  | rel =>
    rename_i σ' σ R ts
    rw [BoundedFormula.Realize, BoundedFormula.Realize, SortedTuple.get_map,
         ← Fam.sumComp_elim g, HomClass.realize_term]
    exact StrongHomClass.map_rel g _ _
  | imp _ _ ih₁ ih₂ => rw [BoundedFormula.Realize, ih₁, ih₂, BoundedFormula.Realize]
  | all η φ ih₃ =>
    rw [BoundedFormula.Realize, BoundedFormula.Realize]
    constructor
    · intro h ys
      have h' := h (g <$>ₛ ys)
      rw [← SortedTuple.map_prod, ih₃] at h'
      exact h'
    · intro h ys
      have h' := h (PerSortEquivLike.inv g <$>ₛ ys)
      rw [← ih₃, SortedTuple.map_prod, ← SortedTuple.comp_map,
        PerSortEquivLike.apply_inv_apply_fun g, map_id] at h'
      exact h'

@[simp]
theorem realize_formula (φ : L.Formula α) {v : α →ₛ M} :
    φ.Realize (g ∘ₛ v) ↔ φ.Realize v := by
  rw [Formula.Realize, Formula.Realize, ← realize_boundedFormula g φ, iff_eq_eq,
    Unique.eq_default (⇑g <$>ₛ default)]

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

namespace Relations

open BoundedFormula
/-
variable {s : Sorts} {r : L.Relations [s,s]}

@[simp]
theorem realize_reflexive : M ⊨ r.reflexive ↔ Reflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => realize_rel₂

@[simp]
theorem realize_irreflexive : M ⊨ r.irreflexive ↔ Irreflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => not_congr realize_rel₂

@[simp]
theorem realize_symmetric : M ⊨ r.symmetric ↔ Symmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr realize_rel₂ realize_rel₂

@[simp]
theorem realize_antisymmetric :
    M ⊨ r.antisymmetric ↔ AntiSymmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ Iff.rfl)

@[simp]
theorem realize_transitive : M ⊨ r.transitive ↔ Transitive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ =>
      forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ realize_rel₂)

@[simp]
theorem realize_total : M ⊨ r.total ↔ Total fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => realize_sup.trans (or_congr realize_rel₂ realize_rel₂)
-/
end Relations

section Cardinality
/-
variable (L)
@[simp]
theorem Sentence.realize_cardGe (n) : M ⊨ Sentence.cardGe L n ↔ ↑n ≤ #M := by
  rw [← lift_mk_fin, ← lift_le.{0}, lift_lift, lift_mk_le, Sentence.cardGe, Sentence.Realize,
    BoundedFormula.realize_exs]
  simp_rw [BoundedFormula.realize_foldr_inf]
  simp only [Function.comp_apply, List.mem_map, Prod.exists, Ne, List.mem_product,
    List.mem_finRange, forall_exists_index, and_imp, List.mem_filter, true_and]
  refine ⟨?_, fun xs => ⟨xs.some, ?_⟩⟩
  · rintro ⟨xs, h⟩
    refine ⟨⟨xs, fun i j ij => ?_⟩⟩
    contrapose! ij
    have hij := h _ i j (by simpa using ij) rfl
    simp only [BoundedFormula.realize_not, Term.realize, BoundedFormula.realize_bdEqual,
      Sum.elim_inr] at hij
    exact hij
  · rintro _ i j ij rfl
    simpa using ij

@[simp]
theorem model_infiniteTheory_iff : M ⊨ L.infiniteTheory ↔ Infinite M := by
  simp [infiniteTheory, infinite_iff, aleph0_le]

instance model_infiniteTheory [h : Infinite M] : M ⊨ L.infiniteTheory :=
  L.model_infiniteTheory_iff.2 h

@[simp]
theorem model_nonemptyTheory_iff : M ⊨ L.nonemptyTheory ↔ Nonempty M := by
  simp only [nonemptyTheory, Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    Sentence.realize_cardGe, Nat.cast_one, one_le_iff_ne_zero, mk_ne_zero_iff]

instance model_nonempty [h : Nonempty M] : M ⊨ L.nonemptyTheory :=
  L.model_nonemptyTheory_iff.2 h

theorem model_distinctConstantsTheory {M : Type w} [L[[α]].MSStructure M] (s : Set α) :
    M ⊨ L.distinctConstantsTheory s ↔ Set.InjOn (fun i : α => (L.con i : M)) s := by
  simp only [distinctConstantsTheory, Theory.model_iff, Set.mem_image,
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

theorem card_le_of_model_distinctConstantsTheory (s : Set α) (M : Type w) [L[[α]].MSStructure M]
    [h : M ⊨ L.distinctConstantsTheory s] : Cardinal.lift.{w} #s ≤ Cardinal.lift.{u'} #M :=
  lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsTheory s).1 h)⟩⟩
-/
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

/-
theorem nonempty_iff (h : M ≅[L] N) : (∀ s, Nonempty (M s)) ↔ (∀ s, Nonempty (N s)) :=
  (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans (model_nonemptyTheory_iff L))

theorem nonempty [Mn : Nonempty M] (h : M ≅[L] N) : Nonempty N :=
  h.nonempty_iff.1 Mn

theorem infinite_iff (h : M ≅[L] N) : Infinite M ↔ Infinite N :=
  (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))

theorem infinite [Mi : Infinite M] (h : M ≅[L] N) : Infinite N :=
  h.infinite_iff.1 Mi
-/
end ElementarilyEquivalent

end MSLanguage

end MSFirstOrder
