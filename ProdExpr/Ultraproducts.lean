/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import ProdExpr.Quotients
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Ultrafilter.Defs
import ProdExpr.SemanticTactics

/-!
# Ultraproducts and Łoś's Theorem

## Main Definitions

- `FirstOrder.Language.Ultraproduct.Structure` is the ultraproduct structure on `Filter.Product`.

## Main Results

- Łoś's Theorem: `FirstOrder.Language.Ultraproduct.sentence_realize`. An ultraproduct models a
  sentence `φ` if and only if the set of structures in the product that model `φ` is in the
  ultrafilter.

## Tags

ultraproduct, Los's theorem
-/

universe u v w z

open MSFirstOrder Filter Fam

variable {Sorts : Type z} {ι : Type*} (M : ι → Fam Sorts) (F : Filter ι)

namespace MSFirstOrder

namespace MSLanguage

open MSStructure Fam Signature Interpret

variable {L : MSLanguage.{u, v} Sorts} [i: ∀ a, L.MSStructure (M a)]

/-! ## Reduced Products

The reduced product construction works for any filter, not just ultrafilters.
The ultrafilter property is only needed for Łoś's theorem.
-/

namespace MSStructure

/-- The reduced product setoid: two functions are equivalent iff they're eventually equal. -/
@[reducible]
def ReducedProductSetoid : MSSetoid (piFam M) :=
  MSSetoid.mk (fun s => F.productSetoid (fun a => M a s))

/-- The reduced product carrier: the quotient of product functions by eventual equality. -/
abbrev ReducedProduct := MSQuotient (ReducedProductSetoid (M := M) (F := F))

/-- The projection FamMap from a product to a coordinate -/
def proj {M : ι → Fam Sorts} (a : ι) : piFam M →ₛ M a := ⟨fun _ x => x a⟩

namespace ReducedProduct

/-- The quotient map into the reduced product. -/
abbrev quot {M : ι → Fam Sorts} : piFam M →ₛ ReducedProduct M F :=
  MSQuotient.mk (ReducedProductSetoid M F)

lemma interpret_equiv_iff_exists_mem_filter {σ : Signature Sorts}
    (x y : (piFam M) [^] σ) :
    letI : MSSetoid (piFam M) := ReducedProductSetoid M F
    x ≈ y ↔
      ∃ A ∈ F, ∀ a ∈ A, ∀ s (v : σ.Idx s), x.get s v a = y.get s v a := by
  constructor
  · intro hxy
    refine ⟨⋂ is : Sigma σ.IdxFam, {a : ι | x.get is.1 is.2 a = y.get is.1 is.2 a}, ?_, ?_⟩
    · refine iInter_mem.2 ?_
      intro is
      have hcoord :=
        (Interpret.interpret_equiv_iff
          (R := ReducedProductSetoid (M := M) (F := F))
          (xs := x) (ys := y)).1 hxy is.1 is.2
      change {a : ι | x.get is.1 is.2 a = y.get is.1 is.2 a} ∈ F
      simpa [Filter.Eventually] using hcoord
    · intro a ha s v
      exact (Set.mem_iInter.1 ha) ⟨s, v⟩
  · rintro ⟨A, hA, hpoint⟩
    refine (Interpret.interpret_equiv_iff
      (R := ReducedProductSetoid (M := M) (F := F))
      (xs := x) (ys := y)).2 ?_
    intro s v
    change {a : ι | x.get s v a = y.get s v a} ∈ F
    refine mem_of_superset hA ?_
    intro a ha
    exact hpoint a ha s v

@[simp]
lemma proj_map_eq_fromGet {σ : Signature Sorts} (x : (piFam M) [^] σ) (a : ι) :
    proj a <$>ₛ x =
      Interpret.fromGet (⟨fun s v => x.get s v a⟩ : σ.IdxFam →ₛ M a) := by
  ext s v : 1
  simp_all only [get_map, FamMap.comp_apply', fromGet_get, FamMap.mk_apply]
  rfl

@[simp]
lemma proj_comp_get {σ : Signature Sorts} (x : (piFam M) [^] σ) (a : ι) :
    (proj a ∘ₛ x.get : σ.IdxFam →ₛ M a) =
      (⟨fun s v => x.get s v a⟩ : σ.IdxFam →ₛ M a) := by
  ext s v
  rfl

instance prestructure :
    L.MSPrestructure (ReducedProductSetoid (M := M) (F := F)) :=
  { (ReducedProductSetoid (M := M) (F := F)) with
    toMSStructure :=
      { funMap := fun {σ} s f x a =>
            funMap f (proj a <$>ₛ x)
        RelMap := fun {_} r x =>
            ∀ᶠ a : ι in F, RelMap r (proj a <$>ₛ x)}
    fun_equiv := fun {s} σ f x y xy => by
      letI : MSSetoid (piFam M) := ReducedProductSetoid M F
      rcases (interpret_equiv_iff_exists_mem_filter (M := M) (F := F) (σ := σ) x y).1 xy with
        ⟨A, hA, hpoint⟩
      change ∀ᶠ a : ι in F, funMap f (proj a <$>ₛ x) = funMap f (proj a <$>ₛ y)
      rw [Filter.Eventually]
      refine mem_of_superset hA ?_
      intro a ha
      simp_all only [interpret_equiv_iff, proj_map_eq_fromGet, Set.mem_setOf_eq]
    rel_equiv := fun {σ} r x y xy => by
      letI : MSSetoid (piFam M) := ReducedProductSetoid M F
      rcases (interpret_equiv_iff_exists_mem_filter (M := M) (F := F) (σ := σ) x y).1 xy with
        ⟨A, hA, hpoint⟩
      change
        (∀ᶠ a : ι in F, RelMap r (proj a <$>ₛ x)) =
          (∀ᶠ a : ι in F, RelMap r (proj a <$>ₛ y))
      apply propext
      constructor
      · intro hx
        refine mem_of_superset (inter_mem hx hA) ?_
        intro a ha; obtain ⟨left, right⟩ := ha
        simp_all only [interpret_equiv_iff, proj_map_eq_fromGet, Set.mem_setOf_eq]
      · intro hy
        refine mem_of_superset (inter_mem hy hA) ?_
        intro a ha; rcases ha with ⟨hyA, haA⟩
        simp_all only [interpret_equiv_iff, proj_map_eq_fromGet, Set.mem_setOf_eq]
  }


noncomputable
instance «structure» : L.MSStructure (ReducedProduct (M := M) (F := F)) :=
  MSLanguage.quotientMSStructure (L := L) (ps := prestructure M F)

end ReducedProduct

end MSStructure

/-! ## Ultraproducts

The ultraproduct is the reduced product with respect to an ultrafilter.
-/

variable (u : Ultrafilter ι)

/-- The ultraproduct of a family of structures, as a reduced product over an ultrafilter. -/
abbrev Ultraproduct : Fam Sorts := ReducedProduct M (u : Filter ι)

noncomputable
instance Ultraproduct.structure : L.MSStructure (Ultraproduct M u) :=
  ReducedProduct.structure M u

namespace Ultraproduct

variable {M} {u}

instance instPiFamStructure : L.MSStructure (piFam M) :=
  (ReducedProduct.prestructure M (u : Filter ι)).toMSStructure



-- The key lemmas for Łoś's theorem
-- These connect realization in the ultraproduct to pointwise realization

theorem funMap_cast {σ : Signature Sorts} {t : Sorts}
    (f : L.Functions σ t) (x : (piFam M) [^] σ) :
    @funMap _ L _ (Ultraproduct.structure M u) σ t f
      ((ReducedProduct.quot u) <$>ₛ x) =
      Quotient.mk (s := (u : Filter ι).productSetoid (fun a => M a t))
        (@funMap _ L _ (ReducedProduct.prestructure M (u : Filter ι)).toMSStructure σ t f x) := by
  simpa [ReducedProduct.quot] using
    (funMap_quotient_mk' (L := L) (ps := ReducedProduct.prestructure M (u : Filter ι))
      (S := ReducedProductSetoid M (u : Filter ι)) f x)

theorem term_realize_cast {β : Fam Sorts} {σ : Signature Sorts}
    (x : β →ₛ (piFam M)) (t : L.Term β σ) :
    let S := ReducedProductSetoid M (u : Filter ι)
    Term.realize (MSQuotient.mk S ∘ₛ x) t =
    Interpret.toQuot (R := S)
      (t.realize (i := (ReducedProduct.prestructure M (u : Filter ι)).toMSStructure) x) := by
  intro S
  rw [Term.realize_quotient_mk' (ps := ReducedProduct.prestructure M (u : Filter ι))]

/-- Ultraproduct equality for interpretations: two tuples of quotients are equal
    iff they're equal componentwise (which means eventually equal pointwise). -/
theorem ultraproduct_interpret_eq_iff {σ : Signature Sorts}
    (x y : (piFam M) [^] σ) :
    Interpret.toQuot (R := ReducedProductSetoid M (u : Filter ι)) x =
    Interpret.toQuot (R := ReducedProductSetoid M (u : Filter ι)) y ↔
    ∀ s (v : σ.Idx s), ∀ᶠ a in u, x.get s v a = y.get s v a := by
  simp only [Interpret.ext_iff, Interpret.get_toQuot]
  constructor
  · intro h s v
    simpa only using Quotient.exact (h s v)
  · intro h s v
    apply Quotient.sound
    exact h s v


@[simp]
lemma term_realize_get_apply
  {β : Fam Sorts} {σ : Signature Sorts}
  (x : β →ₛ (piFam M)) (t : L.Term β σ)
  (a : ι) (s : Sorts) (v : σ.Idx s) :
  letI : L.MSStructure (piFam M) := (ReducedProduct.prestructure M (u : Filter ι)).toMSStructure
  (t.realize x).get s v a = (t.realize (proj a ∘ₛ x)).get s v := by
  induction t generalizing s with
  | nil => cases v
  | var =>
      simp_all only [Term.realize_var]; cases v; rfl
  | func f t ih =>
      cases v
      let xa : β →ₛ M a := proj a ∘ₛ x
      have hleafToTarget :
          Interpret.fromGet
            (⟨fun i w =>
                (Term.realize
                  (i := (ReducedProduct.prestructure M (u : Filter ι)).toMSStructure) x
                  (t.getLeafTerm i w)) a⟩ :
              _ →ₛ M a) =
          Term.realize xa t := by
        ext s' w
        simpa [Interpret.fromGet_get, Term.realize_getLeafTerm, xa] using ih s' w
      simp [Term.realize, funMap]
      congr
  --      congrArg (fun z => funMap f z) hleafToTarget
  | prod t₁ t₂ ih₁ ih₂ =>
      simp only [Term.realize]
      cases v with
      | left v' =>
          simpa only [get_left] using ih₁ s v'
      | right v' =>
          simpa only [get_right] using ih₂ s v'

/-- Two term realizations are equal in the ultraproduct iff they're eventually pointwise equal. -/
theorem term_realize_eq_iff {β : Fam Sorts} {σ : Signature Sorts}
    (α : β →ₛ piFam M) (t₁ t₂ : L.Term β σ) :
    Term.realize (ReducedProduct.quot u ∘ₛ α) t₁ =
    Term.realize (ReducedProduct.quot u ∘ₛ α) t₂ ↔
    ∀ᶠ a : ι in u, t₁.realize (proj a ∘ₛ α) = t₂.realize (proj a ∘ₛ α) := by
  simp only [term_realize_cast, ultraproduct_interpret_eq_iff, term_realize_get_apply]
  constructor
  · case mp =>
    intro h
    have hall :
    ∀ᶠ a : ι in (u : Filter ι),
      ∀ is : Sigma σ.IdxFam,
        (t₁.realize (i := (ReducedProduct.prestructure M (u : Filter ι)).toMSStructure) α).get
        is.1 is.2 a =
        (t₂.realize (i := (ReducedProduct.prestructure M (u : Filter ι)).toMSStructure) α).get
        is.1 is.2 a := by
      simp only [Filter.Eventually, term_realize_get_apply, Ultrafilter.mem_coe]
      refine
        mem_of_superset
          (iInter_mem.2
            (fun is : Sigma σ.IdxFam => by simpa only [Filter.Eventually] using (h is.1 is.2))) ?_
      intro a ha is
      have : a ∈ {a : ι | _} := (Set.mem_iInter.mp ha) is
      simpa only using this
    refine hall.mono ?_
    intro a ha
    ext s v
    let h' := ha ⟨s, v⟩
    simp only [term_realize_get_apply] at h'
    exact h'
  · case mpr =>
    intro h s v
    rw[Filter.Eventually] at *
    refine mem_of_superset h ?_
    simp_all only [Set.setOf_subset_setOf, implies_true]

@[simp]
lemma fromGet_realize_getLeafTerm {β : Fam Sorts} {τ : Signature Sorts}
    {a : ι} (x : β →ₛ M a) (ts : L.Term β τ) :
    Interpret.fromGet (⟨fun s w => Term.realize x (ts.getLeafTerm s w)⟩ : τ.IdxFam →ₛ M a)
      =
    Term.realize x ts := by
  ext s w
  simp_all only [fromGet_get, FamMap.mk_apply, Term.realize_getLeafTerm]

/-- Relation realization in the ultraproduct is equivalent to eventual pointwise realization. -/
theorem rel_term_realize_iff {β : Fam Sorts} {τ : Signature Sorts}
    (x : β →ₛ (piFam M)) (R : L.Relations τ) (ts : L.Term β τ) :
    RelMap R (Term.realize (ReducedProduct.quot u ∘ₛ x) ts) ↔
    ∀ᶠ a : ι in u, RelMap R (Term.realize (proj a ∘ₛ x) ts) := by
  have hterm :
      Term.realize (ReducedProduct.quot (M := M) u ∘ₛ x) ts
        =
      Interpret.toQuot (R := ReducedProductSetoid M (u : Filter ι))
        (ts.realize
          (i := (ReducedProduct.prestructure M (u : Filter ι)).toMSStructure)
          x) := by
    simpa [ReducedProduct.quot] using
      (term_realize_cast (M := M) (u := u) (x := x) (t := ts))
  rw [hterm]
  rw [relMap_quotient_mk']
  constructor <;>
  intro h <;>
  refine h.mono ?_ <;>
  intro a ha <;>
  simpa using ha


@[simp]
lemma term_realize_sum {β : Fam Sorts} {τ η : Signature Sorts}
    (t : L.Term (β ⊕ₛ η.IdxFam) τ) (f : β →ₛ (piFam M))
    (xs : (piFam M) [^] η) :
    let S := ReducedProductSetoid M (u : Filter ι)
    t.realize (sumElim (ReducedProduct.quot u ∘ₛ f) ((MSQuotient.mk S) <$>ₛ xs).get)
    = t.realize (ReducedProduct.quot u ∘ₛ (sumElim f xs.get )) := by
    intro S
    congr 1
    ext s b
    cases b with
    | inl b => rfl
    | inr w =>
        simp_all only [get_map, sumElim_eval_r, FamMap.comp_apply', S]
        rfl

variable [∀ a : ι, ∀ s, Nonempty (M a s)]

theorem boundedFormula_realize_cast {β : Fam Sorts} {η : Signature Sorts}
    (φ : L.BoundedFormula β η)
    (f : β →ₛ (piFam M))
    (v : (piFam M) [^] η) :
    let S := ReducedProductSetoid M u
    φ.Realize (i:= Ultraproduct.structure M u)
      (ReducedProduct.quot (M:= M) u ∘ₛ f) ((MSQuotient.mk S) <$>ₛ v) ↔
      ∀ᶠ a : ι in u, φ.Realize (proj a ∘ₛ f)
        (Interpret.fromGet (proj a ∘ₛ v.get)) := by
  intro S
  have h_aeq : ∀ a : ι,
      (proj a ∘ₛ sumElim f v.get) =
        sumElim (proj a ∘ₛ f) (proj a ∘ₛ v.get : η.IdxFam →ₛ M a) := by
    intro a
    simpa using (sumComp_elim (f := proj a) (g := f) (h := v.get))
  induction φ  with
  | falsum => simp only [BoundedFormula.Realize, Filter.eventually_const]
  | @equal σ τ t₁ t₂ =>
    simp only [BoundedFormula.Realize, Interpret.fromGet_get]
    repeat rw[term_realize_sum]
    rw[term_realize_eq_iff]
    simp_all only [ReducedProduct.proj_comp_get]
  | @rel σ τ R ts =>
    -- The relation case: uses the definition of RelMap in the ultraproduct
    simp only [BoundedFormula.Realize, Interpret.fromGet_get]
    let f' : (β ⊕ₛ σ.IdxFam) →ₛ (piFam M) :=
      sumElim f v.get
    have hsum : sumElim (ReducedProduct.quot u ∘ₛ f)
        ( (MSQuotient.mk S) <$>ₛ v).get =
          ReducedProduct.quot u ∘ₛ f' := by
      ext s b
      cases b with
      | inl b => rfl
      | inr w =>
          simp_all only [ReducedProduct.proj_comp_get, get_map, sumElim_eval_r, FamMap.comp_apply',
            S, f']
          rfl
    rw [hsum]
    have hrel := rel_term_realize_iff (M := M) (u := u) (x := f') (R := R) (ts := ts)
    constructor
    · intro h
      have h' := hrel.mp h
      refine h'.mono ?_
      intro a ha
      simpa [f', h_aeq a] using ha
    · intro h
      have h' : ∀ᶠ a : ι in u, RelMap R (Term.realize (proj a ∘ₛ f') ts) := by
        refine h.mono ?_
        intro a ha
        simpa [f', h_aeq a] using ha
      exact hrel.mpr h'
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [BoundedFormula.Realize]
    rw [Ultrafilter.eventually_imp]
    simp_all only [implies_true]
  | @all η' τ φ ih =>
    simp only [BoundedFormula.Realize]
    constructor
    · intro hall
      by_contra hne
      -- For ultrafilter: ¬(∀ᶠ a, P a) ↔ ∀ᶠ a, ¬P a
      have hfreq : ∀ᶠ a in u, ∃ y : M a[^]τ, ¬φ.Realize (proj a ∘ₛ f)
          ⟨Interpret.fromGet (proj a ∘ₛ v.get : η'.IdxFam →ₛ M a), y⟩ := by
        rw [← Ultrafilter.eventually_not] at hne
        push Not at hne
        exact hne
      classical
      let y : ∀ a, M a[^]τ := fun a =>
        if h : ∃ (y : M a[^]τ), ¬φ.Realize (proj a ∘ₛ f)
            ⟨Interpret.fromGet (proj a ∘ₛ v.get : η'.IdxFam →ₛ M a), y⟩
        then Classical.choose h
        else Interpret.fromGet (⟨fun s _ => Classical.choice inferInstance⟩ : τ.IdxFam →ₛ M a)
      -- Form ultraproduct element from y
      let yrep : (piFam M)[^]τ := Interpret.fromGet (⟨fun s w a => (y a).get s w⟩)
      let z : (Ultraproduct M u)[^]τ := (ReducedProduct.quot u) <$>ₛ yrep
      -- Apply hall to z
      specialize hall z
      -- Use IH: need to prove the h_aeq condition for (v, yrep)
      let vyrep : (piFam M)[^](η' ⨯ τ) := (v, yrep)
      have h_aeq_yrep : ∀ a : ι,
          (proj a ∘ₛ sumElim f vyrep.get) =
            sumElim (proj a ∘ₛ f)
              (proj a ∘ₛ vyrep.get : (η' ⨯ τ).IdxFam →ₛ M a) := by
        intro a
        simpa using (sumComp_elim (f := proj a) (g := f) (h := vyrep.get))
      have hall' := (ih vyrep h_aeq_yrep).mp hall
      -- But by construction, ∀ᶠ a in u, ¬φ.Realize ... (y a)
      have hcontra : ∀ᶠ a in u, ¬φ.Realize (proj a ∘ₛ f)
          ⟨Interpret.fromGet (proj a ∘ₛ v.get : η'.IdxFam →ₛ M a), y a⟩ := by
        refine hfreq.mono ?_
        intro a ha
        simp only [y]
        rw [dif_pos ha]
        exact Classical.choose_spec ha
      -- Simplify: fromGet (... vyrep.get ...) = ⟨fromGet (...v...), y a⟩
      have hctx : ∀ a, Interpret.fromGet (proj a ∘ₛ vyrep.get : (η' ⨯ τ).IdxFam →ₛ M a) =
          ⟨Interpret.fromGet (proj a ∘ₛ v.get : η'.IdxFam →ₛ M a), y a⟩ := by
        intro a
        have hprod :
            Interpret.fromGet (proj a ∘ₛ vyrep.get : (η' ⨯ τ).IdxFam →ₛ M a) =
              ⟨Interpret.fromGet (proj a ∘ₛ v.get : η'.IdxFam →ₛ M a),
                Interpret.fromGet (proj a ∘ₛ yrep.get : τ.IdxFam →ₛ M a)⟩ := by
          simpa [vyrep] using
            (Interpret.fromGet_prod (σ := η') (τ := τ)
              (v := (proj a ∘ₛ vyrep.get : (η' ⨯ τ).IdxFam →ₛ M a)))
        have hy :
            Interpret.fromGet (⟨fun s w => yrep.get s w a⟩ : τ.IdxFam →ₛ M a) = y a := by
          ext s w
          simp only [fromGet_get, FamMap.mk_apply, yrep]
        simpa [hy] using hprod
      simp only [hctx] at hall'
      -- Now hall' and hcontra are contradictory
      have hboth := Filter.eventually_and.mpr ⟨hall', hcontra⟩
      simp only [and_not_self, Filter.eventually_false_iff_eq_bot] at hboth
      exact absurd hboth (Filter.NeBot.ne (Ultrafilter.neBot (f := u)))
    · -- Backward: if eventually ∀ y, φ holds, then ∀ z in ultraproduct, φ holds
      intro hev z
      -- Use Interpret.choice to get a representative for z
      let zrep := (Interpret.choice (R := S) z).out
      have hz : Interpret.toQuot (R := S) zrep = z := Interpret.toQuot_out_choice (R := S) z
      -- z = map quot zrep
      have hz' : z = (ReducedProduct.quot u) <$>ₛ zrep := by
        simpa only [ReducedProduct.quot] using congrArg (fun w => w) hz.symm
      rw [hz']
      -- Use IH with extended context (v, zrep)
      let vzrep : (piFam M)[^](η' ⨯ τ) := (v, zrep)
      have h_aeq_zrep : ∀ a : ι,
          (proj a ∘ₛ sumElim f vzrep.get) =
            sumElim (proj a ∘ₛ f)
              (proj a ∘ₛ vzrep.get : (η' ⨯ τ).IdxFam →ₛ M a) := by
        intro a
        simpa using (sumComp_elim (f := proj a) (g := f) (h := vzrep.get))
      -- Show that map distributes: (map quot v, map quot zrep) = map quot (v, zrep)
      have hmap : ((MSQuotient.mk S) <$>ₛ v, (ReducedProduct.quot u) <$>ₛ zrep) =
          (MSQuotient.mk S) <$>ₛ vzrep := by rfl
      rw [hmap]
      apply (ih vzrep h_aeq_zrep).mpr
      -- Goal: ∀ᶠ a in u, φ.Realize ... (fromGet (... vzrep.get ...))
      refine hev.mono ?_
      intro a ha
      -- Simplify the fromGet
      have hctx : Interpret.fromGet (proj a ∘ₛ vzrep.get : (η' ⨯ τ).IdxFam →ₛ M a) =
          ⟨Interpret.fromGet (proj a ∘ₛ v.get : η'.IdxFam →ₛ M a),
            Interpret.fromGet (proj a ∘ₛ zrep.get : τ.IdxFam →ₛ M a)⟩ := by
        simpa [vzrep] using
          (Interpret.fromGet_prod (σ := η') (τ := τ)
            (v := (proj a ∘ₛ vzrep.get : (η' ⨯ τ).IdxFam →ₛ M a)))
      rw [hctx]
      exact ha _

theorem realize_formula_cast {β : Fam Sorts} (φ : L.Formula β)
    (f : β →ₛ (piFam M)) :
    let S := ReducedProductSetoid M (u : Filter ι)
    @Formula.Realize _ L _ (Ultraproduct.structure (M := M) (u := u)) β φ (MSQuotient.mk S ∘ₛ f) ↔
      ∀ᶠ a : ι in u, φ.Realize (proj a ∘ₛ f) := by
  intro S
  simp only [Formula.Realize]
  have h := boundedFormula_realize_cast (u := u) φ f
    (default : (piFam M)[^]Signature.nil)
  simp only [Interpret.fromGet] at h ⊢
  convert h using 2

/-- **Łoś's Theorem** (multisorted version): A sentence is true in an ultraproduct if and only if
the set of structures it is true in is in the ultrafilter. -/
theorem sentence_realize (φ : L.Sentence) :
    Ultraproduct M u ⊨ φ ↔ ∀ᶠ a : ι in u, M a ⊨ φ := by
  have h :=
    realize_formula_cast (M := M) (u := u)
      (β := Fam.EmptyFam) (φ := φ)
      (f := (default : Fam.EmptyFam →ₛ piFam M))
  have hleft :
      (MSQuotient.mk (ReducedProductSetoid M (u : Filter ι))
        ∘ₛ (default : Fam.EmptyFam →ₛ piFam M))
      = (default : Fam.EmptyFam →ₛ Ultraproduct M u) := by
    ext s x
    exact (False.elim (by cases x))
  have hright :
      (∀ᶠ a : ι in u,
          Formula.Realize φ
            (proj a ∘ₛ (default : Fam.EmptyFam →ₛ piFam M)))
      ↔
      (∀ᶠ a : ι in u, Formula.Realize φ (default : Fam.EmptyFam →ₛ M a)) := by
    have hdefault : ∀ a : ι,
        (proj a ∘ₛ (default : Fam.EmptyFam →ₛ piFam M))
          =
        (default : Fam.EmptyFam →ₛ M a) := by
      intro a
      ext s x
      exact (False.elim (by cases x))
    constructor
    · intro h
      refine h.mono ?_
      intro a ha
      simpa [hdefault a] using ha
    · intro h
      refine h.mono ?_
      intro a ha
      simpa [hdefault a] using ha
  have h' :
      Formula.Realize φ (default : Fam.EmptyFam →ₛ Ultraproduct M u)
      ↔
      (∀ᶠ a : ι in u,
        Formula.Realize φ
          (proj a ∘ₛ (default : Fam.EmptyFam →ₛ piFam M))) := by
    simpa [hleft] using h
  exact (h'.trans hright)

instance instNonemptyUltraproduct (s : Sorts) :
    Nonempty (MSQuotient (ReducedProductSetoid M (u : Filter ι)) s) :=
  ⟨MSQuotient.mk _ s (fun _ => Classical.choice inferInstance)⟩

end Ultraproduct

end MSLanguage

end MSFirstOrder
