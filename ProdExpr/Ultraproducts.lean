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

variable {L : MSLanguage.{u, v} Sorts} [i : ∀ a, L.MSStructure (M a)]

/-! ## Reduced Products

The reduced product construction works for any filter, not just ultrafilters.
The ultrafilter property is only needed for Łoś's theorem.
-/

namespace MSStructure

/-- The reduced product setoid: two functions are equivalent iff they're eventually equal. -/
@[reducible]
instance ReducedProductSetoid : MSSetoid (piFam M) :=
  MSSetoid.mk (fun s => F.productSetoid (fun a => M a s))

/-- The reduced product carrier: the quotient of product functions by eventual equality. -/
abbrev ReducedProduct := MSQuotient (ReducedProductSetoid (M := M) (F := F))

def pi_lift {M : ι → Fam Sorts} : {σ : Signature Sorts} → (piFam M) [^] σ →  (Π a, M a [^] σ)
  | nil => fun _ _ ↦ PUnit.unit
  | of _ => id
  | prod _ _ => fun i j ↦ ⟨pi_lift i.1 j, pi_lift i.2 j⟩

def pi_lift_inv {M : ι → Fam Sorts} : {σ : Signature Sorts} → (Π a, M a [^] σ) → (piFam M) [^] σ
  | nil => fun _ ↦ PUnit.unit
  | of _ => id
  | prod _ _ => fun pi ↦ ⟨pi_lift_inv (fun a ↦ (pi a).1), pi_lift_inv (fun a ↦ (pi a).2)⟩

lemma get_pi_lift {M : ι → Fam Sorts} {σ : Signature Sorts} {s : Sorts} (x : piFam M [^] σ)
      (v : σ.Idx s) (i : ι) :
    x.get _ v i = (pi_lift x i).get _ v := by
  induction σ with
  | nil =>
    cases v
  | of s =>
    cases v
    rfl
  | prod σ₁ σ₂ h₁ h₂ =>
    cases v <;> simp only [Interpret.get, FamMap.mk_apply, pi_lift] <;> simp [h₁, h₂]

lemma pi_lift_LeftInverse (σ : Signature Sorts) :
    Function.LeftInverse (pi_lift (M := M) (σ := σ)) pi_lift_inv := by
  intro i
  induction σ with
  | nil => rfl
  | of _ => rfl
  | prod σ₁ σ₂ h₁ h₂ =>
    simp [pi_lift, pi_lift_inv, h₁, h₂]

lemma pi_lift_RightInverse (σ : Signature Sorts) :
    Function.RightInverse (pi_lift (M := M) (σ := σ)) pi_lift_inv := by
  intro i
  induction σ with
  | nil => rfl
  | of _ => rfl
  | prod σ₁ σ₂ h₁ h₂ =>
    simp [pi_lift, pi_lift_inv, h₁, h₂]

lemma pi_lift_setoid {M : ι → Fam Sorts} {F : Filter ι} {σ : Signature Sorts} {xs ys : (piFam M) [^] σ}
  (h :
    letI : MSSetoid (piFam M) := ReducedProductSetoid M F
    xs ≈ ys) : (F.productSetoid (fun i ↦ M i [^] σ) (pi_lift xs) (pi_lift ys) : Prop) := by
  induction σ with
  | nil => rfl
  | of _ => exact h
  | prod _ _ h₁ h₂ =>
    apply F.mem_of_superset (F.inter_mem (h₁ h.1) (h₂ h.2)) (fun i h' ↦ ?_)
    ext
    · exact h'.1
    · exact h'.2

/-- The projection FamMap from a product to a coordinate -/
def proj {M : ι → Fam Sorts} (a : ι) : piFam M →ₛ M a := ⟨fun _ x => x a⟩

namespace ReducedProduct

/-- The quotient map into the reduced product. -/
abbrev quot {M : ι → Fam Sorts} : piFam M →ₛ ReducedProduct M F :=
  MSQuotient.mk (ReducedProductSetoid M F)

lemma interpret_equiv_iff_eventually_eq {σ : Signature Sorts}
    (x y : (piFam M) [^] σ) :
    letI : MSSetoid (piFam M) := ReducedProductSetoid M F
    x ≈ y ↔
      ∀ᶠ a in F, ∀ s (v : σ.Idx s), x.get s v a = y.get s v a := by
  letI : MSSetoid (piFam M) := ReducedProductSetoid M F
  induction σ with
  | nil => simp
  | of s =>
    constructor
    · intro h
      apply F.mem_of_superset h (fun ai ha ↦ ?_)
      intro s v
      cases v
      exact ha
    · intro h
      apply F.mem_of_superset h (fun ai ha ↦ ?_)
      exact ha s Idx.var
  | prod σ₁ σ₂ h₁ h₂ =>
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp only [prod_equiv (xs := x₁)]
    constructor
    · intro h
      have := And.imp (h₁ x₁ y₁).mp (h₂ x₂ y₂).mp h
      apply F.mem_of_superset (F.inter_mem this.1 this.2)
      intro i h1 s' v
      cases v <;> simp only [Interpret.get, FamMap.mk_apply]
      · exact h1.1 _ _
      · exact h1.2 _ _
    · intro h
      refine And.imp (h₁ x₁ y₁).mpr (h₂ x₂ y₂).mpr
        ⟨
          F.mem_of_superset h (fun i h s v ↦ h s (Idx.left v)),
          F.mem_of_superset h (fun i h s v ↦ h s (Idx.right v))
        ⟩

instance prestructure :
    L.MSPrestructure (ReducedProductSetoid (M := M) (F := F)) :=
  { (ReducedProductSetoid (M := M) (F := F)) with
    toMSStructure := {
        funMap {σ} s f x := fun a =>
            funMap f (pi_lift x a)
        RelMap := fun {_} r x =>
            ∀ᶠ a : ι in F, RelMap r (pi_lift x a)
      }
    fun_equiv := fun {s} σ f x y xy => F.sets_of_superset (pi_lift_setoid xy)
      (fun _ ↦ congrArg ((i _).1 f))
    rel_equiv := fun {σ} r x y xy => by
      simp only [RelMap]
      refine Filter.eventually_congr (F.sets_of_superset (pi_lift_setoid xy) (fun _ ha ↦ ?_))
      rw [Set.mem_setOf, ha]
  }

lemma pi_lift_term_realize {σ τ : Signature Sorts} {β : Fam Sorts} {u : Ultrafilter ι}
    (v : β →ₛ piFam M) (xs : piFam M [^] τ)
    (ts : L.Term (β ⊕ₛ τ.IdxFam) σ) (i : ι):
  pi_lift (@Term.realize _ _ _ (prestructure M u).toMSStructure _ _ (sumElim v xs.get) ts) i =
    Term.realize (sumElim { toFun := fun s b ↦ v s b i } (pi_lift xs i).get) ts := by
  induction ts with
  | nil => rfl
  | var s b =>
    rcases b with _ | xs
    · simp [pi_lift]
    · simp [pi_lift, get_pi_lift]
  | prod t₁ t₂ h₁ h₂ =>
    simp only [pi_lift, Term.realize, Prod.mk.injEq]
    exact ⟨h₁, h₂⟩
  | func f ts h =>
    simp only [pi_lift, Term.realize_func, id_eq, funMap, h]

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

/-- Ultraproduct equality for interpretations: two tuples of quotients are equal
    iff they're equal componentwise (which means eventually equal pointwise). -/
theorem ultraproduct_interpret_eq_iff {σ : Signature Sorts}
    (x y : (piFam M) [^] σ) :
    Interpret.toQuot (R := ReducedProductSetoid M (u : Filter ι)) x =
    Interpret.toQuot (R := ReducedProductSetoid M (u : Filter ι)) y ↔
    ∀ s (v : σ.Idx s), ∀ᶠ a in u, x.get s v a = y.get s v a := by
  simp only [Interpret.ext_iff', Interpret.get_toQuot]
  constructor
  · intro h s v
    simpa only using Quotient.exact (h s v)
  · intro h s v
    apply Quotient.sound
    exact h s v

variable [∀ a : ι, ∀ s, Nonempty (M a s)]

theorem boundedFormula_realize {β : Fam Sorts} {σ : Signature Sorts} (φ : L.BoundedFormula β σ)
    (v : β →ₛ piFam M) (xs : piFam M [^] σ) :
  φ.Realize
      (MSQuotient.mk (ReducedProductSetoid _ u.toFilter) ∘ₛ v)
      (xs.toQuot (R := (ReducedProductSetoid _ u.toFilter)))
    ↔ ∀ᶠ a in u.toFilter, φ.Realize ⟨fun s b ↦ v s b a⟩ (pi_lift xs a) := by
  induction φ with
  | falsum => simp only [BoundedFormula.Realize, u.eventually_const]
  | @equal _ τ t₁ t₂ =>
    letI := (ReducedProductSetoid M u.toFilter)
    have h :
        (sumElim (MSQuotient.mk _ ∘ₛ v) xs.toQuot.get) = MSQuotient.mk _ ∘ₛ (sumElim v xs.get) := by
      ext s b
      cases b
      · rfl
      · simp only [sumElim_eval_r, get_toQuot, FamMap.comp_apply']
        rfl
    simp only [BoundedFormula.Realize]
    induction τ with
    | nil => simp
    | of _ =>
      rw [h]
      simp only [Term.realize_quotient_mk']
      rw [toQuot_eq, ←propext_iff]
      congr
      · simp only [piFam, Interpret, DFunLike.coe]
        ext i
        erw [←ReducedProduct.pi_lift_term_realize]
        rfl
      · simp only [piFam, Interpret, DFunLike.coe]
        ext i
        erw [←ReducedProduct.pi_lift_term_realize]
        rfl
    | prod τ₁ τ₂ h₁ h₂ =>
      cases t₁
      cases t₂
      simp [h₁, h₂]
  | rel R ts =>
    letI := (ReducedProductSetoid M u.toFilter)
    have h :
        (sumElim (MSQuotient.mk _ ∘ₛ v) xs.toQuot.get) = MSQuotient.mk _ ∘ₛ (sumElim v xs.get) := by
      ext s b
      cases b
      · rfl
      · simp only [sumElim_eval_r, get_toQuot, FamMap.comp_apply']
        rfl
    simp only [BoundedFormula.Realize]
    rw [h, Term.realize_quotient_mk']
    simp [RelMap, choice_toQuot, ReducedProduct.pi_lift_term_realize]
  | imp φ ψ hφ hψ =>
    simp only [BoundedFormula.Realize, hφ, hψ, u.eventually_imp]
  | all σ φ h =>
    simp only [BoundedFormula.Realize]
    constructor
    · contrapose!
      intro U
      use (pi_lift_inv
            (fun a ↦
              Classical.epsilon (fun x ↦ ¬φ.Realize (fun s b ↦ v s b a) (pi_lift xs a, x)))).toQuot
                (R := ReducedProductSetoid _ u.toFilter)
      change ¬φ.Realize _  ((MSQuotient.mk _) <$>ₛ(xs, pi_lift_inv _))
      erw [h]
      simp only [Filter.not_eventually, Ultrafilter.frequently_iff_eventually]
      apply u.mem_of_superset U
      intro a ha
      simp only [Set.mem_setOf_eq, pi_lift]
      rw [pi_lift_LeftInverse]
      exact Classical.epsilon_spec ha
    · intro U x
      simp only [weird_needs_name]
      exact (h (xs, MSQuotient.out <$>ₛ x)).mpr (u.mem_of_superset U (fun i h ↦ h _))

theorem formula_realize {β : Fam Sorts} (φ : L.Formula β) (v : β →ₛ piFam M) :
    φ.Realize (MSQuotient.mk (ReducedProductSetoid _ u.toFilter) ∘ₛ v)
      ↔ ∀ᶠ a in (u : Filter ι), φ.Realize ⟨fun s b ↦ v s b a⟩ := by
  simp only [Formula.Realize]
  rw [boundedFormula_realize _ _ PUnit.unit]

theorem sentence_realize (φ : L.Sentence) : Ultraproduct M u ⊨ φ ↔ ∀ᶠ a in u, M a ⊨ φ := by
  simp only [Sentence.Realize]
  have : ∀ a, (default : EmptyFam →ₛ M a) = ⟨fun s b ↦ (default : EmptyFam →ₛ (piFam M)) s b a⟩ := by
    exact fun a ↦ Unique.default_eq _
  simp_rw [this, ←formula_realize φ]
  rw [←propext_iff]
  exact congrArg _ (Subsingleton.elim _ _)

instance instNonemptyUltraproduct (s : Sorts) :
    Nonempty (MSQuotient (ReducedProductSetoid M (u : Filter ι)) s) :=
  ⟨MSQuotient.mk _ s (fun _ => Classical.choice inferInstance)⟩

end Ultraproduct

end MSLanguage

end MSFirstOrder
