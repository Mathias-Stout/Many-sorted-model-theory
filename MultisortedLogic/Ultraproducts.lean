/-
Based on the corresponding Mathlib file by Aaron Anderson
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MultisortedLogic.ElementaryMapsMS
import MultisortedLogic.Quotients
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Ultrafilter.Defs
import MultisortedLogic.SemanticTactics

/-!
# Ultraproducts and Łoś's Theorem

## Main Definitions

- `MSFirstOrder.Language.Ultraproduct.Structure` is the ultraproduct structure on `Filter.Product`.

## Main Results

- Łoś's Theorem: `MSFirstOrder.Language.Ultraproduct.sentence_realize`. An ultraproduct models a
  sentence `φ` if and only if the set of structures in the product that model `φ` is in the
  ultrafilter.

## Tags

ultraproduct, Los's theorem
-/

universe u v w z

namespace MSFirstOrder

variable {Sorts : Type z} {ι : Type*} (M : ι → Fam Sorts) (F : Filter ι)

open Filter Fam

namespace Language

open Structure Fam Signature Interpret

variable {L : Language.{u, v} Sorts} [i : ∀ a, L.Structure (M a)]

/-! ## Reduced Products

The reduced product construction works for any filter, not just ultrafilters.
The ultrafilter property is only needed for Łoś's theorem.
-/

namespace Structure

/-- The reduced product setoid: two functions are equivalent iff they're eventually equal. -/
@[reducible]
def ReducedProductSetoid {Sorts : Type z} {ι : Type*} (M : ι → Fam Sorts) (F : Filter ι)
  : MSSetoid (piFam M) := MSSetoid.mk (fun s => F.productSetoid (fun a => M a s))

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

lemma pi_lift_setoid {M : ι → Fam Sorts} {F : Filter ι} {σ : Signature Sorts}
  {xs ys : (piFam M) [^] σ}
  (h :
    letI : MSSetoid (piFam M) := ReducedProductSetoid M F
    xs ≈ ys) : (F.productSetoid (fun i ↦ M i [^] σ) (pi_lift xs) (pi_lift ys) : Prop) := by
  induction σ with
  | nil => rfl
  | of _ => exact h
  | prod _ _ h₁ h₂ =>
    apply F.mem_of_superset (F.inter_mem (h₁ h.1) (h₂ h.2)) (fun i h' ↦ ?_)
    apply Prod.ext
    · exact h'.1
    · exact h'.2

lemma pi_lift_diag {M : Fam Sorts} {σ : Signature Sorts} {xs : M [^] σ} :
    ∀ (i : ι), pi_lift ((⟨fun _ m _ ↦ m⟩ : M →ₛ piFam fun _ ↦ M) <$>ₛ xs) i = xs := by
  intro i
  induction σ with
  | nil => rfl
  | of _ => rfl
  | prod _ _ h₁ h₂ =>
    exact Prod.ext h₁ h₂

lemma pi_lift_map {M N : ι → Fam Sorts} {σ : Signature Sorts} {xs : piFam M [^] σ} {fi : Π (i : ι),
   M i →ₛ N i} :
    ∀ (i : ι), pi_lift ((⟨fun s xs i ↦ fi i s (xs i)⟩ : piFam M →ₛ piFam N) <$>ₛ xs) i = fi i <$>ₛ
      pi_lift xs i := by
  induction σ with
  | nil =>
    intro i
    rfl
  | of _ =>
    intro i
    rfl
  | prod _ _ h₁ h₂ =>
    intro i
    obtain ⟨x₁, x₂⟩ := xs
    simp only [pi_lift, mapClass_map_prod]
    rw [h₁, h₂]


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
    L.Prestructure (ReducedProductSetoid (M := M) (F := F)) :=
  { (ReducedProductSetoid (M := M) (F := F)) with
    toStructure := {
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
    (ts : L.Term (β ⊕ₛ τ.IdxFam) σ) (i : ι) :
  pi_lift (@Term.realize _ _ _ (prestructure M u).toStructure _ _ (sumElim v xs.get) ts) i =
    Term.realize (sumElim { toFun := fun s b ↦ v s b i } (pi_lift xs i).get) ts := by
  induction ts with
  | nil => rfl
  | var s b =>
    rcases b with b | w
    · rfl
    · exact get_pi_lift _ w i
  | prod t₁ t₂ h₁ h₂ =>
    simp only [pi_lift, Term.realize, Prod.mk.injEq]
    exact ⟨h₁, h₂⟩
  | func f ts h =>
    exact congrArg (funMap f) h

noncomputable
instance «structure» : L.Structure (ReducedProduct (M := M) (F := F)) :=
  Language.quotientStructure (L := L) (ps := prestructure M F)

end ReducedProduct

end Structure

/-! ## Ultraproducts

The ultraproduct is the reduced product with respect to an ultrafilter.
-/

variable (u : Ultrafilter ι)

/-- The ultraproduct of a family of structures, as a reduced product over an ultrafilter. -/
abbrev Ultraproduct : Fam Sorts := ReducedProduct M (u : Filter ι)

noncomputable
instance Ultraproduct.structure : L.Structure (Ultraproduct M u) :=
  ReducedProduct.structure M u

namespace Ultraproduct

variable {M} {u}

@[reducible]
def instPiFamStructure : L.Structure (piFam M) :=
  (ReducedProduct.prestructure M (u : Filter ι)).toStructure

/-- Ultraproduct equality for interpretations: two tuples of quotients are equal
    iff they're equal componentwise (which means eventually equal pointwise). -/
theorem ultraproduct_interpret_eq_iff {σ : Signature Sorts}
    (x y : (piFam M) [^] σ) :
    x.toQuot (R := ReducedProductSetoid M (u : Filter ι))  =
    y.toQuot (R := ReducedProductSetoid M (u : Filter ι)) ↔
    ∀ s (v : σ.Idx s), ∀ᶠ a in u, x.get s v a = y.get s v a := by
  simp only [Interpret.ext_iff', Interpret.get_toQuot]
  constructor
  · intro h s v
    exact Quotient.exact (h s v)
  · intro h s v
    apply Quotient.sound
    exact h s v

variable [∀ a : ι, ∀ s, Nonempty (M a s)]

theorem boundedFormula_realize {β : Fam Sorts} {σ : Signature Sorts} (φ : L.BoundedFormula β σ)
    (v : β →ₛ piFam M) (xs : piFam M [^] σ) :
  φ.Realize
      (MSQuotient.mk _ ∘ₛ v)
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
      · simp only [sumElim_eval_r, get_toQuot]
        rfl
    simp only [BoundedFormula.Realize]
    induction τ with
    | nil => simp
    | of _ =>
      rw [h]
      simp only [Term.realize_quotient_mk']
      rw [toQuot_eq, ←propext_iff]
      congr <;>
        simp only [piFam, Interpret, DFunLike.coe] <;>
        ext i <;>
        erw [←ReducedProduct.pi_lift_term_realize] <;>
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
      · simp only [sumElim_eval_r, get_toQuot]
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
      refine u.mem_of_superset U (fun a ha ↦ ?_)
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
  have : ∀ a, (default : EmptyFam →ₛ M a)
      = ⟨fun s b ↦ (default : EmptyFam →ₛ (piFam M)) s b a⟩ := by
    exact fun a ↦ Unique.default_eq _
  simp_rw [this, ←formula_realize φ]
  rw [←propext_iff]
  exact congrArg _ (Subsingleton.elim _ _)

instance instNonemptyUltraproduct (s : Sorts) :
    Nonempty (MSQuotient (ReducedProductSetoid M (u : Filter ι)) s) :=
  ⟨MSQuotient.mk _ s (fun _ => Classical.choice inferInstance)⟩

def diagonal (M : Fam Sorts) [∀ s, Nonempty (M s)] [L.Structure M] :
    M ↪ₑ[L] Ultraproduct (fun _ ↦ M) u where
  toFun := MSQuotient.mk _ ∘ₛ ⟨fun s m i ↦ m⟩
  map_boundedFormula' φ xs := by
    have : (default : EmptyFam →ₛ Ultraproduct (fun i ↦ M) u) = MSQuotient.mk _ ∘ₛ default := by
      ext s x
      exact x.elim
    rw [this, comp_map]
    have : ∀ (i : ι), (⟨fun s b ↦ (default : EmptyFam →ₛ piFam fun i ↦ M) s b i⟩ : EmptyFam →ₛ M)
      = default := by intro i; ext s e; exact e.elim
    -- This erw is currently necessary because the goal here uses the unfolded
    -- toQuot. This should be changed
    erw [boundedFormula_realize]
    simp only [pi_lift_diag, this, eventually_const]

def map {N : ι → Fam Sorts} [∀ i, L.Structure (N i)] (fs : Π (i : ι), (M i ↪ₑ[L] N i)) :
    Ultraproduct M u ↪ₑ[L] Ultraproduct N u where
  toFun := ⟨fun s ↦ Quotient.map (Pi.map fun i ↦ fs i s)
    (by
      intro _ _ hab
      exact u.sets_of_superset hab fun i hi ↦ by
        rw [Set.mem_setOf_eq] at hi
        exact congrArg (fun x => (fs i) s x) hi)⟩
  map_boundedFormula' {σ} φ xs := by
    have : ∀ s i, Nonempty (N i s) := fun s i => ⟨fs i s  (Nonempty.some inferInstance)⟩
    rw [←toQuot_out_choice xs (R := _)]
    unfold toQuot
    have : ∀ (M : ι → Fam Sorts),  MSQuotient.mk _ ∘ₛ default =
        (default : EmptyFam →ₛ Ultraproduct M u) :=
      fun _ ↦ emptyDomUniqueMap.uniq _
    rw [←this, ←this, ←Interpret.comp_map]
    conv =>
      lhs; rhs; lhs; unfold MSQuotient.mk; simp [FamMap.comp];
      enter [1]
      ext s m
      change (Quotient.mk _ ∘ Pi.map _) _
    change φ.Realize _
      ((MSQuotient.mk (ReducedProductSetoid N u) ∘ₛ (⟨fun s xs ↦ _⟩ : piFam M →ₛ piFam N))
        <$>ₛ (xs.choice (R := _)).out)
      ↔ φ.Realize _ _
    rw [comp_map]
    erw [boundedFormula_realize, boundedFormula_realize]
    rw [iff_def]
    simp only [←Filter.eventually_and, ←u.eventually_imp]
    simp only [←iff_def]
    have := fun i ↦ (fs i).map_boundedFormula' φ
    apply u.mem_of_superset u.univ_sets
    intro i _
    simp only [Set.mem_setOf_eq]
    have this' : (⟨fun s b ↦ (default : EmptyFam →ₛ piFam M) s b i⟩ : EmptyFam →ₛ M i)
        = default := emptyDomUniqueMap.uniq _
    rw [this', ←this, ←propext_iff]
    congr
    · ext _ x
      exact x.elim
    · erw [pi_lift_map]

end Ultraproduct

end Language

end MSFirstOrder
