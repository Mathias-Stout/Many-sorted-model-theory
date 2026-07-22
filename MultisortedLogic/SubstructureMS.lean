/-
Based on the corresponding Mathlib file by Aaron Anderson and Gabin Kolly
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Closure
import MultisortedLogic.Semantics
import MultisortedLogic.Encoding
import MultisortedLogic.DepSet
/-!
# Multisorted Substructures

This file starts the multisorted translation of first-order substructures, replacing sets of
elements with families of sets indexed by sorts.
-/

universe u v w z

namespace MSFirstOrder

namespace Language

variable {Sorts : Type z} {L : Language.{u, v, z} Sorts}
variable {M : Fam.{w} Sorts} {N : Fam Sorts} {P : Fam Sorts}
variable [i : L.Structure M] [L.Structure N] [L.Structure P]

open Structure Signature Interpret Fam DepSet

section ClosedUnder

variable {σ : Signature Sorts} {t : Sorts} (f : L.Functions σ t) (A : DepSet M)

/-- Indicates that a family of sets in a given structure is closed under a function symbol. -/
def ClosedUnder : Prop :=
  ∀ x : M[^]σ, (∀ s (i : σ.Idx s), x.get s i ∈ A s) → funMap f x ∈ A t

variable (L)

@[simp]
theorem closedUnder_univ : @ClosedUnder _ L _ i _ _ f DepSet.univ := by
  intro x hx
  exact Set.mem_univ _

variable {L f A} {B : DepSet M}

namespace ClosedUnder

open Set

theorem inter (hA : ClosedUnder f A) (hB : ClosedUnder f B) :
    ClosedUnder f (A ∩ B) := by
  intro x hx
  refine ⟨hA x (fun s i => (hx s i).1), hB x (fun s i => (hx s i).2)⟩

theorem inf (hA : ClosedUnder f A) (hB : ClosedUnder f B) :
    ClosedUnder f (A ∩ B) :=
  hA.inter hB

variable {S : Set (DepSet M)}

theorem sInf (hS : ∀ A ∈ S, ClosedUnder f A) :
    ClosedUnder f (DepSet.sInter S) := by
  intro x hx
  unfold DepSet.sInter
  simp_all only [sInter_eq_sInf, mem_sInf]
  intro T a
  apply hS
  · simp_all only
  · intro s i_1
    simp_all only

end ClosedUnder

end ClosedUnder

variable (L) (M)

/-- A multisorted substructure of `M` is a family of sets closed under function symbols. -/
structure Substructure extends DepSet M where
  fun_mem : ∀ {σ t}, ∀ f : L.Functions σ t, ClosedUnder f toDepSet

variable {L} {M}

namespace Substructure

instance subStructureDepSetLike : DepSetLike (L.Substructure M) M where
  toDepSet := Substructure.toDepSet
  toDepSet_injective := by
    intro S T h
    cases S
    cases T
    cases h
    rfl

@[simp]
lemma closed_under {σ t} {f : L.Functions σ t} (A : L.Substructure M) :
  ClosedUnder f (A : DepSet M) := by
  exact A.fun_mem f

/-- Two substructures are equal if they have the same elements in each sort. -/
@[ext]
theorem ext {S T : L.Substructure M} (h : ∀ s x, x ∈ S s ↔ x ∈ T s) : S = T := by
  cases S with
  | mk Scarrier Sfun =>
    cases T with
    | mk Tcarrier Tfun =>
      have hcarrier : Scarrier = Tcarrier := by
        apply DepSet.ext
        intro s x
        exact h s x
      simp only [hcarrier]

/-- Copy a substructure replacing `carrier` with a family equal to it. -/
protected def copy (S : L.Substructure M) (s : DepSet M) (hs : s = S) :
    L.Substructure M where
  carrier := s
  fun_mem _ f := hs.symm ▸ S.fun_mem _ f

end Substructure


open Substructure



variable {S : L.Substructure M}

namespace Substructure

@[simp]
theorem coe_copy {s : DepSet M} (hs : s = S) :
    (S.copy s hs : DepSet M) = s :=
  rfl

theorem copy_eq {s : DepSet M} (hs : s = S) : S.copy s hs = S := by
  cases S
  cases hs
  rfl

theorem constants_mem {s : Sorts} (c : L.Constants s) : (c : M s) ∈ S s := by
  have h : funMap c (default : M[^](Signature.nil)) ∈ S s :=
    S.fun_mem c default (by intro s i; exact isEmptyElim i)
  simp_all only [DepSetLike.carrier_toDepSet, PUnit.default_eq_unit]
  exact h


/-- Membership of a multisorted tuple in a substructure. -/
def Mem {σ : Signature Sorts} (S : L.Substructure M) (x : M [^] σ) : Prop :=
  ∀ s (i : σ.Idx s), x.get s i ∈ S s

end Substructure

theorem Term.realize_mem {α : Fam Sorts} {σ : Signature Sorts} (t : L.Term α σ)
    (xs : α →ₛ M) (h : ∀ s a, xs s a ∈ S s) : Substructure.Mem S (t.realize xs) := by
  induction t with
  | var s a =>
      intro s' i
      cases i
      simp_all only [DepSetLike.carrier_toDepSet, realize_var, get_of]
  | func f ts ih =>
      intro s' i
      cases i
      exact (S.fun_mem f _ ih)
  | prod t₁ t₂ ih₁ ih₂ =>
      intro s' i
      cases i with
      | left i' =>
          simpa only [DepSetLike.carrier_toDepSet, realize_prod, get_left,
            realize_getLeafTerm] using ih₁ s' i'
      | right i' =>
          simpa only [DepSetLike.carrier_toDepSet, realize_prod, get_right,
            realize_getLeafTerm] using ih₂ s' i'
  | nil =>
      intro s' i
      exact isEmptyElim i

namespace Substructure

open Set

theorem le_def {S T : L.Substructure M} : S ≤ T ↔ ∀ s, S s ⊆ T s := by
  simp only [DepSetLike.le_def, ge_iff_le, DepSetLike.carrier_toDepSet]
  change S ⊆ T ↔ ∀ (s : Sorts), S.carrier s ⊆ T.carrier s
  exact subset_intro_mem_eq (S:= S.toDepSet) (T:= T.toDepSet)

/-- The maximal multisorted substructure. -/
instance instTop : Top (L.Substructure M) :=
  ⟨{ carrier := fun _ => univ
     fun_mem := fun {_} _ _ _ _ =>  mem_univ _ }⟩

instance instInhabited : Inhabited (L.Substructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top {s : Sorts} (x : M s) : x ∈ (⊤ : L.Substructure M) s :=
  mem_univ x

/-- The inf of two substructures is their pointwise intersection. -/
instance instInf : Min (L.Substructure M) :=
  ⟨fun S₁ S₂ =>
    { carrier := fun s => (S₁ s ∩ S₂ s)
      fun_mem {σ} {s} f xs h := by
        simp_all only [DepSetLike.carrier_toDepSet, Set.mem_inter_iff]
        constructor
        · apply S₁.fun_mem f
          intro s v
          exact (h s v).1
        · apply S₂.fun_mem f
          intro s v
          exact (h s v).2
     }⟩

@[simp]
theorem inf_apply (S₁ S₂ : L.Substructure M) (s : Sorts) :
    ((S₁ ⊓ S₂ : L.Substructure M) s) = (S₁ s ∩ S₂ s) :=
  rfl

@[simp]
theorem mem_inf {S₁ S₂ : L.Substructure M} {s : Sorts} {x : M s} :
    x ∈ (S₁ ⊓ S₂ : L.Substructure M) s ↔ x ∈ S₁ s ∧ x ∈ S₂ s :=
  Iff.rfl

instance instInfSet : InfSet (L.Substructure M) :=
  ⟨fun S =>
    { carrier := fun s => ⋂ T ∈ S, (T s)
      fun_mem := fun {σ t} f x hx => by
        refine mem_iInter₂.2 ?_
        intro T hT
        have hxT : ∀ s i, x.get s i ∈ T s := by
          intro s i
          exact (mem_iInter₂.mp (hx s i) T hT)
        exact T.fun_mem f x hxT }⟩

@[simp]
theorem sInf_apply (S : Set (L.Substructure M)) (s : Sorts) :
    ((sInf S : L.Substructure M) s) = ⋂ T ∈ S, (T s) :=
  rfl

theorem mem_sInf {S : Set (L.Substructure M)} {s : Sorts} {x : M s} :
    x ∈ (sInf S : L.Substructure M) s ↔ ∀ T ∈ S, x ∈ T s :=
  mem_iInter₂

theorem mem_iInf {ι : Sort*} {S : ι → L.Substructure M} {s : Sorts} {x : M s} :
    x ∈ (⨅ i, S i : L.Substructure M) s ↔ ∀ i, x ∈ S i s := by
  simp only [iInf, sInf_apply, mem_range, iInter_exists, iInter_iInter_eq', mem_iInter]

@[simp]
theorem iInf_apply {ι : Sort*} {S : ι → L.Substructure M} (s : Sorts) :
    ((⨅ i, S i : L.Substructure M) s) = ⋂ i, (S i s) := by
  simp only [iInf, sInf_apply, mem_range, iInter_exists, iInter_iInter_eq']

/-- Substructures of a multisorted structure form a complete lattice. -/
instance instCompleteLattice : CompleteLattice (L.Substructure M) :=
  { completeLatticeOfInf (L.Substructure M) (by
      intro S
      constructor
      · intro T hT
        exact (Substructure.le_def).2 (fun s x hx => (mem_sInf.1 hx) T hT)
      · intro T hT
        exact (Substructure.le_def).2 (fun s x hx =>
          (mem_sInf.2 (fun U hU => (Substructure.le_def.1 (hT hU)) s hx)))
    ) with
    le := (· ≤ ·)
    lt := (· < ·)
    top := ⊤
    le_top := by
      intro S
      exact (Substructure.le_def).2 (fun s x hx => mem_univ _)
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := by
      intro A B C hAB hAC
      exact (Substructure.le_def).2 (fun s x hx =>
        ⟨(Substructure.le_def.1 hAB) s hx, (Substructure.le_def.1 hAC) s hx⟩)
    inf_le_left := by
      intro A B
      exact (Substructure.le_def).2 (fun s x hx => (mem_inf.1 hx).1)
    inf_le_right := by
      intro A B
      exact (Substructure.le_def).2 (fun s x hx => (mem_inf.1 hx).2) }

variable (L)

/-- The multisorted substructure generated by a family of sets. -/
def closure : LowerAdjoint ((↑) : L.Substructure M → DepSet M) :=
  ⟨fun A => sInf { S : L.Substructure M | A ≤ (S : DepSet M) }, by
    intro A S
    constructor
    · intro h
      exact (DepSet.le_def).2 (fun s x hx =>
        (Substructure.le_def.1 h) s
          ((mem_sInf.2 fun T hT => (DepSet.le_def.1 hT) s hx)))
    · intro h
      exact sInf_le h⟩


variable {L} {A : DepSet M}

theorem mem_closure {s : Sorts} {x : M s} :
    x ∈ (closure L A : L.Substructure M) s ↔
      ∀ S : L.Substructure M, (∀ s, A s ⊆ S s) → x ∈ S s := by
  constructor
  · intro hx S hS
    exact (mem_sInf.1 hx) S ((DepSet.le_def).2 hS)
  · intro hx
    exact (mem_sInf.2 fun S hS => hx S ((DepSet.le_def).1 hS))

@[simp]
theorem subset_closure : ∀ s, A s ⊆ (closure L A : L.Substructure M) s := by
  exact (DepSet.le_def).1 ((closure L).le_closure A)

@[simp]
theorem subset_closure' : A  ⊆ (closure L A : L.Substructure M) := by
  intro xs hs
  rcases xs with ⟨s, x⟩
  apply subset_closure
  simp_all only [mem_sigma]

theorem not_mem_of_not_mem_closure {s : Sorts} {x : M s} (hx : x ∉ closure L A s) : x ∉ A s :=
  fun hA => hx ((subset_closure (L := L) (A := A) s) hA)

theorem closure_le {S : L.Substructure M} :
    closure L A ≤ S ↔ ∀ s, A s ⊆ S s := by
  constructor
  · intro h s
    exact (DepSet.le_def).1 (((closure L).gc A S).mp h) s
  · intro h
    exact ((closure L).gc A S).mpr ((DepSet.le_def).2 h)

@[gcongr only]
theorem closure_mono {A B : DepSet M} (h : ∀ s, A s ⊆ B s) :
    closure L A ≤ closure L B :=
  (closure_le (L := L) (A := A) (S := closure L B)).2
    (fun s => Set.Subset.trans (h s) (subset_closure (L := L) (A := B) s))

theorem closure_eq_of_le {S : L.Substructure M} (h₁ : ∀ s, A s ⊆ S s) (h₂ : S ≤ closure L A) :
    closure L A = S :=
  le_antisymm ((closure_le (L := L) (A := A) (S := S)).2 h₁) h₂

/-- The closure of a family of sets is the range of term realization. -/
theorem coe_closure_eq_range_term_realize (A : DepSet M) :
    (closure L A : DepSet M) =
      fun s => Set.range (fun t : L.Term A (.of s) =>
        t.realize A.subtypeVal) := by
  let S : L.Substructure M :=
    { carrier := fun s => Set.range (fun t : L.Term A (.of s) => t.realize A.subtypeVal)
      fun_mem := by
        intro σ t f x hx
        let pre : σ.IdxFam →ₛ L.Term₁ A :=
          ⟨fun s (i : σ.IdxFam s) => Classical.choose (hx s i)⟩
        have hpre : ∀ s i, (pre s i).realize A.subtypeVal = x.get s i := by
          intro s i
          exact (Classical.choose_spec (hx s i))
        let ts : L.Term A σ := (Term.varTerm σ).bind (fun s i => pre s i)
        have hts : ts.realize A.subtypeVal = x := by
          ext s i
          calc
            (ts.realize A.subtypeVal).get s i =
                (Interpret.fromGet (fun s i => (pre s i).realize A.subtypeVal)).get s i := by
                  simp only [Term.realize_bind, coeFun_apply, Term.realize_varterm, fromGet_get, ts]
            _ = (pre s i).realize A.subtypeVal := by
                  simp only [fromGet_get, coeFun_apply]
            _ = x.get s i := hpre s i
        refine ⟨Term.func f ts, ?_⟩
        simp only [Term.realize_func, hts] }
  have hA : ∀ s, A s ⊆ S s := by
    intro s x hx
    refine ⟨Term.var s ⟨x, hx⟩, ?_⟩
    rfl
  have hS : S ≤ closure L A := by
    refine (Substructure.le_def).2 ?_
    intro s x hx
    rcases hx with ⟨t, rfl⟩
    have hmem : Substructure.Mem (closure L A) (t.realize A.subtypeVal) := by
      apply Term.realize_mem (S := closure L A) (t := t) (xs := A.subtypeVal)
      intro s a
      exact (subset_closure (L := L) (A := A) s) a.2
    exact hmem s Signature.Idx.var
  have hEq : closure L A = S := closure_eq_of_le (L := L) (A := A) (S := S) hA hS
  funext s
  ext x
  constructor
  · intro hx; rw [hEq] at hx; exact hx
  · intro hx; rw [hEq]; exact hx

instance small_closure (A : DepSet M) (s : Sorts)
    [i : Small.{max u z} (Σ s, A s)] : Small.{max u z} (closure L A s) := by
  classical
  let α : Fam Sorts := A.Subtype
  haveI : Small.{max u z} (Σ s, α s) := by
    simp_all only [α]
    exact i
  haveI : Small.{max u z} (L.TCode α) := by
    dsimp only [TCode]
    infer_instance
  haveI : Small.{max u z} (Signature (L.TCode α)) :=
    small_of_injective (Signature.encode_injective (S := L.TCode α))
  haveI : Small.{max u z} (Sigma (L.Term α)) :=
    small_of_injective (Term.TreeEncode_injective (L := L) (α := α))
  haveI : Small.{max u z} (L.Term α (.of s)) := by
    refine small_of_injective (f:= fun t => (⟨Signature.of s, t⟩ : Sigma (L.Term α))) ?_
    intro t₁ t₂ h
    cases h
    rfl
  let coe : α →ₛ M := A.subtypeVal
  have hset :
      closure L A s = Set.range (fun t : L.Term α (.of s) => t.realize coe) := by
    have h := coe_closure_eq_range_term_realize (L := L) (A := A)
    simpa only [α, coe] using congrArg (fun f => f s) h
  simpa only [hset] using
    (inferInstance :
      Small.{max u z} (Set.range (fun t : L.Term α (.of s) => t.realize coe)))

theorem mem_closure_iff_exists_term {A : DepSet M} {s : Sorts} {x : M s} :
    x ∈ closure L A s ↔
      ∃ t : L.Term A (.of s),
        t.realize A.subtypeVal = x := by
  simp only [coe_closure_eq_range_term_realize (L := L) (A := A), mem_range]

open Cardinal

theorem lift_card_closure_le_card_term (A : DepSet M) (s : Sorts) :
    lift.{max u w z} #(closure L A s) ≤
     #(L.Term A (.of s)) := by
  let coe := A.subtypeVal
  let f:= (fun t : L.Term A (.of s) => t.realize coe)
  have hset :
      closure L A s =
        Set.range f := by
    have h := coe_closure_eq_range_term_realize (L := L) (A := A)
    simpa only [coe] using congrArg (fun f => f s) h
  simp only [hset, ge_iff_le]
  rw[← lift_id'.{max z w u} #(L.Term A (.of s))]
  simp only [lift_id]
  refine (lift_le.1 ?_)  -- turns goal into lifted goal
  simpa only [lift_lift, lift_id] using Cardinal.mk_range_le_lift (f:= f)
/-
lemma sigma_ineq {Sorts : Type z} {A : Sorts → Type u} {B : Sorts → Type u'}
    (h : ∀ s, lift.{u'} #(A s) ≤ lift.{u} #(B s)) :
    lift.{max u' z} #(Σ s, A s) ≤ lift.{max u z} #(Σ s, B s) := by
  classical
  -- pointwise inequality, lifted once more so both sides live in the same universe
  have reminding :
      ∀ s,
        lift.{max u' z} #(A s) ≤ lift.{max u z} #(B s) := by
    intro s
    -- lift the inequality `h s`, then simplify the double-lifts
    simpa [lift_lift, max_assoc, max_comm, max_left_comm] using
      (Cardinal.lift_le.2 (h s))

  -- rewrite sigma cardinals as sums and use `sum_le_sum`
  simp_all [Cardinal.mk_sigma, Cardinal.lift_sum, lift_lift,
        max_assoc, max_comm, max_left_comm]



/-- The lifted closure cardinality is bounded by the sigma of all term cardinalities.
This is a more direct bound that avoids universe complications with the full
cardinality theorem. For applications, combine with `Term.card_le` when universes align. -/
theorem lift_card_closure_le_sigma_term (A: DepSet M) (s : Sorts) :
    lift.{u} #(Σ s, closure L A s) ≤ #(Σ σ, L.Term A σ) := by
  have h0 := sigma_ineq (A := (fun t => A t)) (B := fun t => L.Term A (.of t))
  have h1 : ∀ s, lift.{max u w z, w} #↑((((closure L).toFun A)).carrier s) ≤
            #((σ : Signature Sorts) × L.Term (fun t ↦ ↑(A t)) σ)
  have h1 : lift.{max u w z} #(closure L A s) ≤ #(L.Term A (.of s)) :=
    lift_card_closure_le_card_term (i := i) A s
  have h2 : #(L.Term A (.of s)) ≤ #(Σ σ, L.Term A σ) :=
    Cardinal.mk_le_of_injective
      (f := fun t => (⟨Signature.of s, t⟩ : Σ σ, L.Term A σ))
      (fun _ _ h => by cases h; rfl)
  let h3:=  h1.trans h2

  let h4:=
-/
/-- The lifted closure cardinality is bounded by the sigma of all term cardinalities.
This is a more direct bound that avoids universe complications with the full
cardinality theorem. For applications, combine with `Term.card_le` when universes align. -/
theorem lift_card_closure_le_sigma_term (A : DepSet M) (s : Sorts) :
    lift.{max u w z} #(closure L A s) ≤ #(Σ σ, L.Term A σ) := by
  have h1 : lift.{max u w z} #(closure L A s) ≤ #(L.Term A (.of s)) :=
    lift_card_closure_le_card_term (i := i) A s
  have h2 : #(L.Term A (.of s)) ≤ #(Σ σ, L.Term A σ) :=
    Cardinal.mk_le_of_injective
      (f := fun t => (⟨Signature.of s, t⟩ : Σ σ, L.Term A σ))
      (fun _ _ h => by cases h; rfl)
  exact h1.trans h2


theorem lift_card_sigma_closure_le_sigma_term (A : DepSet M) :
    lift.{u} #(Σ s, closure L A s) ≤ #(Σ σ, L.Term A σ) := by
  classical
  have hterm :
      ∀ s (x : M s), x ∈ closure L A s →
        ∃ t : L.Term A (.of s), t.realize A.subtypeVal = x := by
    intro s x hx
    simpa using
      (mem_closure_iff_exists_term (L := L) (A := A) (s := s) (x := x)).1 hx
  choose term hterm' using hterm
  let f : (Σ s, closure L A s) → Σ s, L.Term A (.of s) :=
    fun ⟨s, x⟩ => ⟨s, term s x.1 x.2⟩
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | mk s x =>
      cases b with
      | mk s' y =>
        simp only [f, Sigma.mk.injEq] at h
        obtain ⟨hs, ht⟩ := h
        cases hs
        have ht' : term s x.1 x.2 = term s y.1 y.2 := eq_of_heq ht
        have hx :
            (term s x.1 x.2).realize A.subtypeVal = x.1 := hterm' s x.1 x.2
        have hy :
            (term s y.1 y.2).realize A.subtypeVal = y.1 := hterm' s y.1 y.2
        have hxy : x.1 = y.1 := by
          calc
            x.1 = (term s x.1 x.2).realize A.subtypeVal := by symm; exact hx
            _ = (term s y.1 y.2).realize A.subtypeVal := by simp only [ht']
            _ = y.1 := hy
        have hxy' : x = y := by
          apply Subtype.ext
          exact hxy
        simp [hxy']
  let f' : ULift.{u} (Σ s, closure L A s) → Σ s, L.Term A (.of s) :=
    fun x => f x.down
  have hf' : Function.Injective f' := by
    intro x y h
    apply ULift.down_injective
    apply hf
    simpa using h
  have h1 : lift.{u} #(Σ s, closure L A s) ≤
      #(Σ s, L.Term A (.of s)) := by
    have h1:= (Cardinal.mk_le_of_injective hf')
    simp only [mk_uLift, mk_sigma, ge_iff_le] at h1
    simp_all only [lift_sum, mk_sigma, f, f']
  have h2 : #(Σ s, L.Term A (.of s)) ≤ #(Σ σ, L.Term A σ) := by
    apply Cardinal.mk_le_of_injective
      (f := fun p => (⟨Signature.of p.1, p.2⟩ : Σ σ, L.Term A σ))
    intro p q h
    cases p with
    | mk s t =>
      cases q with
      | mk s' t' =>
        simp only [Sigma.mk.injEq, Signature.of.injEq] at h
        obtain ⟨hs, ht⟩ := h
        cases hs
        have ht' : t = t' := eq_of_heq ht
        simp [ht']
  exact h1.trans h2


--TODO: Simplify this proof!
/-- The cardinality of the total closure is bounded by ℵ₀ or the sum of the
cardinalities of the generators and function symbols (with appropriate universe lifts).
This is the multi-sorted generalization of
`MSFirstOrder.Language.Substructure.lift_card_closure_le`.
-/
theorem lift_card_closure_le {A : DepSet M} :
    lift.{u} #(Σ s, closure L A s) ≤
      max ℵ₀ (lift.{u} #(Σ s, A s) + lift.{w} #(Σ η s, L.Functions η s)) := by
  refine (lift_card_sigma_closure_le_sigma_term (i := i) A).trans ?_
  refine (Term.card_le' (L := L) (α := A) (Sorts := Sorts)).trans ?_
  calc max ℵ₀ #(L.TCode A)
      ≤ max ℵ₀ (lift.{u} #(Σ s, A s) + lift.{w} #(Σ η s, L.Functions η s)) := by
        apply max_le_max_left
        unfold TCode
        rw [Cardinal.mk_sum]
        simp only [mk_sigma, lift_sum]
        gcongr <;> apply le_of_eq
        <;> simp only [ ← Cardinal.lift_sum, ]
        · apply lift_inj.{_, max w z }.1
          simp_all only [lift_sum, lift_lift]
          rfl
        · let R : Cardinal :=
            sum fun i : Sorts =>
              sum fun σ : Signature Sorts =>
                lift.{w, u} #(L.Functions σ i)
          -- lift R up (in the Sorts-universe parameter), and push the lift through both sums
          have h :
              lift.{z, _} R
                =
              sum (fun i : Sorts =>
                sum (fun σ : Signature Sorts =>
                  lift.{max w z, u} #(L.Functions σ i))) := by
            -- push lift through the outer sum
            rw [lift_sum
              (ι := Sorts)
              (f := fun i : Sorts =>
                sum (fun σ : Signature Sorts =>
                  lift.{w, u} #(L.Functions σ i)))
              ]
            apply congrArg
            funext i
            rw [lift_sum
              (ι := Signature Sorts)
              (f := fun σ : Signature Sorts =>
                lift.{w, u} #(L.Functions σ i))
              ]
            simp only [lift_lift]
          have hid : lift.{z, _} R = R := lift_id' (a := R)
          simpa only [lift_sum] using
  (by
    simp only [←lift_sum]
    rw[←lift_inj.{_, max w z}]
    simp only [lift_sum, lift_lift]
    )


/-- If the sigma of terms is countable, then the closure is countable.
This provides a practical way to establish countability of closures. -/
theorem countable_closure_of_countable_sigma_term (A : DepSet M)
    [Countable (Σ σ, L.Term A σ)] :
    Countable (Σ s , closure L A s) := by
  rw [← Cardinal.mk_le_aleph0_iff, ← lift_le_aleph0.{max z w, u}]
  exact (lift_card_sigma_closure_le_sigma_term A).trans Cardinal.mk_le_aleph0


/-- If the generators and function symbols are both countable, then the closure is countable. -/
theorem countable_closure [Countable Sorts]
    (A : DepSet M)
    [Countable (Σ t, A t)] [Countable (Σ η t, L.Functions η t)] :
    Countable (Σ s , closure L A s) := by
  -- TCode is countable since it's a sum of the two countable sigma types
  haveI : Countable (Σ t, A.Subtype t) := by
    rename_i inst_2 inst_3
    exact inst_2
  haveI : Countable (L.TCode A) := inferInstance
  -- Signature over countable type is countable
  haveI : Countable (Signature (L.TCode A)) := BoundedFormula.countableSignature
  -- Terms inject into signatures via TreeEncode, hence countable
  haveI : Countable (Σ σ, L.Term A σ) :=
    Function.Injective.countable Term.TreeEncode_injective
  exact countable_closure_of_countable_sigma_term A

lemma mem_closed_iff (A : DepSet M) :
    A ∈ (closure L).closed ↔ ∀ {σ t}, ∀ f : L.Functions σ t, ClosedUnder f A := by
  refine ⟨?_, ?_⟩
  · intro h σ t f
    have h' : closure L A = A := h
    simpa only [h'] using (closure L A).closed_under
  · intro h
    have h' : closure L A = (⟨⟨A⟩, h⟩ : L.Substructure M) := by
      apply closure_eq_of_le (L := L) (A := A) (S := ⟨⟨A⟩, h⟩)
      · intro s x hx
        exact hx
      · intro s x hx
        apply (subset_closure (L := L) (A := A) )
        simp_all only
        obtain ⟨fst, snd⟩ := s
        simp_all only [mem_sigma, DepSetLike.carrier_toDepSet]
        exact x
    have h'' : (closure L A : DepSet M) = A := by
      ext s
      simp_all only [DepSetLike.carrier_toDepSet]
      rfl
    exact h''

@[simp]
lemma closed (S : L.Substructure M) : (closure L).closed S.toDepSet := by
  refine (mem_closed_iff (L := L) S.toDepSet).2 ?_
  intro σ t f
  simpa only using S.fun_mem f

variable (L)

lemma mem_closed_of_isRelational [L.IsRelational] (A : DepSet M) :
    A ∈ (closure L).closed :=
  (mem_closed_iff (L := L) (A := A)).2 (by
    intro σ t f
    exact (isEmptyElim f))

@[simp]
lemma closure_eq_of_isRelational [L.IsRelational] (A : DepSet M) :
    (closure L A : DepSet M) = A :=
  LowerAdjoint.closure_eq_self_of_mem_closed _ (mem_closed_of_isRelational L A)

@[simp]
lemma mem_closure_iff_of_isRelational [L.IsRelational] (A : DepSet M) {s : Sorts} (m : M s) :
    m ∈ closure L A s ↔ m ∈ A s := by
  simp only [closure_eq_of_isRelational]

variable {L}

/-- An induction principle for closure membership. -/
@[elab_as_elim]
theorem closure_induction {A : DepSet M} {p : ∀ s, M s → Prop} {s : Sorts} {x : M s}
    (hx : x ∈ closure L A s) (Hs : ∀ s x, x ∈ A s → p s x)
    (Hfun : ∀ {σ t} (f : L.Functions σ t), ClosedUnder f ⟨fun s => {x | p s x}⟩) :
    p s x := by
  let S : L.Substructure M :=
    { carrier := fun s => {x | p s x}
      fun_mem := by
        intro σ t f x hx
        exact Hfun f x hx }
  have hclosure : closure L A ≤ S :=
    (closure_le (L := L) (A := A) (S := S)).2 (fun s x hx => Hs s x hx)
  have hxS : x ∈ S s := (Substructure.le_def.1 hclosure) s hx
  exact hxS

/-- If `A` is dense in `M`, it suffices to prove a predicate on `A` and show it is closed under
function symbols. -/
@[elab_as_elim]
theorem dense_induction {A : DepSet M} {p : ∀ s, M s → Prop} {s : Sorts} (x : M s)
    (hA : closure L A = ⊤) (Hs : ∀ s x, x ∈ A s → p s x)
    (Hfun : ∀ {σ t} (f : L.Functions σ t), ClosedUnder f ⟨fun s => {x | p s x}⟩) :
    p s x := by
  have hclosure : ∀ s x, x ∈ closure L A s → p s x := by
    intro s x hx
    exact closure_induction (L := L) (A := A) (s := s) (x := x) hx Hs Hfun
  have hx : x ∈ closure L A s := by
    simp only [hA, mem_top]
  exact hclosure s x hx

variable (L) (M)

/-- `closure` forms a Galois insertion with the coercion to families of sets. -/
protected def gi : GaloisInsertion (@closure _ L M _) ((↑) : L.Substructure M → DepSet M)  where
  choice A _ := closure L A
  gc := (closure L).gc
  le_l_u _ := subset_closure'
  choice_eq _ _ := rfl

variable {L} {M}

@[simp]
theorem closure_eq (S : L.Substructure M) : closure L S = S :=
  (Substructure.gi L M).l_u_eq S

@[simp]
theorem closure_empty : closure L ∅ = (⊥ : L.Substructure M) := (Substructure.gi L M).gc.l_bot

@[simp]
theorem closure_univ : closure L univ = (⊤ : L.Substructure M) := by
  exact (closure_eq (L := L) (⊤ : L.Substructure M))

instance small_bot (s : Sorts) : Small.{max u z} ((⊥ : L.Substructure M) s) := by
  haveI : IsEmpty (Σ s, (∅ : Set (M s))) := by
    refine ⟨?_⟩
    intro x
    cases x with
    | mk s xs =>
      cases xs
      tauto
  haveI : Small.{max u z} (Σ s, (∅ : Set (M s))) := by
    infer_instance
  simpa only [closure_empty] using
    (small_closure (L := L) (A := ∅) (s := s))

theorem closure_union (A B : DepSet M) :
    closure L (A ∪ B) = closure L A ⊔ closure L B := (Substructure.gi L M).gc.l_sup

theorem closure_iUnion {ι} (A : ι → DepSet M) :
    closure L (iUnion A) = ⨆ i, closure L (A i) := by
  apply le_antisymm
  · refine (closure_le (L := L) (A := iUnion A) (S := ⨆ i, closure L (A i))).2 ?_
    intro s x hx
    have hx' : x ∈ (⨆ i, A i : DepSet M) s := by
      simpa [DepSet.iUnion_eq_iSup] using hx
    rcases (DepSet.mem_iSup.1 hx') with ⟨i, hi⟩
    have hsup : closure L (A i) ≤ ⨆ j, closure L (A j) := le_iSup (fun j => closure L (A j)) i
    exact (Substructure.le_def.1 hsup) s ((subset_closure (L := L) (A := A i) s) hi)
  · refine iSup_le ?_
    intro i
    refine (closure_le (L := L) (A := A i) (S := closure L (iUnion A))).2 ?_
    intro s x hx
    have hx' : x ∈ (⨆ j, A j : DepSet M) s := DepSet.mem_iSup.2 ⟨i, hx⟩
    have hx'' : x ∈ (iUnion A) s := by
      simpa [DepSet.iUnion_eq_iSup] using hx'
    exact (subset_closure (L := L) (A := iUnion A) s) hx''


def insertAt (A : DepSet M) (s : Sorts) (m : M s) : DepSet M:=
  ⟨fun t => by
    classical
    by_cases h : t = s
    · subst h
      exact Set.insert m (A t)
    · exact A t⟩

def singleAt (s : Sorts) (m : M s) : DepSet M :=
  ⟨fun t => by
    classical
    by_cases h : t = s
    · subst h
      exact ({m} : Set (M t))
    · exact (∅ : Set (M t))⟩

theorem insertAt_eq_union (A : DepSet M) (s : Sorts) (m : M s) :
    insertAt A s m = singleAt s m ∪ A  := by
  ext t
  classical
  by_cases h : t = s
  · subst h
    simp only [insertAt, ↓reduceDIte, singleAt, DepSet.mem_union, mem_singleton_iff]
    rfl
  · simp only [insertAt, h, ↓reduceDIte, singleAt, DepSet.mem_union, mem_empty_iff_false, false_or]

theorem closure_insertAt (A : DepSet M) (s : Sorts) (m : M s) :
    closure L (insertAt A s m) = closure L (singleAt s m) ⊔ closure L A := by
  have h := insertAt_eq_union (A := A) (s := s) (m := m)
  simpa only [h] using (closure_union (L := L) (A := singleAt s m) (B := A))

theorem iSup_eq_closure {ι : Sort*} (S : ι → L.Substructure M) :
    ⨆ i, S i = closure L (DepSet.iUnion (fun i => (S i : DepSet M))) := by
  simpa only [closure_eq] using
    (closure_iUnion (L := L) (A := fun i => (S i : DepSet M))).symm

-- This proof uses the fact that `Substructure.closure` is finitary.
theorem mem_iSup_of_directed {ι : Type*} [Nonempty ι] {S : ι → L.Substructure M}
    (hS : Directed (· ≤ ·) S) {s : Sorts} {x : M s} :
    x ∈ (⨆ i, S i) s ↔ ∃ i, x ∈ S i s := by
  refine ⟨?_, fun ⟨i, hi⟩ => (Substructure.le_def.1 (le_iSup (fun i => S i) i)) s hi⟩
  intro hx
  have hx' : x ∈ closure L (DepSet.iUnion (fun i => (S i : DepSet M))) s := by
    simpa only [iSup_eq_closure (L := L) (S := S)] using hx
  refine (closure_induction (L := L) (A := DepSet.iUnion (fun i => (S i : DepSet M)))
    (p := fun s x => ∃ i, x ∈ S i s) (s := s) (x := x) hx' ?_ ?_)
  · intro s x hx
    have hx' : x ∈ (⨆ i, (S i : DepSet M)) s := by
      simpa [DepSet.iUnion_eq_iSup] using hx
    exact DepSet.mem_iSup.1 hx'
  · intro σ t f xs hC
    classical
    simp_rw [Set.mem_setOf] at hC ⊢
    let g : Sigma (σ.IdxFam) → ι := fun si => Classical.choose (hC si.1 si.2)
    obtain ⟨k, hk⟩ := hS.finite_le (g := g)
    refine ⟨k, (S k).fun_mem f xs ?_⟩
    intro s i
    exact (Substructure.le_def.1 (hk ⟨s, i⟩)) s (Classical.choose_spec (hC s i))

-- This proof uses the fact that `Substructure.closure` is finitary.
theorem mem_sSup_of_directedOn {S : Set (L.Substructure M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {s : Sorts} {x : M s} :
    x ∈ (sSup S) s ↔ ∃ T ∈ S, x ∈ T s := by
  haveI : Nonempty S := Sne.to_subtype
  simpa only [sSup_eq_iSup', Subtype.exists, exists_prop] using
    (mem_iSup_of_directed (L := L) (S := fun T : S => (T : L.Substructure M))
      (hS.directed_val) (s := s) (x := x))

/-!
### `comap` and `map`
-/

/-- The preimage of a substructure along a homomorphism is a substructure. -/
def comap (φ : M →[L] N) (S : L.Substructure N) : L.Substructure M where
  carrier := fun s => { x : M s | φ s x ∈ S s }
  fun_mem := by
    intro σ t f x hx
    have hx' : ∀ s (i : σ.Idx s), (φ <$>ₛ x).get s i ∈ S s := by
      intro s i
      have hmem : φ s (x.get s i) ∈ S s := by
        simpa [Set.mem_setOf_eq] using hx s i
      have hget' : (φ <$>ₛ x).get s i = φ s (x.get s i) := by
        simp_all only [DepSetLike.carrier_toDepSet, mem_setOf_eq, get_map, FamMap.comp_apply']
        rfl
      exact hget' ▸ hmem
    have hmem : funMap f (φ <$>ₛ x) ∈ S t := S.fun_mem f (φ <$>ₛ x) hx'
    have hmap : φ t (funMap f x) = funMap f (φ <$>ₛ x) := Hom.map_fun (φ := φ) (f := f) (x := x)
    simpa [hmap] using hmem

@[simp]
theorem mem_comap {S : L.Substructure N} {f : M →[L] N} {s : Sorts} {x : M s} :
    x ∈ (S.comap f) s ↔ f s x ∈ S s :=
  Iff.rfl

theorem comap_comap (S : L.Substructure P) (g : N →[L] P) (f : M →[L] N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
theorem comap_id (S : L.Substructure P) : S.comap (Hom.id L _) = S := by
  ext s x
  rfl

/-- The image of a substructure along a homomorphism is a substructure. -/
def map (φ : M →[L] N) (S : L.Substructure M) : L.Substructure N where
  carrier := fun s => φ s '' S s
  fun_mem := by
    intro σ t f x hx
    classical
    let pre : σ.IdxFam →ₛ M := ⟨fun s i => Classical.choose (hx s i)⟩
    have hpre_mem : ∀ s i, pre s i ∈ S s := by
      intro s i
      exact (Classical.choose_spec (hx s i)).1
    have hpre_eq : ∀ s i, φ s (pre s i) = x.get s i := by
      intro s i
      exact (Classical.choose_spec (hx s i)).2
    let y : M[^]σ := Interpret.fromGet pre
    have hy_mem : ∀ s i, y.get s i ∈ S s := by
      intro s i
      have hy : y.get s i = pre s i := by
        simp only [fromGet_get, y]
      simpa only [hy] using hpre_mem s i
    have hxy : (φ <$>ₛ y) = x := by
      ext s i
      have hget' : (φ <$>ₛ y).get s i = φ s (y.get s i) := by
        simp_all only [DepSetLike.carrier_toDepSet, FamMap.mk_apply, fromGet_get, implies_true,
          get_map, FamMap.comp_apply', pre, y]
        apply hpre_eq
      have hy : y.get s i = pre s i := by
        simp only [fromGet_get, y]
      simpa only [hget', hy] using hpre_eq s i
    refine ⟨funMap f y, S.fun_mem f y hy_mem, ?_⟩
    have hmap : φ t (funMap f y) = funMap f (φ <$>ₛ y) :=
      Hom.map_fun (φ := φ) (f := f) (x := y)
    simp_all only [DepSetLike.carrier_toDepSet, FamMap.mk_apply, fromGet_get, implies_true,
      mapClass_eq_map, HomClass.map_fun, pre, y]


@[simp]
theorem mem_map {f : M →[L] N} {S : L.Substructure M} {s : Sorts} {y : N s} :
    y ∈ (S.map f) s ↔ ∃ x ∈ S s, f s x = y :=
  Iff.rfl

theorem mem_map_of_mem (f : M →[L] N) {S : L.Substructure M} {s : Sorts} {x : M s} (hx : x ∈ S s) :
    f s x ∈ (S.map f) s :=
  ⟨x, hx, rfl⟩

theorem apply_coe_mem_map (f : M →[L] N) (S : L.Substructure M) {s : Sorts} (x : S s) :
    f s x.1 ∈ (S.map f) s :=
  mem_map_of_mem f x.2

theorem map_map (g : N →[L] P) (f : M →[L] N) (S : L.Substructure M) :
    (S.map f).map g = S.map (g.comp f) := by
  ext s x
  change x ∈ g s '' (f s '' S s) ↔ x ∈ (g.comp f) s '' S s
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨f s z, ⟨z, hz, rfl⟩, rfl⟩

theorem map_le_iff_le_comap {f : M →[L] N} {S : L.Substructure M} {T : L.Substructure N} :
    S.map f ≤ T ↔ S ≤ T.comap f := by
  constructor
  · intro h
    exact (Substructure.le_def).2 (fun s x hx =>
      (Substructure.le_def.1 h) s (mem_map_of_mem f hx))
  · intro h
    exact (Substructure.le_def).2 (fun s y hy => by
      rcases hy with ⟨x, hx, rfl⟩
      exact (Substructure.le_def.1 h) s hx)

theorem gc_map_comap (f : M →[L] N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

theorem map_le_of_le_comap {T : L.Substructure N} {f : M →[L] N} {S : L.Substructure M} :
    S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

theorem le_comap_of_map_le {T : L.Substructure N} {f : M →[L] N} {S : L.Substructure M} :
    S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

theorem le_comap_map {f : M →[L] N} (S : L.Substructure M) : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

theorem map_comap_le {S : L.Substructure N} {f : M →[L] N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

theorem monotone_map {f : M →[L] N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

theorem monotone_comap {f : M →[L] N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp]
theorem map_comap_map {f : M →[L] N} (S : L.Substructure M) :
    ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[simp]
theorem comap_map_comap {S : L.Substructure N} {f : M →[L] N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

theorem map_sup (S T : L.Substructure M) (f : M →[L] N) :
    (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup

theorem map_iSup {ι : Sort*} (f : M →[L] N) (S : ι → L.Substructure M) :
    (⨆ i, S i).map f = ⨆ i, (S i).map f :=
  (gc_map_comap f).l_iSup

theorem comap_inf (S T : L.Substructure N) (f : M →[L] N) :
    (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf

theorem comap_iInf {ι : Sort*} (f : M →[L] N) (S : ι → L.Substructure N) :
    (⨅ i, S i).comap f = ⨅ i, (S i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
theorem map_bot (f : M →[L] N) : (⊥ : L.Substructure M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : M →[L] N) : (⊤ : L.Substructure N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
theorem map_id (S : L.Substructure M) : S.map (Hom.id L M) = S := by
  ext s x
  simp only [map, Hom.id_apply, DepSetLike.carrier_toDepSet]
  exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem map_closure (f : M →[L] N) (A: DepSet M) :
    (closure L A).map f = closure L (⟨fun s => f s '' A s⟩ : DepSet N) := by
  apply Eq.symm
  refine closure_eq_of_le (L := L) (A := (⟨fun s => f s '' A s⟩ : DepSet N))
    (S := (closure L A).map f) ?_ ?_
  · intro s x hx
    exact Set.image_mono (subset_closure (L := L) (A := A) s) hx
  · refine (map_le_iff_le_comap (f := f) (S := closure L A)
      (T := closure L (⟨fun s => f s '' A s⟩ : DepSet N))).2 ?_
    refine (closure_le (L := L) (A := A)
      (S := (closure L (⟨fun s => f s '' A s⟩ : DepSet N)).comap f)).2 ?_
    intro s x hx
    exact (subset_closure (L := L) (A := (⟨fun s => f s '' A s⟩ : DepSet N)) s) ⟨x, hx, rfl⟩

@[simp]
theorem closure_image (f : M →[L] N) (A: DepSet M) :
    closure L (⟨fun s => f s '' A s⟩ : DepSet N) = map f (closure L A) :=
  (map_closure f A).symm

section GaloisCoinsertion

variable {ι : Type*} {f : M →[L] N}

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective on each sort. -/
def gciMapComap (hf : ∀ s, Function.Injective (f s)) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion (fun S => by
    rintro ⟨s, x⟩ hx
    change f s x ∈ (S.map f) s at hx
    rcases (mem_map (f := f) (S := S) (s := s) (y := f s x)).1 hx with ⟨y, hy, hfy⟩
    exact (hf s hfy) ▸ hy)

variable (hf : ∀ s, Function.Injective (f s))
include hf

theorem comap_map_eq_of_injective (S : L.Substructure M) : (S.map f).comap f = S :=
  (gciMapComap (f := f) hf).u_l_eq S

theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap (f := f) hf).u_surjective

theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap (f := f) hf).l_injective

theorem comap_inf_map_of_injective (S T : L.Substructure M) :
    (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap (f := f) hf).u_inf_l _ _

theorem comap_iInf_map_of_injective (S : ι → L.Substructure M) :
    (⨅ i, (S i).map f).comap f = ⨅ i, S i :=
  (gciMapComap (f := f) hf).u_iInf_l _

theorem comap_sup_map_of_injective (S T : L.Substructure M) :
    (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap (f := f) hf).u_sup_l _ _

theorem comap_iSup_map_of_injective (S : ι → L.Substructure M) :
    (⨆ i, (S i).map f).comap f = ⨆ i, S i :=
  (gciMapComap (f := f) hf).u_iSup_l _

theorem map_le_map_iff_of_injective {S T : L.Substructure M} :
    S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap (f := f) hf).l_le_l_iff

theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap (f := f) hf).strictMono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type*} {f : M →[L] N} (hf : ∀ s, Function.Surjective (f s))
include hf

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective on each sort. -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion (fun S => by
    rintro ⟨s, y⟩ hy
    change y ∈ (map f (comap f S)) s
    rcases hf s y with ⟨x, rfl⟩
    exact ⟨x, hy, rfl⟩)

theorem map_comap_eq_of_surjective (S : L.Substructure N) : (S.comap f).map f = S :=
  (giMapComap (f := f) hf).l_u_eq S

theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap (f := f) hf).l_surjective

theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap (f := f) hf).u_injective

theorem map_inf_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap (f := f) hf).l_inf_u _ _

theorem map_iInf_comap_of_surjective (S : ι → L.Substructure N) :
    (⨅ i, (S i).comap f).map f = ⨅ i, S i :=
  (giMapComap (f := f) hf).l_iInf_u _

theorem map_sup_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap (f := f) hf).l_sup_u _ _

theorem map_iSup_comap_of_surjective (S : ι → L.Substructure N) :
    (⨆ i, (S i).comap f).map f = ⨆ i, S i :=
  (giMapComap (f := f) hf).l_iSup_u _

theorem comap_le_comap_iff_of_surjective {S T : L.Substructure N} :
    S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap (f := f) hf).u_le_u_iff

theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap (f := f) hf).strictMono_u

end GaloisInsertion

/-! ### Induced structures and embeddings -/

instance inducedStructure {S : L.Substructure M} : L.Structure S := by
  classical
  refine
    { funMap := ?_
      RelMap := ?_ }
  · intro σ t f x
    let coe : S.Subtype →ₛ M := fun s (x : S.Subtype s) => x.1
    refine ⟨funMap f (coe <$>ₛ x), ?_⟩
    refine S.fun_mem f (coe <$>ₛ x) ?_
    intro s i
    have hget : (coe <$>ₛ x).get s i = (x.get s i).1 := by
      simp_all only [get_map, FamMap.comp_apply', DepSetLike.carrier_toDepSet, coe]
      rfl
    exact hget ▸ (x.get s i).2
  · intro σ r x
    let coe : S.Subtype →ₛ M := fun s (x : S.Subtype s) => x.1
    exact RelMap r (coe <$>ₛ x)

/-- The natural embedding of a substructure into the ambient structure. -/
def subtype (S : L.Substructure M) : S ↪[L] M where
  toFun := fun s (x : S.Subtype s) => x.1
  inj' := by
    intro s x y h
    exact Subtype.ext h
  map_fun' := by
    intro σ t f x
    rfl
  map_rel' := by
    intro σ r x
    rfl

@[simp]
theorem subtype_apply (S : L.Substructure M) {s : Sorts} (x : S.Subtype s) :
    S.subtype s x = x.1 := by
  rfl

@[simp]
theorem realize_boundedFormula_top {α : Fam Sorts} {σ : Signature Sorts}
    {φ : L.BoundedFormula α σ} {v : α →ₛ (⊤ : L.Substructure M)}
    {xs : (⊤ : L.Substructure M).Subtype [^] σ} :
    φ.Realize v xs ↔
      φ.Realize ((((⊤ : DepSet M).subtypeVal) ∘ₛ v) : (s : Sorts) → α s → M s)
        (((⊤ : DepSet M).subtypeVal) <$>ₛ xs) := by
  let S := (⊤ : L.Substructure M)
  let g := S.subtype
  suffices h : ∀ {σ : Signature Sorts} (φ : L.BoundedFormula α σ)
      (v : α →ₛ S) (xs : S.Subtype[^]σ),
      φ.Realize v xs ↔ φ.Realize (g ∘ₛ v) (g <$>ₛ xs) by
    exact h φ v xs
  intro σ φ
  induction φ with
  | falsum => intros; rfl
  | equal t₁ t₂ =>
    intro v xs
    simp only [BoundedFormula.Realize, Interpret.get_map, ← Fam.sumComp_elim]
    rw [HomClass.realize_term (g := g), HomClass.realize_term (g := g)]
    constructor
    · intro h
      exact congrArg (g <$>ₛ ·) h
    · intro h
      have hinj := fun s => g.toMSEmbedding.inj' s
      exact Interpret.ext fun s i => hinj s (by
        have := congrArg (fun x => x.get s i) h
        simp only [Interpret.get_map] at this
        exact this)
  | rel R ts =>
    intro v xs
    simp only [BoundedFormula.Realize, Interpret.get_map, ← Fam.sumComp_elim]
    rw [HomClass.realize_term (g := g)]
    exact g.map_rel' _ _
  | imp f₁ f₂ ih₁ ih₂ =>
    intro v xs
    simp only [BoundedFormula.Realize, ih₁ v xs, ih₂ v xs]
  | all τ f ih =>
    intro v xs
    simp only [BoundedFormula.Realize]
    let lift : ∀ s, M s → S.Subtype s := fun s x => ⟨x, mem_top x⟩
    have hsimp : ∀ (σ : Signature Sorts) (ys : M[^]σ), g <$>ₛ (lift <$>ₛ ys) = ys := by
      intro σ ys
      induction σ with
      | nil => rfl
      | of s =>
          change g s (lift s ys) = ys
          dsimp only [subtype, g, lift]
          rfl
      | prod σ₁ σ₂ ih₁ ih₂ =>
          exact Prod.ext (ih₁ ys.1) (ih₂ ys.2)
    constructor
    · intro h ys
      have key := (ih v (xs, lift <$>ₛ ys)).mp (h (lift <$>ₛ ys))
      rw [Interpret.map_prod (f := g), hsimp] at key
      exact key
    · intro h ys
      rw [ih, Interpret.map_prod (f := g)]
      exact h (g <$>ₛ ys)

@[simp]
theorem realize_formula_top {α : Fam Sorts} {φ : L.Formula α}
    {v : α →ₛ (⊤ : L.Substructure M)} :
    φ.Realize v ↔ φ.Realize (((⊤ : DepSet M).subtypeVal) ∘ₛ v) := by
  unfold Formula.Realize
  let xsTop : (⊤ : L.Substructure M).Subtype[^]Signature.nil := default
  have h :
      BoundedFormula.Realize φ v xsTop ↔
        BoundedFormula.Realize φ ((((⊤ : DepSet M).subtypeVal) ∘ₛ v) : (s : Sorts) → α s → M s)
          (((⊤ : DepSet M).subtypeVal) <$>ₛ xsTop) := by
    exact realize_boundedFormula_top (L := L) (φ := φ) (v := v) (xs := xsTop)
  have hmap :
      (((⊤ : DepSet M).subtypeVal) <$>ₛ xsTop) = (default : M[^]Signature.nil) := by
    simp only [DepSet.top_eq_univ, PUnit.default_eq_unit, xsTop]
  have h' :
      BoundedFormula.Realize φ ((((⊤ : DepSet M).subtypeVal) ∘ₛ v) : (s : Sorts) → α s → M s)
          (((⊤ : DepSet M).subtypeVal) <$>ₛ xsTop) ↔
      BoundedFormula.Realize φ ((((⊤ : DepSet M).subtypeVal) ∘ₛ v) : (s : Sorts) → α s → M s)
          (default : M[^]Signature.nil) := by
    simp only [DepSet.top_eq_univ, mapClass_eq_map, PUnit.default_eq_unit]
  exact h.trans h'

/-- A dependent version of `Substructure.closure_induction`. -/
@[elab_as_elim]
theorem closure_induction' {A : DepSet M}
    {p : ∀ s (x : M s), x ∈ closure L A s → Prop}
    (Hs : ∀ s x (hx : x ∈ A s),
      p s x ((subset_closure (L := L) (A := A) s) hx))
    (Hfun : ∀ {σ t} (f : L.Functions σ t),
      ClosedUnder f ⟨fun s => {x | ∃ hx, p s x hx}⟩)
    {s : Sorts} {x : M s} (hx : x ∈ closure L A s) :
    p s x hx := by
  refine Exists.elim ?_ (fun (hx' : x ∈ closure L A s) (hc : p s x hx') => hc)
  have Hs' : ∀ s x, x ∈ A s → ∃ hx, p s x hx := by
    intro s x hx
    exact ⟨(subset_closure (L := L) (A := A) s) hx, Hs s x hx⟩
  exact closure_induction (L := L) (A := A) (p := fun s x => ∃ hx, p s x hx)
    (s := s) (x := x) hx Hs' Hfun

end Substructure

namespace LHom

variable {Sorts : Type z} {L L' : Language Sorts}
variable {M : Fam.{w} Sorts} [L.Structure M] [L'.Structure M]

/-- Reduces the language of a substructure along a language hom. -/
def substructureReduct (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    L'.Substructure M ↪o L.Substructure M where
  toFun S :=
    { carrier := S.carrier
      fun_mem := by
        intro σ t f x hx
        have h := S.fun_mem (φ.onFunction f) x hx
        simpa only [LHom.map_onFunction] using h }
  inj' := by
    intro S T h
    cases S
    cases T
    cases h
    rfl
  map_rel_iff' := Iff.rfl

variable (φ : L →ᴸ L') [φ.IsExpansionOn M]

@[simp]
theorem mem_substructureReduct {s : Sorts} {x : M s} {S : L'.Substructure M} :
    x ∈ (φ.substructureReduct S) s ↔ x ∈ S s :=
  Iff.rfl

@[simp]
theorem coe_substructureReduct {S : L'.Substructure M} :
    (φ.substructureReduct S : DepSet M) = S :=
  rfl

end LHom

namespace Substructure

/-- Turns any substructure containing a constant family `A` into an
`L[[fun t => A t]]`-substructure. -/
def withConstants (S : L.Substructure M) {A : DepSet M} (h : ∀ s, A s ⊆ S s) :
    L[[DepSet.Subtype A]].Substructure M where
  carrier := S.carrier
  fun_mem := by
    intro σ t f x hx
    cases f with
    | inl f =>
        exact S.fun_mem f x hx
    | inr f =>
        cases σ with
        | nil =>
            exact h t f.2
        | of =>
            exact isEmptyElim f
        | prod =>
            exact isEmptyElim f

variable {A : DepSet M} {S : L.Substructure M} (h : ∀ s, A s ⊆ S s)

@[simp]
theorem mem_withConstants {s : Sorts} {x : M s} : x ∈ (S.withConstants h) s ↔ x ∈ S s :=
  by
  exact Iff.rfl

@[simp]
theorem coe_withConstants : (S.withConstants h : DepSet M) = S :=
  by
  rfl

@[simp]
theorem reduct_withConstants :
    (L.lhomWithConstants (DepSet.Subtype A)).substructureReduct (S.withConstants h) = S := by
  ext s x
  rfl

variable {s : DepSet M}

theorem subset_closure_withConstants {A : DepSet M} :
    ∀ t, (A t) ⊆ (closure (L[[DepSet.Subtype A]]) s) t := by
  intro t a ha
  refine (mem_closure (L := L[[DepSet.Subtype A]]) (A := s) (s := t) (x := a)).2 ?_
  intro S hS
  exact constants_mem (L := L[[DepSet.Subtype A]]) (c := Sum.inr ⟨a, ha⟩)

theorem closure_withConstants_eq {A s : ∀ t, Set (M t)} :
    closure (L[[DepSet.Subtype (⟨A⟩ : DepSet M)]]) (⟨s⟩ : DepSet M) =
      (closure L (⟨fun t => A t ∪ s t⟩ : DepSet M)).withConstants
        (fun t =>
          (Set.subset_union_left.trans
            (subset_closure (L := L) (A := (⟨fun t => A t ∪ s t⟩ : DepSet M)) t))) := by
  let hA : ∀ t, A t ⊆ (closure L (⟨fun t => A t ∪ s t⟩ : DepSet M) : L.Substructure M) t :=
    fun t => (Set.subset_union_left.trans
      (subset_closure (L := L) (A := (⟨fun t => A t ∪ s t⟩ : DepSet M)) t))
  refine closure_eq_of_le (L := L[[DepSet.Subtype (⟨A⟩ : DepSet M)]]) (A := (⟨s⟩ : DepSet M))
    (S := (closure L (⟨fun t => A t ∪ s t⟩ : DepSet M)).withConstants hA) ?_ ?_
  · intro t x hx
    have hx' :
        x ∈ (closure L (⟨fun t => A t ∪ s t⟩ : DepSet M) : L.Substructure M) t :=
      (subset_closure (L := L) (A := (⟨fun t => A t ∪ s t⟩ : DepSet M)) t) (Or.inr hx)
    simpa only [Substructure.coe_withConstants, hA] using hx'
  · refine (Substructure.le_def).2 ?_
    intro t x hx
    have hx' :
        x ∈ (closure L (⟨fun t => A t ∪ s t⟩ : DepSet M) : L.Substructure M) t := by
      simpa only [Substructure.coe_withConstants, hA] using hx
    let T : L.Substructure M :=
      (L.lhomWithConstants (DepSet.Subtype (⟨A⟩ : DepSet M))).substructureReduct
        (closure (L[[DepSet.Subtype (⟨A⟩ : DepSet M)]]) (⟨s⟩ : DepSet M))
    have hT : closure L (⟨fun t => A t ∪ s t⟩ : DepSet M) ≤ T := by
      apply (closure_le (L := L) (A := (⟨fun t => A t ∪ s t⟩ : DepSet M)) (S := T)).2
      intro t y hy
      cases hy with
      | inl hyA =>
          have hy' :
              y ∈ (closure (L[[DepSet.Subtype (⟨A⟩ : DepSet M)]]) (⟨s⟩ : DepSet M)) t :=
            (subset_closure_withConstants (L := L) (A := (⟨A⟩ : DepSet M))
              (s := (⟨s⟩ : DepSet M)) t) hyA
          simpa only [T, LHom.coe_substructureReduct] using hy'
      | inr hyS =>
          have hy' :
              y ∈ (closure (L[[DepSet.Subtype (⟨A⟩ : DepSet M)]]) (⟨s⟩ : DepSet M)) t :=
            (subset_closure (L := L[[DepSet.Subtype (⟨A⟩ : DepSet M)]])
              (A := (⟨s⟩ : DepSet M)) t) hyS
          simpa only [LHom.coe_substructureReduct, T] using hy'
    exact (Substructure.le_def.1 hT) t hx'

end Substructure

namespace Hom

/-- The restriction of a hom to a substructure in the domain. -/
def domRestrict (f : M →[L] N) (p : L.Substructure M) : p →[L] N :=
  f.comp p.subtype.toHom

/-- A hom whose values lie in a substructure can be restricted to that substructure. -/
def codRestrict (p : L.Substructure N) (f : M →[L] N) (h : ∀ s x, f s x ∈ p s) :
    M →[L] p where
  toFun := ⟨fun s (x : M s) => (⟨f s x, h s x⟩ : (p : DepSet N).Subtype s)⟩
  map_fun' {σ t} fn x := by
    apply Subtype.ext
    let g : M →ₛ p := ⟨fun s (x : M s) => (⟨f s x, h s x⟩ : (p : DepSet N).Subtype s)⟩
    let coe : p →ₛ N := ⟨fun s (y : p s) => y.1⟩
    have hcomp : coe ∘ₛ g = f := by
      ext s y
      rfl
    have hmap : coe <$>ₛ (g <$>ₛ x) = (coe ∘ₛ g) <$>ₛ x := by
      simpa using (Interpret.comp_map (φ := g) (ψ := coe) (xs := x)).symm
    have hcomp' : coe ∘ₛ g = (f : M →ₛ N) := by
      simpa using hcomp
    have hR : ((funMap fn (g <$>ₛ x)).1 : N t) = funMap fn (f <$>ₛ x) := by
      change funMap fn (coe <$>ₛ (g <$>ₛ x)) = funMap fn (((f : M →ₛ N) <$>ₛ x))
      have hcomp_map : ((coe ∘ₛ g) <$>ₛ x) = (((f : M →ₛ N) <$>ₛ x)) := by
        simp only [hcomp', mapClass_eq_map]
      calc
        funMap fn (coe <$>ₛ (g <$>ₛ x)) = funMap fn ((coe ∘ₛ g) <$>ₛ x) :=
          congrArg (fun ys => funMap fn ys) hmap
        _ = funMap fn (((f : M →ₛ N) <$>ₛ x)) :=
          congrArg (fun ys => funMap fn ys) hcomp_map
    exact (f.map_fun fn x).trans hR.symm
  map_rel' {σ} r x hx := by
    simp_all only [RelMap, ← Interpret.comp_map]
    apply map_rel
    exact hx

@[simp]
theorem comp_codRestrict (f : M →[L] N) (g : N →[L] P) (p : L.Substructure P)
    (h : ∀ s x, g s x ∈ p s) :
    ((codRestrict p g h).comp f : M →[L] p) =
      codRestrict p (g.comp f) (fun s x => h s (f s x)) := by
  ext s x
  rfl

@[simp]
theorem subtype_comp_codRestrict (f : M →[L] N) (p : L.Substructure N)
    (h : ∀ s x, f s x ∈ p s) :
    p.subtype.toHom.comp (codRestrict p f h) = f := by
  ext s x
  rfl

/-- The range of a hom as a substructure. -/
def range (f : M →[L] N) : L.Substructure N := by
  exact
    (map f ⊤).copy (⟨fun s => Set.range (f s)⟩ : DepSet N) (by
      apply DepSet.ext
      intro s y
      constructor
      · intro hy
        rcases hy with ⟨x, hxy⟩
        exact ⟨x, mem_top (s := s) x, hxy⟩
      · intro hy
        rcases hy with ⟨x, _hx, hxy⟩
        exact ⟨x, hxy⟩)

theorem range_coe (f : M →[L] N) (s : Sorts) : (range f : ∀ s, Set (N s)) s = Set.range (f s) :=
  by
  unfold range
  simp [Substructure.coe_copy]

@[simp]
theorem mem_range {f : M →[L] N} {s : Sorts} {x : N s} :
    x ∈ range f s ↔ ∃ y, f s y = x :=
  by
  simp only [range_coe (f := f) (s := s), Set.mem_range]

theorem range_eq_map (f : M →[L] N) : f.range = map f ⊤ := by
  ext s x
  constructor
  · intro hx
    rcases (mem_range (f := f) (s := s) (x := x)).1 hx with ⟨y, rfl⟩
    exact ⟨y, mem_top (s := s) y, rfl⟩
  · intro hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact (mem_range (f := f) (s := s) (x := f s y)).2 ⟨y, rfl⟩

theorem mem_range_self (f : M →[L] N) {s : Sorts} (x : M s) : f s x ∈ f.range s :=
  by
  exact (mem_range (f := f) (s := s) (x := f s x)).2 ⟨x, rfl⟩

@[simp]
theorem range_id : range (Hom.id L M) = (⊤ : L.Substructure M) := by
  ext s x
  simp_all only [mem_range, id_apply, exists_eq, mem_top]

theorem range_comp (f : M →[L] N) (g : N →[L] P) :
    range (g.comp f : M →[L] P) = map g (range f) := by
  ext s x
  constructor
  · intro hx
    rcases (mem_range (f := (g.comp f : M →[L] P)) (s := s) (x := x)).1 hx with ⟨y, hy⟩
    refine ⟨f s y, ?_, hy⟩
    exact (mem_range (f := f) (s := s) (x := f s y)).2 ⟨y, rfl⟩
  · intro hx
    rcases hx with ⟨z, hz, hzx⟩
    rcases (mem_range (f := f) (s := s) (x := z)).1 hz with ⟨y, hy⟩
    exact (mem_range (f := (g.comp f : M →[L] P)) (s := s) (x := x)).2 ⟨y, by simpa [hy] using hzx⟩

theorem range_comp_le_range (f : M →[L] N) (g : N →[L] P) :
    range (g.comp f : M →[L] P) ≤ range g := by
  refine (Substructure.le_def).2 ?_
  intro s x hx
  rcases (mem_range (f := (g.comp f : M →[L] P)) (s := s) (x := x)).1 hx with ⟨y, hy⟩
  exact (mem_range (f := g) (s := s) (x := x)).2 ⟨f s y, hy⟩

theorem range_eq_top {f : M →[L] N} : range f = ⊤ ↔ ∀ s, Function.Surjective (f s) := by
  constructor
  · intro h s y
    have : y ∈ (range f : L.Substructure N) s := by
      simp only [h, mem_top]
    exact (mem_range (f := f) (s := s) (x := y)).1 this
  · intro h
    ext s y
    constructor
    · intro _hy
      exact mem_top (s := s) y
    · intro _hy
      exact (mem_range (f := f) (s := s) (x := y)).2 (h s y)

theorem range_le_iff_comap {f : M →[L] N} {p : L.Substructure N} :
    range f ≤ p ↔ comap f p = ⊤ := by
  rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

theorem map_le_range {f : M →[L] N} {p : L.Substructure M} : map f p ≤ range f := by
  refine (Substructure.le_def).2 ?_
  intro s y hy
  rcases hy with ⟨x, _hx, rfl⟩
  exact (mem_range (f := f) (s := s) (x := f s x)).2 ⟨x, rfl⟩

/-- The substructure of elements `x` such that `f` and `g` agree in each sort. -/
def eqLocus (f g : M →[L] N) : L.Substructure M := by
  refine
    { carrier := fun s => { x : M s | f s x = g s x }
      fun_mem := ?_ }
  intro σ t fn x hx
  have hfg : f <$>ₛ x = g <$>ₛ x := by
    ext s i
    have hf' : (f <$>ₛ x).get s i = f s (x.get s i) := by
      simp_all only [Set.mem_setOf_eq, get_map, FamMap.comp_apply']
      apply hx
    have hg' : (g <$>ₛ x).get s i = g s (x.get s i) := by
      simp_all only [Set.mem_setOf_eq, get_map, FamMap.comp_apply']
      rfl
    calc
      (f <$>ₛ x).get s i = f s (x.get s i) := hf'
      _ = g s (x.get s i) := hx s i
      _ = (g <$>ₛ x).get s i := hg'.symm
  have hmap_f : f t (funMap fn x) = funMap fn (f <$>ₛ x) :=
    Hom.map_fun (φ := f) (f := fn) (x := x)
  have hmap_g : g t (funMap fn x) = funMap fn (g <$>ₛ x) :=
    Hom.map_fun (φ := g) (f := fn) (x := x)
  calc
    f t (funMap fn x) = funMap fn (f <$>ₛ x) := hmap_f
    _ = funMap fn (g <$>ₛ x) := by simp only [hfg]
    _ = g t (funMap fn x) := hmap_g.symm

/-- If two homs agree on a family of sets, they agree on its closure. -/
theorem eqOn_closure {f g : M →[L] N} {A : DepSet M}
    (h : ∀ s, Set.EqOn (f s) (g s) (A s)) :
    ∀ s, Set.EqOn (f s) (g s) ((closure L A) s) := by
  have hclosure : closure L A ≤ f.eqLocus g :=
    (closure_le (L := L) (A := A) (S := f.eqLocus g)).2 (fun s x hx => h s hx)
  intro s x hx
  exact (Substructure.le_def.1 hclosure) s hx

theorem eq_of_eqOn_top {f g : M →[L] N}
    (h : ∀ s, Set.EqOn (f s) (g s) ((⊤ : L.Substructure M) s)) : f = g := by
  ext s x
  exact h s (x := x) (mem_top (s := s) x)

variable {A : DepSet M}

theorem eq_of_eqOn_dense (hA : closure L A = ⊤) {f g : M →[L] N}
    (h : ∀ s, Set.EqOn (f s) (g s) (A s)) : f = g := by
  apply eq_of_eqOn_top (L := L) (f := f) (g := g)
  simpa only [hA] using (eqOn_closure (L := L) (f := f) (g := g) (A := A) h)


end Hom

namespace Embedding

/-- The restriction of an embedding to a substructure in the domain. -/
def domRestrict (f : M ↪[L] N) (p : L.Substructure M) : p ↪[L] N :=
  f.comp p.subtype

@[simp]
theorem domRestrict_apply (f : M ↪[L] N) (p : L.Substructure M) {s : Sorts} (x : p s) :
    f.domRestrict p s x = f s x.1 :=
  by
  rfl

/-- An embedding whose values lie in a substructure can be restricted to that substructure. -/
def codRestrict (p : L.Substructure N) (f : M ↪[L] N) (h : ∀ s x, f s x ∈ p s) :
    M ↪[L] p where
  toFun := ⟨fun s (x : M s) => (⟨f s x, h s x⟩ : (p : DepSet N).Subtype s)⟩
  inj' := by
    intro s x y hxy
    apply f.injective s
    exact congrArg (fun z => z.1) hxy
  map_fun' {σ t} fn x := by
    apply Subtype.ext
    let g : M →ₛ p := ⟨fun s (x : M s) => (⟨f s x, h s x⟩ : (p : DepSet N).Subtype s)⟩
    let coe : p →ₛ N := ⟨fun s (y : p s) => y.1⟩
    have hcomp : coe ∘ₛ g = (f : M →ₛ N) := by
      ext s y
      rfl
    have hmap : coe <$>ₛ (g <$>ₛ x) = (coe ∘ₛ g) <$>ₛ x := by
      simpa using (Interpret.comp_map (φ := g) (ψ := coe) (xs := x)).symm
    have hR : ((funMap fn (g <$>ₛ x) : p t).1 : N t) = funMap fn (f <$>ₛ x) := by
      change funMap fn (coe <$>ₛ (g <$>ₛ x)) = funMap fn (((f : M →ₛ N) <$>ₛ x))
      have hcomp_map : ((coe ∘ₛ g) <$>ₛ x) = (((f : M →ₛ N) <$>ₛ x)) := by
        simp only [hcomp, mapClass_eq_map]
      calc
        funMap fn (coe <$>ₛ (g <$>ₛ x)) = funMap fn ((coe ∘ₛ g) <$>ₛ x) :=
          congrArg (fun ys => funMap fn ys) hmap
        _ = funMap fn (((f : M →ₛ N) <$>ₛ x)) :=
          congrArg (fun ys => funMap fn ys) hcomp_map
    exact (f.map_fun fn x).trans hR.symm
  map_rel' {σ} r x := by
    let coe : p →ₛ N := ⟨fun s (y : p s) => y.1⟩
    let toSub : M →ₛ p := ⟨fun s (x : M s) => (⟨f s x, h s x⟩ : (p : DepSet N).Subtype s)⟩
    have hcomp : coe ∘ₛ toSub = f.toFun := by
      ext s y
      rfl
    have hmap :
        Interpret.map (↑coe) (Interpret.map (↑toSub) x) = Interpret.map (↑(f.toFun)) x := by
      calc
        Interpret.map (↑coe) (Interpret.map (↑toSub) x) =
        Interpret.map (↑(coe ∘ₛ toSub)) x :=
          (Interpret.comp_map (φ := toSub) (ψ := coe) (xs := x)).symm
        _ = Interpret.map (↑(f.toFun)) x := by
              simp only [hcomp]
    change RelMap r (Interpret.map (↑coe) (Interpret.map (↑toSub) x)) ↔ RelMap r x
    rw [hmap]
    exact f.map_rel' r x

@[simp]
theorem codRestrict_apply (p : L.Substructure N) (f : M ↪[L] N) {h} {s : Sorts} (x : M s) :
    ((codRestrict p f h s x).1 : N s) = f s x :=
  by
  rfl

@[simp]
theorem codRestrict_apply' (p : L.Substructure N) (f : M ↪[L] N) {h} {s : Sorts} (x : M s) :
    codRestrict p f h s x = ⟨f s x, h s x⟩ :=
  by
  rfl

@[simp]
theorem comp_codRestrict (f : M ↪[L] N) (g : N ↪[L] P) (p : L.Substructure P)
    (h : ∀ s x, g s x ∈ p s) :
    ((codRestrict p g h).comp f : M ↪[L] p) =
      codRestrict p (g.comp f) (fun s x => h s (f s x)) := by
  ext s x
  apply Subtype.ext
  rfl

@[simp]
theorem subtype_comp_codRestrict (f : M ↪[L] N) (p : L.Substructure N)
    (h : ∀ s x, f s x ∈ p s) :
    p.subtype.comp (codRestrict p f h) = f := by
  ext s x
  rfl

/-- The equivalence between a substructure and its image under an embedding. -/
noncomputable def substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) :
    s ≃[L] (s.map f.toHom) := by
  classical
  let hs : ∀ t (x : s.Subtype t), (f.domRestrict s) t x ∈ (s.map f.toHom) t := by
    intro t x
    exact ⟨x.1, x.2, rfl⟩
  refine
    { toFun := codRestrict (s.map f.toHom) (f.domRestrict s) hs
      invFun := ⟨fun t x => ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩⟩
      left_inv' := ?_
      right_inv' := ?_
      map_fun' := ?_
      map_rel' := ?_ }
  · intro t x
    apply Subtype.ext
    apply f.injective t
    exact (Classical.choose_spec ((codRestrict (s.map f.toHom) (f.domRestrict s) hs) t x).2).2
  · intro t x
    apply Subtype.ext
    exact (Classical.choose_spec x.2).2
  · intro σ t fn x
    exact (codRestrict (s.map f.toHom) (f.domRestrict s) hs).map_fun' fn x
  · intro σ r x
    exact (codRestrict (s.map f.toHom) (f.domRestrict s) hs).map_rel' r x

@[simp]
theorem substructureEquivMap_apply (f : M ↪[L] N) (p : L.Substructure M) {s : Sorts}
    (x : p s) : ((f.substructureEquivMap p s x).1 : N s) = f s x.1 :=
  by
  classical
  unfold substructureEquivMap
  change
      (((codRestrict (p.map f.toHom) (f.domRestrict p)
        (fun t (y : p t) => (⟨y.1, y.2, rfl⟩ : (f.domRestrict p) t y ∈ (p.map f.toHom) t))
        s x).1 : N s) = f s x.1)
  calc
    ((codRestrict (p.map f.toHom) (f.domRestrict p)
        (fun t (y : p t) => (⟨y.1, y.2, rfl⟩ : (f.domRestrict p) t y ∈ (p.map f.toHom) t))
        s x).1 : N s) = (f.domRestrict p) s x := by
      exact codRestrict_apply (p := p.map f.toHom) (f := f.domRestrict p) (s := s) (x := x)
    _ = f s x.1 := by
      rfl

@[simp]
theorem subtype_substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) :
    (Substructure.subtype (L := L) (M := N) (S := s.map f.toHom)).comp
      (f.substructureEquivMap s).toEmbedding =
    f.comp (Substructure.subtype (L := L) (M := M) (S := s)) := by
  ext t x
  change ((f.substructureEquivMap s t x).1 : N t) = f t x.1
  exact substructureEquivMap_apply (f := f) (p := s) (s := t) (x := x)

/-- The equivalence between the domain and the range of an embedding `f`. -/
noncomputable def equivRange (f : M ↪[L] N) : M ≃[L] f.toHom.range where
  toFun := codRestrict f.toHom.range f (fun s x => f.toHom.mem_range_self (s := s) (x := x))
  invFun := ⟨fun s x => Classical.choose x.2⟩
  left_inv' := by
    intro t x
    apply f.injective t
    exact Classical.choose_spec
      ((codRestrict f.toHom.range f (fun s x => f.toHom.mem_range_self (s := s) (x := x)) t x).2)
  right_inv' := by
    intro s x
    apply Subtype.ext
    exact Classical.choose_spec x.2
  map_fun' := by
    intro σ t fn x
    exact
      (codRestrict f.toHom.range f (fun s x => f.toHom.mem_range_self (s := s) (x := x))).map_fun'
        fn x
  map_rel' := by
    intro σ r x
    exact
      (codRestrict f.toHom.range f (fun s x => f.toHom.mem_range_self (s := s) (x := x))).map_rel'
        r x

@[simp]
theorem equivRange_apply (f : M ↪[L] N) {s : Sorts} (x : M s) :
    ((f.equivRange s x).1 : N s) = f s x :=
  by
  rfl

@[simp]
theorem subtype_equivRange (f : M ↪[L] N) :
    (Substructure.subtype (L := L) (M := N)
    (S := f.toHom.range)).comp f.equivRange.toEmbedding = f := by
  ext s x
  rfl

end Embedding

namespace Equiv

theorem toHom_range (f : M ≃[L] N) : f.toHom.range = ⊤ := by
  ext s n
  constructor
  · intro _hn
    exact mem_top (s := s) n
  · intro _hn
    refine ⟨f.symm s n, ?_⟩
    simp only [coe_toHom, apply_symm_apply]

end Equiv

namespace Substructure

/-- The embedding associated to an inclusion of substructures. -/
def inclusion {S T : L.Substructure M} (h : S ≤ T) : S ↪[L] T :=
  S.subtype.codRestrict T (fun s x => (Substructure.le_def.1 h) s x.2)

@[simp]
theorem inclusion_self (S : L.Substructure M) :
    inclusion (le_refl S) = Embedding.refl L S :=
  by
  rfl

@[simp]
theorem coe_inclusion {S T : L.Substructure M} (h : S ≤ T) :
    (inclusion h : ∀ s, S s → T s) =
      fun s => Set.inclusion ((Substructure.le_def.1 h) s) :=
  by
  rfl

theorem range_subtype (S : L.Substructure M) : S.subtype.toHom.range = S := by
  ext s x
  refine ⟨?_, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rintro ⟨⟨y, hy⟩, rfl⟩
  exact hy

@[simp]
lemma subtype_comp_inclusion {S T : L.Substructure M} (h : S ≤ T) :
    T.subtype.comp (inclusion h) = S.subtype :=
  by
  rfl

end Substructure

end Language

end MSFirstOrder
