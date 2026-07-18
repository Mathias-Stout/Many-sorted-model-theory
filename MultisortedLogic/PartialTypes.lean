import MultisortedLogic.TSatisfiable

/-!
  # Partial Δ-types

  This file deals with types over a set of formulas Δ(α,σ) ⊆ L.BoundedFormula α σ

-/

universe u v u' z w

namespace MSFirstOrder

namespace Language

namespace FSet

open Fam Signature Language Structure

variable {Sorts : Type z} {α : Fam.{u'} Sorts} {σ : Signature Sorts} {L : Language.{u, v, z} Sorts}
  {M : Fam.{w} Sorts} {v : α →ₛ M} {x : M [^] σ} {φ : L.BoundedFormula α σ}
  {Δ Γ : L.FSet α σ} {p : L.FSet α σ}
  [L.Structure M]

section Fragments

/- Some mathematical questions/observations below: -/
/-  - For technical reasons, it is good that fragments  contain at least ⊥ and ⊤
      (so that they are closed under bigOr and bigAnd) -/
/-- A set of formulas closed under finite conjunctions (including empty conjunctions). -/
class ConjClosed (Δ : L.FSet α σ) where
  conj_mem : ∀ φ ψ, φ ∈ Δ → ψ ∈ Δ → φ ⊓ ψ ∈ Δ
  top_mem     : ⊤ ∈ Δ

/-- A set of formulas closed under finite dijunctions (including empty dijunctions). -/
class DisjClosed (Δ : L.FSet α σ) where
  disj_mem : ∀ φ ψ, φ ∈ Δ → ψ ∈ Δ → φ ⊔ ψ ∈ Δ
  bot_mem     : ⊥ ∈ Δ

/-- A fragment is a set of formulas closed under conjunction and disjunction. -/
class Fragment (Δ : L.FSet α σ) extends (ConjClosed Δ), (DisjClosed Δ)

instance instConjClosedInter (Δ Γ : L.FSet α σ) [ConjClosed Δ] [ConjClosed Γ] : ConjClosed (Δ ∩ Γ)
    where
  conj_mem := by
    intro φ ψ hφ hψ
    exact Set.mem_inter
      (ConjClosed.conj_mem φ ψ (Set.mem_of_mem_inter_left hφ) (Set.mem_of_mem_inter_left hψ))
      (ConjClosed.conj_mem φ ψ (Set.mem_of_mem_inter_right hφ) (Set.mem_of_mem_inter_right hψ))
  top_mem := by simp only [Set.mem_inter_iff, ConjClosed.top_mem, and_self]

instance instDisjClosedInter (Δ Γ : L.FSet α σ) [DisjClosed Δ] [DisjClosed Γ] :
     DisjClosed (Δ ∩ Γ) where
  disj_mem := by
    intro φ ψ hφ hψ
    exact Set.mem_inter
      (DisjClosed.disj_mem φ ψ (Set.mem_of_mem_inter_left hφ) (Set.mem_of_mem_inter_left hψ))
      (DisjClosed.disj_mem φ ψ (Set.mem_of_mem_inter_right hφ) (Set.mem_of_mem_inter_right hψ))
  bot_mem := by simp only [Set.mem_inter_iff, DisjClosed.bot_mem, and_self]

instance instFragmentInter [Fragment Δ] [Fragment Γ] : Fragment (Δ ∩ Γ) :=
  @Fragment.mk _ _ _ _ (Δ ∩ Γ) _ _

/- A class of formulas closed under negation. -/
class NegClosed (Δ : L.FSet α σ) where
  neg_closed : ∀ {φ}, φ ∈ Δ ↔ ∼ φ ∈ Δ

/-- A strong fragment is a a fragment that is closed under negation (and removing one negation)
  A strong fragment is satisfiable iff it is empty.
  --TODO: find a better name for this -/
class StrongFragment (Δ : L.FSet α σ) extends (Fragment Δ), (NegClosed Δ)

/-- All bounded formulas in `Δ` that are implied by `p`. -/
def RelDeductiveClosure (Δ : L.FSet α σ) (p : L.FSet α σ) : L.FSet α σ := {φ ∈ Δ | p ⊨ᵇ φ}

--TODO: move this lemma
lemma models_imp_iff {ψ : L.BoundedFormula α σ} : p ⊨ᵇ φ ⟹ ψ ↔ p ∪ {φ} ⊨ᵇ ψ  := by
  constructor
  · intro h ⟨M, hM⟩
    rw [realize_union_iff] at hM
    obtain ⟨hp, hφ⟩ := hM
    exact h ⟨M, hp⟩ (realize_singleton_iff.mp hφ)
  · intro hpφ ⟨M, hp⟩
    rw [BoundedFormula.realize_imp]
    intro hφ
    refine hpφ ⟨M, ?_⟩
    rw [realize_union_iff, realize_singleton_iff]
    exact ⟨hp, hφ⟩


lemma relDeduductiveClosure_of_union_singleton : RelDeductiveClosure Δ (p ∪ {φ}) =
    {ψ ∈ Δ | p ⊨ᵇ φ ⟹ ψ} := by
  simp only [RelDeductiveClosure, Set.union_singleton, models_imp_iff]

@[simp]
lemma DeductiveClosure.mem_iff : φ ∈ RelDeductiveClosure Δ p ↔ φ ∈ Δ ∧ p ⊨ᵇ φ := by rfl

instance DeductiveClosure.instConjClosed (p : L.FSet α σ) [ConjClosed Δ] :
    ConjClosed (RelDeductiveClosure Δ p) where
  conj_mem := by
    intro φ ψ ⟨hφΔ, hpφ⟩ ⟨hψΔ, hpψ⟩
    simp only [DeductiveClosure.mem_iff, models_iff] at *
    refine ⟨ConjClosed.conj_mem φ ψ hφΔ hψΔ, ?_⟩
    intro M
    rw [BoundedFormula.realize_inf]
    exact ⟨hpφ M, hpψ M⟩
  top_mem := by
    simp only [DeductiveClosure.mem_iff, models_iff]
    refine ⟨ConjClosed.top_mem, ?_⟩
    intro M
    simp [BoundedFormula.realize_top]

-- TODO: move this e.g. to Syntax
lemma bigOr_mem_if {l : List (L.BoundedFormula α σ)} (hmem : ∀ φ ∈ l, φ ∈ Δ)
    (hbot : ⊥ ∈ Δ) (hsup : ∀ φ ψ, φ ∈ Δ → ψ ∈ Δ → φ ⊔ ψ ∈ Δ) : ⋁ l ∈ Δ := by
  induction l with
  | nil => exact hbot
  | cons φ φs ih =>
    rw [BoundedFormula.bigOr, List.foldr_cons]
    apply hsup
    · exact hmem φ List.mem_cons_self
    · exact ih fun φ hφ => hmem φ (List.mem_cons_of_mem _ hφ)

lemma DisjClosed.bigOr [DisjClosed Δ] {l : List (L.BoundedFormula α σ)} (h : ∀ φ ∈ l, φ ∈ Δ) :
    ⋁ l ∈ Δ := bigOr_mem_if h DisjClosed.bot_mem DisjClosed.disj_mem

lemma DisjClosed.iSup [DisjClosed Δ] {A : Type*} [Finite A] {ι : A → L.BoundedFormula α σ}
    (h : ∀ a, ι a ∈ Δ) : BoundedFormula.iSup ι ∈ Δ := by
  rw [BoundedFormula.iSup]
  apply DisjClosed.bigOr
  simp_all only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, implies_true]

-- TODO: move this e.g. to Syntax
lemma bigAnd_mem_if {l : List (L.BoundedFormula α σ)} (hmem : ∀ φ ∈ l, φ ∈ Δ)
    (htop : ⊤ ∈ Δ) (hinf : ∀ φ ψ, φ ∈ Δ → ψ ∈ Δ → φ ⊓ ψ ∈ Δ) : ⋀ l ∈ Δ := by
  induction l with
  | nil => exact htop
  | cons φ φs ih =>
    rw [BoundedFormula.bigAnd, List.foldr_cons]
    apply hinf
    · exact hmem φ List.mem_cons_self
    · exact ih fun φ hφ => hmem φ (List.mem_cons_of_mem _ hφ)

lemma ConjClosed.bigAnd [ConjClosed Δ] {l : List (L.BoundedFormula α σ)} (h : ∀ φ ∈ l, φ ∈ Δ) :
    ⋀ l ∈ Δ := bigAnd_mem_if h ConjClosed.top_mem ConjClosed.conj_mem

lemma ConjClosed.iInf [ConjClosed Δ] {A : Type*} [Finite A] {ι : A → L.BoundedFormula α σ}
    (h : ∀ a, ι a ∈ Δ) : BoundedFormula.iInf ι ∈ Δ := by
  rw [BoundedFormula.iInf]
  apply ConjClosed.bigAnd
  simp_all only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, implies_true]

end Fragments

/-- The Δ-type of a realization `(M,v,x)`. Note that `(M,v,x) ⊨ᵖ tpOf(Δ,v,x)` and
  `(M,v,x) ⊨ᵇ ∼ φ` for `φ ∈ Δ \ tpOf(Δ,v,x). -/
abbrev tpOf (Δ : L.FSet α σ) (v : α →ₛ M) (x : M [^] σ) : L.FSet α σ :=
  {φ ∈ Δ | φ.Realize v x}

lemma tpOf.mem_superset {Δ : L.FSet α σ} : φ ∈ tpOf Δ v x → φ ∈ Δ := Set.mem_of_mem_inter_left

lemma realize_tpOf {Δ : L.FSet α σ} : φ ∈ tpOf Δ v x → φ.Realize v x := fun φ => φ.2


-- TODO: move to TSastisfiable
/-- A recurring lemma in the proof of the separation lemma. -/
theorem union_not_satisfiable_iff_exist_finset_models_imp
    {A : L.FSet α σ} :
    ¬ (p ∪ A ∪ {∼ φ}).IsSatisfiable  ↔ ∃ (A₀ : Finset (L.BoundedFormula α σ)),
      ((A₀ : L.FSet α σ)  ⊆ A) ∧   p ⊨ᵇ (BoundedFormula.iInf fun (χ : A₀) ↦ χ) ⟹ φ := by
  constructor
  · intro hnotsat
    rw [← models_iff_not_satisfiable, union_models_iff_exists_finset_union_models] at hnotsat
    obtain ⟨A₀, hsub, hmodels⟩ := hnotsat
    use A₀
    refine ⟨hsub, ?_⟩
    rw [← union_finset_models_iff]
    exact hmodels
  · intro ⟨A₀, hsub, himp⟩ ⟨M, hreal⟩
    let ψ := BoundedFormula.iInf fun (χ : A₀) ↦ (χ : L.BoundedFormula α σ)
    have hMA₀ : M ⊨ᵖ (A₀ : L.FSet α σ)     := realize_mono hreal (by grind)
    have hMimp : (ψ ⟹ φ).Realize M.v M.x  := himp ⟨M, realize_mono hreal (by grind)⟩
    have hnotφ : ¬ (φ.Realize M.v M.x)     := by
      rw [← BoundedFormula.realize_not, ← realize_singleton_iff]
      exact realize_mono hreal (by grind)
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_iInf] at hMimp
    exact hnotφ (hMimp fun χ => hMA₀ χ.val χ.prop)


/-- A version of the separation lemma: given two classes of formulas Δ, Γ (e.g. all quantifier-free
  formulas and all formulas, respectively), then modulo the realization of a type p, any Δ-formula
  is equivalent to some Γ-formula iff for every two realizations `(M,v,x)` and `(N,w,y)` of `p`,
  if  `tp_Δ(v,x) ⊆ tp_Δ(w,y)` then `tp_Γ(v,x) ⊆ tp_Γ(w,y)`. -/
theorem exists_equiv_boundedformula_iff_type_subset_implies_imp [Fragment Δ] :
    (∃ ψ ∈ Δ , p ⊨ᵇ φ ⇔ ψ) ↔ ∀ M N : Realization.{u, v, u', z, max u v u' z} p,
    tpOf Δ M.v M.x  ⊆ tpOf Δ N.v N.x
    → φ.Realize M.v M.x  → φ.Realize N.v N.x := by
  constructor
  · /- This direction is straightforward: if every formula in Δ is equivalent to a formula in Γ,
    then clearly tp_Δ(M,v,x) \  -/
    intro hequiv M N hsub hφM
    obtain ⟨ψ, hψΔ, hψequiv⟩ := hequiv
    simp only [models_iff, BoundedFormula.realize_iff] at hψequiv
    rw [hψequiv N]
    exact realize_tpOf (Set.mem_of_subset_of_mem hsub (Set.mem_setOf.mpr ⟨hψΔ, (hψequiv M).mp hφM⟩))
  · -- This direction has actual content
    intro hsub
    by_contra hnotequiv
    -- Collect all formal consequences of `φ` mod `p`
    let A := {ψ ∈ Δ | p ⊨ᵇ φ ⟹ ψ }
    have hAeq : A = RelDeductiveClosure Δ (p ∪ {φ}) :=
      by rw [relDeduductiveClosure_of_union_singleton]
    /- By compactness, `(p ∪ A ∪ {∼ φ})` is satisfiable, indeed else there is a finite subset
      A₀ ⊆ A such that `p ∪ A₀ ⊨ φ` and then p ⊨ ⋀_{ψ ∈ A_0} ψ → φ.
      todo: isolate this into a separate lemma. -/
    have hN : (p ∪ A ∪ {∼ φ}).IsSatisfiable := by
      by_contra h_not_sat
      obtain ⟨A₀, hsub, himp⟩ := union_not_satisfiable_iff_exist_finset_models_imp.mp h_not_sat
      rw [← models_iff_not_satisfiable, union_models_iff_exists_finset_union_models] at h_not_sat
      obtain ⟨A₀, hsub, hA₀⟩ := h_not_sat
      let ψ := (BoundedFormula.iInf fun (χ : A₀) ↦ χ.val)
      have hψA : ψ ∈ A := by
        rw [hAeq]
        exact ConjClosed.iInf (fun χ => Set.mem_of_subset_of_mem (hAeq ▸ hsub) χ.prop)
      rw [union_finset_models_iff] at hA₀
      push Not at hnotequiv
      -- But since φ implies every formula in A, it also implies ψ
      have hequiv : p ⊨ᵇ φ ⇔ ψ := by
        rw [models_bounded_formula_iff_models_imp_imp]
        exact ⟨hψA.2, hA₀⟩
      exact (hnotequiv ψ (by grind only [usr Set.mem_setOf_eq])) hequiv
    obtain ⟨N, hNrealize⟩ := hN
    let A_N := { χ  | χ ∈ Δ ∧  ¬ χ.Realize N.v N.x}
    /- The set A_N is closed under finite disjunctions, we record this here for later use. -/
    letI : DisjClosed A_N := by
        constructor
        · intro φ ψ ⟨hφΔ, hφnot⟩ ⟨hψΔ, hψnot⟩
          exact ⟨DisjClosed.disj_mem φ ψ hφΔ hψΔ,
            by rw [BoundedFormula.realize_sup, not_or]; exact ⟨hφnot, hψnot⟩⟩
        · rw [Set.mem_setOf_eq]
          simp only [DisjClosed.bot_mem, BoundedFormula.realize_bot, not_false_eq_true, and_self]
    set Γ_N := BoundedFormula.not '' A_N
    have : (p ∪ {φ} ∪ Γ_N ).IsSatisfiable := by
      rw [satisfiable_iff_not_models_bot]
      by_contra h
      rw [union_models_iff_exists_finset_union_models] at h
      obtain ⟨Γ₀, hsub, hmodels⟩ := h
      rw [union_finset_models_iff, ← BoundedFormula.not] at hmodels
      -- todo: this is a more general lemma
      have h_not_inj : Function.Injective (BoundedFormula.not : L.BoundedFormula α σ → _) :=
        fun a b h => (BoundedFormula.imp.inj h).1
      set A₀ := BoundedFormula.not ⁻¹' (Γ₀ : L.FSet α σ) with A₀_def
      have hA₀ : BoundedFormula.not '' A₀ = ↑Γ₀ :=
        A₀_def ▸ Set.image_preimage_eq_of_subset (Set.SurjOn.subset_range hsub)
      letI : Finite A₀ :=
        Set.Finite.preimage (Function.Injective.injOn h_not_inj) (Finset.finite_toSet Γ₀)
      have hA₀sub : A₀ ⊆ A_N :=
        A₀_def ▸ (Set.preimage_image_eq A_N h_not_inj) ▸ Set.preimage_mono hsub
      let ψ := BoundedFormula.iSup (fun (χ : A₀) => (χ : L.BoundedFormula α σ))
      /- We note that ψ lies in A_N: the set of Δ-formulas not realized by N. -/
      have hψA : ψ ∈ A_N := DisjClosed.iSup (fun a => hA₀sub a.prop)
      /- Unfolding the definitions of `Γ₀` and `A₀`, we seet that
        `hmodels : p ∪ {φ} ⊨ᵇ ∼(BoundedFormula.iInf fun (ψ : Γ₀) ↦ ↑ψ)` means that
        `p ∪ {φ} ⊨ᵇ BoundedFormula.iSup (fun (χ : A₀) => (χ : L.BoundedFormula α σ))`
        in other words, `p ⊨ᵇ φ ⟹ ψ` and thus `ψ ∈ A`     -/
      have hψΓ : ψ ∈ A := by
        rw [Set.mem_setOf_eq]
        refine ⟨DisjClosed.iSup fun a => (hA₀sub a.prop).1, ?_⟩
        rw [models_imp_iff, models_iff]
        intro ⟨M, hM⟩
        rw [BoundedFormula.realize_iSup]
        have hMψ := hmodels ⟨M, hM⟩
        rw [BoundedFormula.realize_not, BoundedFormula.realize_iInf] at hMψ
        push Not at hMψ
        obtain ⟨χ, hχ⟩ := hMψ
        obtain ⟨δ, hδ, hδeq⟩ : (χ : L.BoundedFormula α σ) ∈ BoundedFormula.not '' A₀ := by
          rw [hA₀]; exact Finset.mem_coe.mpr χ.prop
        use ⟨δ, hδ⟩
        by_contra h
        rw [← BoundedFormula.realize_not, hδeq] at h
        exact hχ h
      /- But membership of A_N and A contradicts eachother,
        since N realizes all formulas from A_N -/
      rw [Set.mem_setOf] at hψA
      refine hψA.2 <| realize_of_mem A (realize_mono hNrealize (by grind)) hψΓ
    /- We now find a structure `M` realizing `p`, `φ` and realizing only `Δ`-formulas that are
      realized by `N`.  This contradicts our assumption-/
    obtain ⟨M, hM⟩ := this
    have htp : tpOf Δ M.v M.x ⊆ tpOf Δ N.v N.x := by
      intro ψ; contrapose
      rw [Set.mem_setOf, Set.mem_setOf]; push Not
      intro hN hΔ
      rw [← BoundedFormula.realize_not]
      exact realize_of_mem Γ_N (realize_mono hM Set.subset_union_right)
        (Set.mem_image_of_mem BoundedFormula.not ⟨hΔ, hN hΔ⟩)
    exact absurd
      (hsub ⟨M, realize_mono hM (by grind)⟩ ⟨N, realize_mono hNrealize (by grind)⟩ htp
        (realize_of_mem _ hM (by grind)))
      (by rw [← BoundedFormula.realize_not]
          exact realize_of_mem _ hNrealize (Set.mem_union_right (p ∪ A) rfl))

theorem forall_exists_equiv_boundedformula_iff_subset_implies_subset [Fragment Δ] :
  (∀ φ ∈ Γ, ∃ ψ ∈ Δ, p ⊨ᵇ φ ⇔ ψ) ↔ (∀ (M N : Realization.{u, v, u', z, max u v u' z} p),
    (tpOf Δ M.v M.x) ⊆ tpOf Δ N.v N.x → tpOf Γ M.v M.x ⊆ tpOf Γ N.v N.x) := by
  simp only [exists_equiv_boundedformula_iff_type_subset_implies_imp, Set.setOf_subset_setOf,
    and_imp]
  grind

theorem exists_equiv_boundedformula_iff_type_eq_implies_imp [StrongFragment Δ] :
    (∃ ψ ∈ Δ , p ⊨ᵇ φ ⇔ ψ) ↔ ∀ M N : Realization.{u, v, u', z, max u v u' z} p,
    tpOf Δ M.v M.x  ⊆ tpOf Δ N.v N.x  → φ.Realize M.v M.x  → φ.Realize N.v N.x := by
  have : ∀ (M N : StructureType.{u, v, u', z, max u v u' z} L α σ),
      ((tpOf Δ M.v M.x ⊆ tpOf Δ N.v N.x) ↔ (tpOf Δ M.v M.x = tpOf Δ N.v N.x)) := by
    intro M N
    simp only [Set.setOf_subset_setOf, and_imp, subset_antisymm_iff, iff_self_and]
    intro himp φ h_φ_mem h_φ_real
    refine ⟨h_φ_mem, ?_⟩
    by_contra hM
    rw [← BoundedFormula.realize_not] at hM
    have hN : (∼ φ).Realize N.v N.x := (himp (∼ φ) (NegClosed.neg_closed.mp h_φ_mem) hM).2
    rw [BoundedFormula.realize_not] at hN
    exact hN h_φ_real
  rw [exists_equiv_boundedformula_iff_type_subset_implies_imp]

end FSet

end Language

end MSFirstOrder
