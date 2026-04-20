import ProdExpr.Semantics
import ProdExpr.Satisfiable

universe u v w u' w' v' z

namespace MSFirstOrder

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
  {M : Fam.{w} Sorts} {N P : Fam Sorts} [L.MSStructure M] [L.MSStructure N] [L.MSStructure P]
  {α : Fam.{u'} Sorts} {β : Fam.{v'} Sorts} {γ : Fam Sorts}
  {σ ξ η : Signature Sorts}
  {s : Sorts} {t : Sorts}


namespace MSLanguage
open Signature Interpret


namespace BoundedFormula


/-- Atomic formulas -/
inductive IsAtomic : L.BoundedFormula α σ → Prop
  | equal {ξ : Signature Sorts} (t₁ t₂ : L.Term (α ⊕ₛ σ.IdxFam) ξ) : IsAtomic (t₁.bdEqual t₂)
  | rel {ξ : Signature Sorts} (R : L.Relations ξ) (ts : L.Term (α ⊕ₛ σ.IdxFam) ξ) :
    IsAtomic (R.boundedFormula ts)

/-- Quantifier-free formulas -/
inductive IsQF : {σ : Signature Sorts} → L.BoundedFormula α σ → Prop
  | falsum : IsQF falsum
  | of_isAtomic {φ} (h : IsAtomic φ) : IsQF φ
  | imp {φ₁ φ₂} (h₁ : IsQF φ₁) (h₂ : IsQF φ₂) : IsQF (φ₁.imp φ₂)
  /-- dummy quantification case-/
  | all {ξ : Signature Sorts} {σ} {φ : L.BoundedFormula α (σ ⨯ ξ)} (hφ : IsQF φ)
    (hξ : ξ.fromSorts ∅) : IsQF φ.all

/-- Quantifier-free formulas, except over Sorts R ⊆ Sorts -/
inductive IsQFRelTo (R : Set Sorts) :
     {σ : Signature Sorts} → L.BoundedFormula α σ → Prop
  | falsum : IsQFRelTo R falsum
  | of_isAtomic {φ} (h : IsAtomic φ) : IsQFRelTo R φ
  | imp {φ₁ φ₂} (h₁ : IsQFRelTo R φ₁) (h₂ : IsQFRelTo R φ₂) : IsQFRelTo R (φ₁.imp φ₂)
  | all {ξ σ : Signature Sorts} {φ : L.BoundedFormula α (σ ⨯ ξ)} (hφ : IsQFRelTo R φ)
    (hξ : ξ.fromSorts R) : IsQFRelTo R φ.all

/-TODO: we need to allow dummy quantification over empty tuples in IsQF if we want this
equivalence to hold -/
lemma isQF_iff_isQFRelTo_empty (φ : L.BoundedFormula α σ) : IsQF φ ↔ IsQFRelTo ∅ φ (σ := σ) := by
  constructor
  · intro h
    induction h
    case falsum => exact IsQFRelTo.falsum
    case of_isAtomic ih => exact IsQFRelTo.of_isAtomic ih
    case imp ih₁ ih₂ => exact IsQFRelTo.imp ih₁ ih₂
    case all hξ ih => exact IsQFRelTo.all ih hξ
  · intro h
    induction h
    case falsum => exact IsQF.falsum
    case of_isAtomic ih => exact IsQF.of_isAtomic ih
    case imp ih₁ ih₂ => exact IsQF.imp ih₁ ih₂
    case all hξ ih => exact IsQF.all ih hξ

/-- Abstraction to simultaneously handle with quantifiers only over certain sorts as well
  as formulas over a sublanguage on the same level -/
class ImpClass (L : MSLanguage Sorts)
    (Δ : {α : Fam Sorts} → {σ : Signature Sorts} → L.BoundedFormula α σ → Prop) : Prop where
  falsum : ∀ {α} {σ}, @Δ α σ falsum
  imp : ∀ {α} {σ} (φ ψ : L.BoundedFormula α σ), Δ φ → Δ ψ → Δ (φ ⟹ ψ)

instance instQFImpclass : ImpClass L IsQF where
  falsum := IsQF.falsum
  imp := fun _ _ hφ hψ => IsQF.imp hφ hψ

instance instQFRelToImpClass (R : Set Sorts) : ImpClass L (IsQFRelTo R) where
  falsum := IsQFRelTo.falsum
  imp := fun _ _ hφ hψ => IsQFRelTo.imp hφ hψ

variable (Δ : {α : Fam Sorts} → {σ : Signature Sorts} → L.BoundedFormula α σ → Prop)
  [ImpClass L Δ]

theorem ImpClass.top : @Δ α σ ⊤ :=
  ImpClass.imp ⊥ ⊥ ImpClass.falsum ImpClass.falsum

theorem ImpClass.inf {φ ψ : L.BoundedFormula α σ} (hφ : Δ φ) (hψ : Δ ψ) : Δ (φ ⊓ ψ) :=
  -- φ ⊓ ψ = (φ ⟹ (ψ ⟹ ⊥)) ⟹ ⊥
  ImpClass.imp _ _ (ImpClass.imp _ _ hφ (ImpClass.imp _ _ hψ ImpClass.falsum)) ImpClass.falsum


--TODO: doublecheck these GenAI lemmas
private theorem ImpClass.bigAnd {l : List (L.BoundedFormula α σ)}
    (hl : ∀ φ ∈ l, Δ φ) : Δ (l.foldr (· ⊓ ·) ⊤) := by
  induction l with
  | nil => simpa using ImpClass.top (Δ := Δ)
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    apply ImpClass.inf
    · exact hl hd (.head tl)
    · exact ih (fun φ hφ => hl φ (List.mem_cons_of_mem _ hφ))

--TODO: doublecheck these GenAI lemmas
theorem ImpClass.iInf {X : Type*} [Finite X] {f : X → L.BoundedFormula α σ}
    (hf : ∀ x, Δ (f x)) : Δ (BoundedFormula.iInf f) := by
  unfold BoundedFormula.iInf
  apply ImpClass.bigAnd
  intro φ hφ
  simp only [List.mem_map] at hφ
  exact hφ.choose_spec.2 ▸ hf hφ.choose

open Formula Theory
#check fully_instantiate


-- TODO, move this to Satisfiable.lean
private theorem bigAnd_implies_of_finset_implies {φ : L.Sentence} {T : L.Theory}
    {Γ₀ : Finset (L.Sentence)} (hΓ₀ : ∀ χ ∈ Γ₀, T ⊨ᵇ φ ⟹ χ) : T ⊨ᵇ φ ⟹ ⋀ Γ₀.toList := by
  rw [models_sentence_imp_iff]
  intro N hφ
  rw [Sentence.Realize, Formula.Realize, realize_bigAnd]
  intro χ hχ
  have imp_χ : T ⊨ᵇ φ ⟹ χ := hΓ₀ χ (Finset.mem_toList.mp hχ)
  rw [← Formula.Realize, ← Sentence.Realize]
  rw [Theory.models_sentence_imp_iff] at imp_χ
  exact imp_χ N hφ

--TODO: move to satisfiability
private theorem models_bigAnd_imp_of_finset_models {φ : L.Sentence} {T : L.Theory}
    {Γ₀ : Finset L.Sentence} (h : T ∪ Γ₀ ⊨ᵇ φ) : T ⊨ᵇ ⋀ Γ₀.toList ⟹ φ := by
  rw [models_sentence_imp_iff]
  intro N hN
  letI : (T ∪ Γ₀).Model N := by
    rw [Theory.model_union_iff]
    rw [Sentence.Realize, Formula.Realize, realize_bigAnd] at hN
    constructor
    · exact N.is_model
    · rw [Theory.model_iff]
      intro χ hχ
      apply hN χ (Finset.mem_toList.mpr hχ)
  rw [Theory.models_sentence_iff] at h
  exact h ⟨N⟩


private theorem helper {φ : L.Sentence} {T : L.Theory} {Γ : L.Theory}
    (Γ_def : ∀ ψ : L.Sentence, ψ ∈ Γ ↔ Δ ψ ∧ (T ⊨ᵇ (φ ⟹ ψ)))
    (hT : ∀ ψ : L.Sentence, Δ ψ → ¬ (T ⊨ᵇ (φ ⇔ ψ))) :
    (T ∪ Γ ∪ {∼ φ}).IsSatisfiable := by
  refine Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr ?_
  rw [Theory.IsFinitelySatisfiable]
  intro T₀ hT₀
  -- Likely not strictly necessary, but helps when dealing with both `sets` and `Finsets`
  classical
  let Γ₀ := T₀.filter (· ∈ Γ)
  have hΓ : ∀ χ ∈ Γ, Δ χ ∧ T ⊨ᵇ (φ ⟹ χ) := fun χ => (Γ_def χ).mp
  have hΓ₀_χ : ∀ χ ∈ Γ₀, T ⊨ᵇ φ ⟹ χ := fun χ hχ => (hΓ χ (Finset.mem_filter.mp hχ).2).2
  have hΓ₀_Δ : ∀ χ ∈ Γ₀, Δ χ := fun χ hχ => (hΓ χ (Finset.mem_filter.mp hχ).2).1
  let ψ  := ⋀ Γ₀.toList
  apply Theory.IsSatisfiable.mono (T' := ((T ∪ Γ₀ ∪ {∼ φ})))
  · by_contra h
    rw [← Theory.models_iff_not_satisfiable (T := T ∪ Γ₀) φ] at h
    have φ_imp_ψ := bigAnd_implies_of_finset_implies hΓ₀_χ
    have ψ_imp_φ : T ⊨ᵇ (⋀ Γ₀.toList ⟹ φ) := models_bigAnd_imp_of_finset_models h
    have φ_equiv_ψ : T ⊨ᵇ (φ ⇔ ⋀ Γ₀.toList) :=
      models_sentence_iff.mpr fun M => by
        rw [Sentence.realize_iff]
        exact ⟨(models_sentence_imp_iff.mp φ_imp_ψ) M,
               (models_sentence_imp_iff.mp ψ_imp_φ) M⟩
    have Δ_ψ : Δ (⋀ Γ₀.toList) := by
      apply ImpClass.bigAnd
      intro χ hχ
      exact hΓ₀_Δ χ (Finset.mem_toList.mp hχ)
    exact hT (⋀ Γ₀.toList) Δ_ψ φ_equiv_ψ
  · intro x hx
    rcases hT₀ hx with (hxT | hxΓ) | hxφ
    · exact Set.mem_union_left _ (Set.mem_union_left _ hxT)
    · exact Set.mem_union_left _ (Set.mem_union_right _
        (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hx, hxΓ⟩)))
    · exact Set.mem_union_right _ hxφ


theorem two_models_of_not_in_impclass (φ : L.Formula α) (T : L.Theory)
    (hT : ∀ (ψ : L.Formula α), Δ ψ → ¬ (T ⊨ᵇ φ ⇔ ψ)) :
    -- Hacky attempt at trying to make the universe levels line up
    ∃ (M N : MSModelType.{u, v, z, max (max (max u u') v) z} T) (v : α →ₛ M) (w : α →ₛ N),
      φ.Realize v ∧ ¬ φ.Realize w ∧
    ∀ (ψ : L.Formula α), Δ ψ → (ψ.Realize v ↔ ψ.Realize w) := by
  -- Setup: work as much as possible with sentences over an extended Language
  set φₐ := φ.equivSentence with φₐ_def
  set Tₐ := (lhomWithConstants L α).onTheory T with Tₐ_def
  let Γ : L[[α]].Theory := {ψ : L[[α]].Sentence | Δ (Formula.equivSentence.symm ψ) ∧ Tₐ ⊨ᵇ φₐ ⟹ ψ}
  have Γ_def : ∀ ψ : L[[α]].Sentence, ψ ∈ Γ ↔ Δ (equivSentence.symm ψ) ∧ (Tₐ ⊨ᵇ φₐ ⟹ ψ) := by
    intro ψ
    rfl
  have hT' : ∀ ψ : L[[α]].Sentence, Δ (equivSentence.symm ψ) → ¬ (Tₐ ⊨ᵇ (φₐ ⇔ ψ)) := by
    intro ψ hΔ hiff
    apply hT (equivSentence.symm ψ) hΔ
    rw [models_formula_iff_onTheory_models_equivSentence]
    simp only [BoundedFormula.iff, equivSentence_inf, equivSentence_imp,
      _root_.Equiv.apply_symm_apply, ← φₐ_def, ← Tₐ_def]
    exact hiff
  have : (Tₐ ∪ Γ ∪ {∼ φₐ}).IsSatisfiable := by
    refine Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr ?_
    rw [Theory.IsFinitelySatisfiable]
    intro T₀ hT₀
    classical
    let Γ₀ := T₀.filter (· ∈ Γ)
    have hΓ : ∀ χ ∈ Γ, Δ (equivSentence.symm χ) ∧ Tₐ ⊨ᵇ (φₐ ⟹ χ) := fun χ => (Γ_def χ).mp
    have hΓ₀_χ : ∀ χ ∈ Γ₀, Tₐ ⊨ᵇ φₐ ⟹ χ :=
      fun χ hχ => (hΓ χ (Finset.mem_filter.mp hχ).2).2
    have hΓ₀_Δ : ∀ χ ∈ Γ₀, Δ (equivSentence.symm χ) :=
      fun χ hχ => (hΓ χ (Finset.mem_filter.mp hχ).2).1
    apply Theory.IsSatisfiable.mono (T' := ((Tₐ ∪ Γ₀ ∪ {∼ φₐ})))
    · by_contra h
      rw [← Theory.models_iff_not_satisfiable (T := Tₐ ∪ Γ₀) φₐ] at h
      have φ_imp_ψ := bigAnd_implies_of_finset_implies hΓ₀_χ
      have ψ_imp_φ : Tₐ ⊨ᵇ (⋀ Γ₀.toList ⟹ φₐ) := models_bigAnd_imp_of_finset_models h
      have φ_equiv_ψ : Tₐ ⊨ᵇ (φₐ ⇔ ⋀ Γ₀.toList) :=
        models_sentence_iff.mpr fun M => by
          rw [Sentence.realize_iff]
          exact ⟨(models_sentence_imp_iff.mp φ_imp_ψ) M,
                 (models_sentence_imp_iff.mp ψ_imp_φ) M⟩
      have Δ_ψ : Δ (equivSentence.symm (⋀ Γ₀.toList)) := by
        rw [equivSentence_symm_bigAnd]
        apply ImpClass.bigAnd
        intro χ hχ
        simp only [List.mem_map] at hχ
        obtain ⟨ξ, hξ, rfl⟩ := hχ
        exact hΓ₀_Δ ξ (Finset.mem_toList.mp hξ)
      exact hT' (⋀ Γ₀.toList) Δ_ψ φ_equiv_ψ
    · intro x hx
      rcases hT₀ hx with (hxT | hxΓ) | hxφ
      · exact Set.mem_union_left _ (Set.mem_union_left _ hxT)
      · exact Set.mem_union_left _ (Set.mem_union_right _
          (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hx, hxΓ⟩)))
      · exact Set.mem_union_right _ hxφ
  -- Extract model N from the satisfiable theory (Tₐ ∪ Γ ∪ {∼ φₐ})
  let ⟨N⟩ := this
  -- N is an L[[α]]-structure modelling Tₐ ∪ Γ ∪ {∼ φₐ}
  letI : L.MSStructure N.Carrier := (L.lhomWithConstants α).reduct N.Carrier
  -- N models Tₐ, hence T
  have hNTₐ : N.Carrier ⊨ Tₐ :=
    N.is_model.mono (Set.subset_union_left.trans Set.subset_union_left)
  haveI hNT : N.Carrier ⊨ T := (LHom.onTheory_model (φ := L.lhomWithConstants α) T).1 hNTₐ
  -- N models Γ
  have hNΓ : N.Carrier ⊨ Γ :=
    N.is_model.mono (Set.subset_union_right.trans Set.subset_union_left)
  -- N models ∼ φₐ
  have hN_not_φ : N ⊨ ∼ φₐ :=
    Theory.realize_sentence_of_mem (T := Tₐ ∪ Γ ∪ {∼ φₐ}) (Set.mem_union_right _ rfl)
  -- The assignment w : α →ₛ N is given by the constants interpretation
  let w : α →ₛ N.Carrier := ⟨fun s a => (L.con s a : N.Carrier s)⟩
  -- w does not satisfy φ
  have hw_not_φ : ¬ φ.Realize w := by
    rw [Sentence.realize_not] at hN_not_φ
    exact fun h => hN_not_φ ((realize_equivSentence N.Carrier φ).2 h)
  -- Build N as a T.MSModelType
  let N' : T.MSModelType := Theory.MSModelType.mk N.Carrier
    (struc := (L.lhomWithConstants α).reduct N.Carrier) (is_model := hNT)
    (nonempty' := N.nonempty')
  /-
  Now define A: the Δ-sentences true in N.
  Show (Tₐ ∪ A ∪ {φₐ}) is satisfiable, to produce the structure M.
  -/
  let A : L[[α]].Theory := {ψ : L[[α]].Sentence | Δ (equivSentence.symm ψ) ∧ N ⊨ ψ }
  have hA_sat : (Tₐ ∪ A ∪ {φₐ}).IsSatisfiable := by
    refine Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr ?_
    rw [Theory.IsFinitelySatisfiable]
    intro T₀ hT₀
    classical
    let A₀ := T₀.filter (· ∈ A)
    let l' := A₀.toList
    let χ  := ⋀ l'
    have χ_def : χ = ⋀ l' := rfl
    -- If Tₐ ∪ Σ₀ ∪ {φₐ} is not satisfiable, then Tₐ ⊨ φₐ ⟹ ∼χ
    apply Theory.IsSatisfiable.mono (T' := ((Tₐ ∪ ↑A₀ ∪ {φₐ})))
    · by_contra h
      -- h : ¬(Tₐ ∪ ↑A₀ ∪ {φₐ}).IsSatisfiable
      have h_φ_imp_not_χ : Tₐ ⊨ᵇ φₐ ⟹ ∼ χ := by
        rw [Theory.models_sentence_imp_iff]
        intro M hMφ
        rw [Sentence.realize_not]
        intro hMχ
        apply h
        have hMA₀ : (M : Fam Sorts) ⊨ (↑A₀ : L[[α]].Theory) := by
          rw [Theory.model_iff]
          intro ξ hξ
          rw [χ_def, Sentence.Realize, Formula.Realize, realize_bigAnd] at hMχ
          exact hMχ ξ (Finset.mem_toList.mpr (Finset.mem_coe.mp hξ))
        letI : (Tₐ ∪ ↑A₀ ∪ {φₐ}).Model M := by
          rw [Theory.model_union_iff, Theory.model_union_iff, Theory.model_singleton_iff]
          exact ⟨⟨M.is_model, hMA₀⟩ ,hMφ⟩
        exact ⟨MSModelType.mk M.Carrier⟩
      -- χ ∈ Δ, up to equivalence between sentences and formulas
      have hχ_in_Δ : Δ (equivSentence.symm χ) := by
        rw [χ_def, equivSentence_symm_bigAnd]
        apply ImpClass.bigAnd
        intro φ' hφ'
        obtain ⟨ξ, hξ, rfl⟩ := List.mem_map.mp hφ'
        exact ((Finset.mem_filter.mp (Finset.mem_toList.mp hξ)).2).1
      -- (∼ χ) ∈  Δ, up to equivalences between sentences and formulas
      have h_not_χ_in_Δ : Δ (equivSentence.symm (∼ χ)) := by
        rw [equivSentence_symm_not]
        exact ImpClass.imp _ _ hχ_in_Δ ImpClass.falsum
      -- So ∼χ ∈ Γ
      have h_not_χ_in_Γ : ∼ χ ∈ Γ := ⟨h_not_χ_in_Δ, h_φ_imp_not_χ⟩
      -- But N ⊨ Γ, so N ⊨ ∼χ
      haveI : N.Carrier ⊨ Γ := hNΓ
      have hN_not_χ : N ⊨ ∼ χ := Theory.realize_sentence_of_mem (T := Γ) h_not_χ_in_Γ
      -- But N ⊨ χ (since N models all of A₀ ⊆ A)
      have hN_χ : N ⊨ χ := by
        rw [χ_def, Sentence.Realize, Formula.Realize, realize_bigAnd]
        intro ξ hξ
        exact ((Finset.mem_filter.mp (Finset.mem_toList.mp hξ)).2).2
      -- Contradiction
      rw [Sentence.realize_not] at hN_not_χ
      exact hN_not_χ hN_χ
    · intro x hx
      rcases hT₀ hx with (hxT | hxA) | hxφ
      · exact Set.mem_union_left _ (Set.mem_union_left _ hxT)
      · exact Set.mem_union_left _ (Set.mem_union_right _
          (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hx, hxA⟩)))
      · exact Set.mem_union_right _ hxφ
  -- Extract model M from (Tₐ ∪ A ∪ {φₐ})
  let ⟨M⟩ := hA_sat
  letI : L[[α]].MSStructure M.Carrier := M.struc
  letI : L.MSStructure M.Carrier := (L.lhomWithConstants α).reduct M.Carrier
  have hMTₐ : M.Carrier ⊨ Tₐ :=
    M.is_model.mono (Set.subset_union_left.trans Set.subset_union_left)
  haveI hMT : M.Carrier ⊨ T := (LHom.onTheory_model (φ := L.lhomWithConstants α) T).1 hMTₐ
  have hMA : M.Carrier ⊨ A :=
    M.is_model.mono (Set.subset_union_right.trans Set.subset_union_left)
  have hM_φ : M ⊨ φₐ :=
    Theory.realize_sentence_of_mem (T := Tₐ ∪ A ∪ {φₐ}) (Set.mem_union_right _ rfl)
  let v : α →ₛ M.Carrier := ⟨fun s a => (L.con s a : M.Carrier s)⟩
  have hv_φ : φ.Realize v := by
    exact (realize_equivSentence M.Carrier φ).1 hM_φ
  let M' : T.MSModelType := MSModelType.mk M.Carrier
    (struc := (L.lhomWithConstants α).reduct M.Carrier) (is_model := hMT)
    (nonempty' := M.nonempty')
  -- M and N agree on all Δ-formulas (using that Δ is closed under negation)
  refine ⟨M', N', v, w, hv_φ, hw_not_φ, ?_⟩
  intro ψ hψ
  constructor
  · -- If M ⊨ ψ(v), show N ⊨ ψ(w)
    intro hMψ
    -- ψ(v) holds in M, so equivSentence ψ holds in M (as L[[α]]-sentence)
    have hMψₐ : M ⊨ equivSentence ψ :=
      (realize_equivSentence M.Carrier ψ).2 hMψ
    -- equivSentence ψ ∈ A would follow if Δ ψ and M ⊨ equivSentence ψ
    -- But A is what N models, not M. Instead: equivSentence ψ ∈ Γ (since φ ⟹ ψ ∈ Γ? No...)
    -- Actually: N models Γ, and if ψ ∈ Δ and N doesn't model ψ, then N models ¬ψ,
    -- so ¬ψ ∈ A, so M models ¬ψ, contradicting M ⊨ ψ.
    by_contra hNψ_not
    have hNψ_not' : N ⊨ equivSentence ψ.not := by
      rw [equivSentence_not, Sentence.realize_not]
      exact fun h => hNψ_not ((realize_equivSentence N.Carrier ψ).1 h)
    -- ψ.not ∈ Δ (Δ is closed under negation via imp + falsum)
    have hψ_not_Δ : Δ ψ.not := ImpClass.imp _ _ hψ ImpClass.falsum
    -- So equivSentence ψ.not ∈ A
    have : equivSentence ψ.not ∈ A := by
      refine ⟨?_, hNψ_not'⟩
      rw [equivSentence.symm_apply_apply]
      exact hψ_not_Δ
    -- M models A, so M ⊨ equivSentence ψ.not
    have hM_not_ψ : M ⊨ equivSentence ψ.not :=
      Theory.realize_sentence_of_mem (T := A) this
    -- But equivSentence ψ.not = (equivSentence ψ).not
    rw [equivSentence_not, Sentence.realize_not] at hM_not_ψ
    exact hM_not_ψ hMψₐ
  · -- If N ⊨ ψ(w), show M ⊨ ψ(v)
    intro hNψ
    have hNψₐ : N ⊨ equivSentence ψ :=
      (realize_equivSentence N.Carrier ψ).2 hNψ
    -- equivSentence ψ ∈ A (since Δ ψ and N ⊨ equivSentence ψ)
    have hψ_in_A : equivSentence ψ ∈ A := by
      refine ⟨?_, hNψₐ⟩
      rw [equivSentence.symm_apply_apply]
      exact hψ
    -- M models A
    have : M ⊨ equivSentence ψ :=
      Theory.realize_sentence_of_mem (T := A) hψ_in_A
    exact (realize_equivSentence M.Carrier ψ).1 this

end BoundedFormula

end MSLanguage

end MSFirstOrder
