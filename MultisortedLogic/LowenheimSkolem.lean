/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, Mathias Stout
-/
module

public import MultisortedLogic.Skolem
public import MultisortedLogic.Satisfiability

/-!
# Large models and the Löwenheim–Skolem theorems

The size of a structure `M` is measured by `Σ s, M s`, the union of its sorts.

## Main definitions

* `distinctConstantsTheory L A`: the `L[[α]]`-sentences saying that the constants for the names in
  `A : ∀ s, Set (α s)` are distinct, sort by sort.

## Main results

* `Theory.Model.isSatisfiable'`: a model in any universe shows that its theory is satisfiable. The
  model is shrunk to the universe of the language by a small elementary substructure.
* `Theory.ModelsFormula.realize_sentence`, `Theory.ModelsFormula.realize_formula`: a consequence
  of `T` holds in every model of `T`, in every universe.
* `Theory.exists_large_model_of_infinite_model`: a theory with a model that is infinite at a sort
  `t` has models with arbitrarily many elements of sort `t`, by compactness.
* `exists_elementaryEmbedding_card_eq_of_le`, `exists_elementaryEmbedding_card_eq_of_ge`: the
  downward and upward Löwenheim–Skolem theorems, for structures in the universe of the cardinal.
* `exists_elementarilyEquivalent_card_eq`, `Theory.exists_model_card_eq`: their consequences for
  elementary equivalence and for models of a theory.

## Implementation notes

Mathlib states the size condition on the language as `lift L.card ≤ lift κ`. Here the sorts count
too: the condition is `lift (lift #S + L.card) ≤ lift κ`.

## References

This file was originally based on `Mathlib/ModelTheory/Satisfiability.lean` and
`Mathlib/ModelTheory/Skolem.lean`, both by Aaron Anderson.
-/

@[expose] public section

universe u v w w' z u'

namespace ManySorted.Language

open Arity Structure Cardinal

variable {S : Type z} {L : Language.{u, v} S} {M : S → Type w} {N : S → Type w'}
  [L.Structure M] [L.Structure N]

/-! ### Satisfiability in every universe -/

namespace Theory

variable {T : L.Theory}

/-- **A model in any universe shows that a theory is satisfiable.** A small elementary
substructure of the model, shrunk to the universe of the language, is a realization. -/
theorem Model.isSatisfiable' (M : S → Type w) [L.Structure M] [∀ s, Nonempty (M s)] [M ⊨ T] :
    T.IsSatisfiable := by
  obtain ⟨A, hA⟩ := exists_small_elementarySubstructure L (M := M)
  let e : ∀ s, A s ≃ Shrink.{max z u v} (A s) := fun s => @equivShrink _ (hA s)
  let := Equiv.inducedStructure L e
  have : (fun s => Shrink.{max z u v} (A s)) ⊨ T := (Equiv.inducedStructureEquiv e).theory_model
  have : ∀ s, Nonempty (Shrink.{max z u v} (A s)) := fun s => (A.nonempty s).map (e s)
  exact Model.isSatisfiable (fun s => Shrink.{max z u v} (A s))

/-- **A consequence of `T` holds in every model of `T`**, in every universe. -/
theorem ModelsFormula.realize_sentence {φ : L.Sentence} (h : T ⊨ᵇ φ) (M : S → Type w)
    [L.Structure M] [∀ s, Nonempty (M s)] [M ⊨ T] : M ⊨ φ := by
  by_contra hφ
  have : M ⊨ T ∪ {φ.not} :=
    model_union_iff.2 ⟨inferInstance, model_singleton_iff.2 (Formula.realize_not.2 hφ)⟩
  obtain ⟨r⟩ := Model.isSatisfiable' (T := T ∪ {φ.not}) M
  have : r.carrier ⊨ T := r.model.mono Set.subset_union_left
  exact (realize_sentence_of_mem (T := T ∪ {φ.not}) (Set.mem_union_right _ rfl) :
    r.carrier ⊨ φ.not) (h r.carrier PUnit.unit)

/-- **A consequence of `T` holds of every tuple in every model of `T`**, in every universe. -/
theorem ModelsFormula.realize_formula {σ : Arity S} {φ : L.Formula σ} (h : T ⊨ᵇ φ)
    (M : S → Type w) [L.Structure M] [∀ s, Nonempty (M s)] [M ⊨ T] (xs : M [^] σ) :
    φ.Realize xs := by
  have hall : T ⊨ᵇ (Formula.all σ (φ.relabel fun _ => Idx.right) : L.Sentence) :=
    fun N _ _ _ _ => Formula.realize_all.2 fun ys => by
      rw [Formula.realize_relabel, Interpret.comap_right]
      exact h N ys
  have := Formula.realize_all.1 (hall.realize_sentence M) xs
  rwa [Formula.realize_relabel, Interpret.comap_right] at this

end Theory

/-! ### Distinct constants and large models -/

section DistinctConstants

variable {α : S → Type u'}

variable (L) in
/-- The sentences saying that the constants for the names in `A` are distinct, sort by sort. -/
def distinctConstantsTheory (A : ∀ s, Set (α s)) : L[[α]].Theory :=
  {ψ | ∃ (s : S) (a b : α s), a ∈ A s ∧ b ∈ A s ∧ a ≠ b ∧ ψ = ∼(Term.con L a =' Term.con L b)}

theorem distinctConstantsTheory_mono {A B : ∀ s, Set (α s)} (h : A ≤ B) :
    L.distinctConstantsTheory A ⊆ L.distinctConstantsTheory B := by
  rintro _ ⟨s, a, b, ha, hb, hab, rfl⟩
  exact ⟨s, a, b, h s ha, h s hb, hab, rfl⟩

/-- The constants for the names in `A` are distinct exactly when the values of the names are
injective on `A`. -/
theorem realizeWith_distinctConstantsTheory_iff (v : ∀ s, α s → M s) (A : ∀ s, Set (α s)) :
    (L.distinctConstantsTheory A).RealizeWith v PUnit.unit ↔ ∀ s, Set.InjOn (v s) (A s) := by
  refine ⟨fun h s a ha b hb hab => by_contra fun hne => ?_, ?_⟩
  · exact h _ ⟨s, a, b, ha, hb, hne, rfl⟩ hab
  · rintro h _ ⟨s, a, b, ha, hb, hab, rfl⟩ (hab' : v s a = v s b)
    exact hab (h s ha hb hab')

end DistinctConstants

namespace Theory

variable {α : S → Type u'}

/-- **Distinct constants by compactness**: if `T` has a model with nonempty sorts that is infinite
at every sort where `A` is nonempty, then `T` with distinct constants for the names in `A` is
satisfiable. -/
theorem isSatisfiable_onTheory_union_distinctConstantsTheory (T : L.Theory)
    (A : ∀ s, Set (α s)) (M : S → Type w) [L.Structure M] [∀ s, Nonempty (M s)] [M ⊨ T]
    (hM : ∀ s, (A s).Nonempty → Infinite (M s)) :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory A).IsSatisfiable := by
  classical
  -- the finite stages
  let A' (F : Finset (Σ s, α s)) (s : S) : Set (α s) := {a | a ∈ A s ∧ ⟨s, a⟩ ∈ F}
  have hsat (F : Finset (Σ s, α s)) :
      ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory (A' F)).IsSatisfiable := by
    have hv (s : S) : ∃ v : α s → M s, Set.InjOn v (A' F s) := by
      rcases (A' F s).eq_empty_or_nonempty with h | h
      · exact ⟨fun _ => Classical.arbitrary _, by simp [h]⟩
      have hsub : A' F s ⊆ A s := fun _ ha => ha.1
      have := hM s (h.mono hsub)
      have hfin : (A' F s).Finite :=
        (F.finite_toSet.preimage sigma_mk_injective.injOn).subset fun _ ha => ha.2
      obtain ⟨f⟩ := lift_mk_le'.1 ((lift_lt_aleph0.2 hfin.lt_aleph0).le.trans
        (aleph0_le_lift.2 (aleph0_le_mk (M s))))
      refine ⟨fun a => if ha : a ∈ A' F s then f ⟨a, ha⟩ else Classical.arbitrary _,
        fun a ha b hb hab => ?_⟩
      simp only [ha, hb, dite_true] at hab
      exact congrArg Subtype.val (f.injective hab)
    choose v hv using hv
    let := withConstantsStructure (L := L) v
    have : M ⊨ (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory (A' F) :=
      model_union_iff.2 ⟨(LHom.onTheory_model _ T).2 inferInstance,
        ⟨(realizeWith_distinctConstantsTheory_iff v (A' F)).2 hv⟩⟩
    exact Model.isSatisfiable' M
  -- compactness
  have hsub : (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory A ⊆
      ⋃ F, ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory (A' F)) := by
    rintro ψ (hψ | ⟨s, a, b, ha, hb, hab, rfl⟩)
    · exact Set.mem_iUnion.2 ⟨∅, Or.inl hψ⟩
    · refine Set.mem_iUnion.2 ⟨{⟨s, a⟩, ⟨s, b⟩}, Or.inr ⟨s, a, b, ⟨ha, by simp⟩, ⟨hb, by simp⟩,
        hab, rfl⟩⟩
  have hdir : Directed (· ⊆ ·) fun F =>
      (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory (A' F) := fun F G =>
    ⟨F ∪ G, Set.union_subset_union_right _ (distinctConstantsTheory_mono fun s _ ha =>
        ⟨ha.1, Finset.mem_union_left _ ha.2⟩),
      Set.union_subset_union_right _ (distinctConstantsTheory_mono fun s _ ha =>
        ⟨ha.1, Finset.mem_union_right _ ha.2⟩)⟩
  refine FormulaSet.IsFinitelySatisfiable.isSatisfiable fun T₀ hT₀ => ?_
  obtain ⟨F, hF⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion (hT₀.trans hsub)
  exact (hsat F).mono hF

/-- **Large models**: a theory with a model that is infinite at a sort `t` has, for every cardinal
`κ`, a model with at least `κ` elements of sort `t`. -/
theorem exists_large_model_of_infinite_model (T : L.Theory) (t : S) (κ : Cardinal.{w'})
    (M : S → Type w) [L.Structure M] [∀ s, Nonempty (M s)] [M ⊨ T] [Infinite (M t)] :
    ∃ (N : S → Type (max z u v w')) (_ : L.Structure N) (_ : ∀ s, Nonempty (N s)) (_ : N ⊨ T),
      lift.{max z u v} κ ≤ lift.{w'} #(N t) := by
  let α (s : S) : Type w' := PLift (s = t) × κ.out
  obtain ⟨r⟩ := isSatisfiable_onTheory_union_distinctConstantsTheory T
    (fun s => (Set.univ : Set (α s))) M fun s ⟨⟨⟨h⟩, _⟩, _⟩ => by subst h; infer_instance
  let : L.Structure r.carrier := (L.lhomWithConstants α).reduct r.carrier
  have hr := r.realize
  rw [← withConstantsStructure_reduct r.str] at hr
  let v := constants (L := L) (M := r.carrier) (α := α)
  have hr : FormulaSet.RealizeWith ((L.lhomWithConstants α).onTheory T ∪
      L.distinctConstantsTheory fun s => Set.univ) v PUnit.unit := hr
  refine ⟨r.carrier, inferInstance, inferInstance, ?_, ?_⟩
  · let := withConstantsStructure (L := L) v
    exact (LHom.onTheory_model (L.lhomWithConstants α) T).1 ⟨fun ψ hψ => hr ψ (Or.inl hψ)⟩
  · have hinj := (realizeWith_distinctConstantsTheory_iff _ _).1 fun ψ hψ => hr ψ (Or.inr hψ)
    have := lift_mk_le_lift_mk_of_injective (f := fun x : κ.out => v t (⟨rfl⟩, x)) fun x y hxy =>
      congrArg Prod.snd (hinj t (Set.mem_univ _) (Set.mem_univ _) hxy)
    rw [mk_out] at this
    rw [← lift_umax.{w', max z u v}]
    exact this

end Theory

/-! ### The Löwenheim–Skolem theorems -/

/-- **A structure whose size is a cardinal `κ` of universe `w'` is isomorphic to a structure in
universe `w'`**, of size `κ`. -/
theorem exists_equiv_of_lift_card_eq (κ : Cardinal.{w'})
    (h : lift.{w'} #(Σ s, M s) = lift.{max z w} κ) :
    ∃ (N : S → Type w') (_ : L.Structure N), Nonempty (M ≃[L] N) ∧ #(Σ s, N s) = lift.{z} κ := by
  rw [← mk_out κ, lift_mk_eq'] at h
  obtain ⟨e⟩ := h
  have : ∀ s, Small.{w'} (M s) := fun s =>
    small_of_injective (f := fun x => e ⟨s, x⟩) (e.injective.comp sigma_mk_injective)
  let e' (s : S) : M s ≃ Shrink.{w'} (M s) := equivShrink _
  let := Equiv.inducedStructure L e'
  refine ⟨fun s => Shrink.{w'} (M s), inferInstance, ⟨Equiv.inducedStructureEquiv e'⟩, ?_⟩
  rw [← mk_out κ]
  have := lift_mk_eq'.2 ⟨(_root_.Equiv.sigmaCongrRight fun s => (e' s).symm).trans e⟩
  rw [lift_id'.{w', z}, lift_umax] at this
  exact this

variable (L)

/-- **The downward Löwenheim–Skolem theorem**, for structures in a given universe: a structure `M`
with nonempty sorts has an elementary substructure of every infinite size `κ` at most its own and
at least the sizes of the sorts and of the symbols, as a structure in the universe of `κ`. -/
theorem exists_elementaryEmbedding_card_eq_of_le (M : S → Type w) [L.Structure M]
    [∀ s, Nonempty (M s)] (κ : Cardinal.{w'}) (h1 : ℵ₀ ≤ κ)
    (h2 : lift.{w'} (lift.{max u v} #S + L.card) ≤ lift.{max z u v} κ)
    (h3 : lift.{max z w} κ ≤ lift.{w'} #(Σ s, M s)) :
    ∃ (N : S → Type w') (_ : L.Structure N) (_ : ∀ s, Nonempty (N s)),
      Nonempty (N ↪ₑ[L] M) ∧ #(Σ s, N s) = lift.{z} κ := by
  obtain ⟨B, -, hB⟩ := exists_elementarySubstructure_card_eq L ⊥ κ h1
    (by rw [mk_eq_zero_iff.2 ⟨fun x => x.2.2⟩, lift_zero]; exact zero_le) h2 h3
  obtain ⟨N, _, ⟨e⟩, hN⟩ := exists_equiv_of_lift_card_eq (L := L) κ hB
  exact ⟨N, inferInstance, fun s => (B.nonempty s).map (e s),
    ⟨B.subtype.comp e.symm.toElementaryEmbedding⟩, hN⟩

/-- **The upward Löwenheim–Skolem theorem**: a structure `M` with nonempty sorts and an infinite
sort has an elementary extension of every size `κ` at least its own and at least the sizes of the
sorts and of the symbols, as a structure in the universe of `κ`. -/
theorem exists_elementaryEmbedding_card_eq_of_ge (M : S → Type w) [L.Structure M]
    [∀ s, Nonempty (M s)] {t : S} [Infinite (M t)] (κ : Cardinal.{w'})
    (h2 : lift.{w'} (lift.{max u v} #S + L.card) ≤ lift.{max z u v} κ)
    (h3 : lift.{w'} #(Σ s, M s) ≤ lift.{max z w} κ) :
    ∃ (N : S → Type w') (_ : L.Structure N) (_ : ∀ s, Nonempty (N s)),
      Nonempty (M ↪ₑ[L] N) ∧ #(Σ s, N s) = lift.{z} κ := by
  have h1 : ℵ₀ ≤ κ := aleph0_le_lift.1 <| (aleph0_le_lift.2 <| aleph0_le_mk_iff.2 <|
    Infinite.of_injective (fun x : M t => (⟨t, x⟩ : Σ s, M s)) sigma_mk_injective).trans h3
  -- a model of the elementary diagram of `M` with at least `κ` elements of sort `t`
  let := withConstantsStructure (L := L) fun s (x : M s) => x
  have : M ⊨ elementaryDiagram L M := ⟨(ElementaryEmbedding.refl L M).realize_elementaryDiagram⟩
  obtain ⟨N₀, str₀, _, hN₀, hκ⟩ :=
    Theory.exists_large_model_of_infinite_model (elementaryDiagram L M) t κ M
  let : L.Structure N₀ := (L.lhomWithConstants M).reduct N₀
  have hdiag : (elementaryDiagram L M).RealizeWith (constants (L := L) (M := N₀)) PUnit.unit := by
    have := hN₀.realize_of_mem
    rw [← withConstantsStructure_reduct str₀] at this
    exact this
  let j : M ↪ₑ[L] N₀ := .ofElementaryDiagram hdiag
  -- an elementary substructure of size `κ` containing the image of `M`
  obtain ⟨B, hjB, hB⟩ := exists_elementarySubstructure_card_eq L (fun s => Set.range (j s)) κ h1
    (by
      rw [← mk_out κ] at h3 ⊢
      obtain ⟨f⟩ := lift_mk_le'.1 h3
      exact lift_mk_le'.2 ⟨(_root_.Equiv.sigmaCongrRight fun s =>
        (_root_.Equiv.ofInjective (j s) (j.injective s)).symm).toEmbedding.trans f⟩)
    h2
    (by
      rw [← mk_out κ] at hκ ⊢
      rw [← lift_umax.{w', max z u w v}] at hκ
      obtain ⟨f⟩ := lift_mk_le'.1 hκ
      exact lift_mk_le'.2 ⟨f.trans ⟨_, sigma_mk_injective⟩⟩)
  -- `j` into `B`
  let j' : M ↪ₑ[L] fun s => B s := .ofMapFormula (fun s x => ⟨j s x, hjB s ⟨x, rfl⟩⟩)
    fun φ xs h => (B.subtype.map_formula φ _).1 (by
      rw [Interpret.map_map]
      exact (j.map_formula φ xs).2 h)
  obtain ⟨N, _, ⟨e⟩, hN⟩ := exists_equiv_of_lift_card_eq (L := L) κ hB
  exact ⟨N, inferInstance, fun s => ⟨e s (j' s (Classical.arbitrary _))⟩,
    ⟨e.toElementaryEmbedding.comp j'⟩, hN⟩

/-- **The Löwenheim–Skolem theorem**: a structure `M` with nonempty sorts and an infinite sort,
and an infinite cardinal `κ` at least the sizes of the sorts and of the symbols. Then a structure of
size `κ`, in the universe of `κ`, embeds elementarily into `M` or is an elementary extension of
`M`. -/
theorem exists_elementaryEmbedding_card_eq (M : S → Type w) [L.Structure M]
    [∀ s, Nonempty (M s)] {t : S} [Infinite (M t)] (κ : Cardinal.{w'}) (h1 : ℵ₀ ≤ κ)
    (h2 : lift.{w'} (lift.{max u v} #S + L.card) ≤ lift.{max z u v} κ) :
    ∃ (N : S → Type w') (_ : L.Structure N) (_ : ∀ s, Nonempty (N s)),
      (Nonempty (N ↪ₑ[L] M) ∨ Nonempty (M ↪ₑ[L] N)) ∧ #(Σ s, N s) = lift.{z} κ := by
  rcases le_total (lift.{max z w} κ) (lift.{w'} #(Σ s, M s)) with h | h
  · obtain ⟨N, _, _, hN, hκ⟩ := exists_elementaryEmbedding_card_eq_of_le L M κ h1 h2 h
    exact ⟨N, inferInstance, inferInstance, Or.inl hN, hκ⟩
  · obtain ⟨N, _, _, hN, hκ⟩ := exists_elementaryEmbedding_card_eq_of_ge L M (t := t) κ h2 h
    exact ⟨N, inferInstance, inferInstance, Or.inr hN, hκ⟩

/-- A structure with nonempty sorts and an infinite sort is elementarily equivalent to a structure
of every infinite size `κ` at least the sizes of the sorts and of the symbols, in the universe of
`κ`. -/
theorem exists_elementarilyEquivalent_card_eq (M : S → Type w) [L.Structure M]
    [∀ s, Nonempty (M s)] {t : S} [Infinite (M t)] (κ : Cardinal.{w'}) (h1 : ℵ₀ ≤ κ)
    (h2 : lift.{w'} (lift.{max u v} #S + L.card) ≤ lift.{max z u v} κ) :
    ∃ (N : S → Type w') (_ : L.Structure N) (_ : ∀ s, Nonempty (N s)),
      L.ElementarilyEquivalent M N ∧ #(Σ s, N s) = lift.{z} κ := by
  obtain ⟨N, _, _, hN | hN, hκ⟩ := exists_elementaryEmbedding_card_eq L M (t := t) κ h1 h2
  · exact ⟨N, inferInstance, inferInstance, hN.some.elementarilyEquivalent.symm, hκ⟩
  · exact ⟨N, inferInstance, inferInstance, hN.some.elementarilyEquivalent, hκ⟩

variable {L}

/-- A theory with a model that has an infinite sort has a model of every infinite size `κ` at
least the sizes of the sorts and of the symbols, in the universe of `κ`. -/
theorem Theory.exists_model_card_eq {T : L.Theory} (M : S → Type w) [L.Structure M]
    [∀ s, Nonempty (M s)] [M ⊨ T] {t : S} [Infinite (M t)] (κ : Cardinal.{w'}) (h1 : ℵ₀ ≤ κ)
    (h2 : lift.{w'} (lift.{max u v} #S + L.card) ≤ lift.{max z u v} κ) :
    ∃ (N : S → Type w') (_ : L.Structure N) (_ : ∀ s, Nonempty (N s)) (_ : N ⊨ T),
      #(Σ s, N s) = lift.{z} κ := by
  obtain ⟨N, _, _, hN, hκ⟩ := exists_elementarilyEquivalent_card_eq L M (t := t) κ h1 h2
  exact ⟨N, inferInstance, inferInstance, hN.theory_model, hκ⟩

end ManySorted.Language
