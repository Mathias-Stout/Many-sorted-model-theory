
import ProdExpr.Ultraproducts
import ProdExpr.Skolem
import ProdExpr.Bundled

universe u v z u' v' w w' w''

namespace MSFirstOrder
namespace MSLanguage

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
  {M : Fam.{w} Sorts} {N : Fam Sorts} {P : Fam Sorts}
  [i : L.MSStructure M] [L.MSStructure N] [L.MSStructure P]
  {α : Fam.{u'} Sorts} {β : Fam.{v'} Sorts} {γ : Fam Sorts}
  {s : Sorts} {t : Sorts}

namespace Theory
variable (T : L.Theory)
/-- A theory is satisfiable if a structure models it. -/
def IsSatisfiable : Prop :=
  Nonempty (MSModelType.{u, v, z, (max u v z)} T)

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def IsFinitelySatisfiable (T : L.Theory) : Prop :=
  ∀ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T → IsSatisfiable (T0 : L.Theory)

variable {T} {T' : L.Theory}

/-- Any model of a theory witnesses satisfiability, using Skolemization to shrink to the right
universe level. -/
theorem Model.isSatisfiable [∀ {s : Sorts}, Nonempty (M s)] [M ⊨ T] :
    T.IsSatisfiable := by
  classical
  -- Get an elementary substructure that is small in each sort
  obtain ⟨S, hSmall⟩ := exists_small_elementarySubstructure L (M := M)
  -- S models T because it's an elementary substructure
  haveI : S ⊨ T := inferInstance
  -- S is nonempty at each sort because it's elementarily equivalent to M
  haveI hSNonempty : ∀ s, Nonempty (S s) := fun s => S.elementarilyEquivalent.symm.nonempty
  -- Define the shrunk carrier at universe max u v z
  let N : Fam Sorts := ⟨fun s => Shrink (S s)⟩
  -- Build equivalence between S and N using equivShrink for each sort
  haveI : ∀ s, Small.{max u v z} (S s) := hSmall
  let e : S ≃ₛ N := Fam.MSEquiv.fromEquivs (fun s => equivShrink (S s))
  -- Transfer the structure to N
  letI : L.MSStructure N := Equiv.inducedStructure e
  -- The equivalence becomes an L-isomorphism
  let φ : S ≃[L] N := Equiv.inducedStructureEquiv e
  -- Transfer the theory model via the isomorphism
  haveI hModel : N ⊨ T := StrongHomClass.theory_model φ
  -- Nonemptiness transfers through the equivalence
  haveI hNonempty : ∀ {s}, Nonempty (N s) := fun {s} =>
    Nonempty.map (equivShrink (S s)) (hSNonempty s)
  exact ⟨MSModelType.mk N (struc := Equiv.inducedStructure e) (is_model := hModel)
    (nonempty' := hNonempty)⟩

theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable := by
  obtain ⟨M⟩ := h
  exact ⟨MSModelType.mk M.Carrier (struc := M.struc)
    (is_model := @Theory.Model.mono _ _ _ M.struc T T' M.is_model hs)
    (nonempty' := M.nonempty')⟩

theorem IsSatisfiable.isFinitelySatisfiable (h : T.IsSatisfiable) : T.IsFinitelySatisfiable :=
  fun _ => h.mono

/-- The **Compactness Theorem of first-order logic**: A theory is satisfiable if and only if it is
finitely satisfiable. -/
theorem isSatisfiable_iff_isFinitelySatisfiable {T : L.Theory} :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  ⟨Theory.IsSatisfiable.isFinitelySatisfiable, fun h => by
    classical
      -- For each finite subtheory T0, get the model directly
      let getModel : (T0 : Finset T) →
        MSModelType (T0.map (Function.Embedding.subtype fun x => x ∈ T) : L.Theory) :=
        fun T0 =>
          (h (T0.map (Function.Embedding.subtype fun x => x ∈ T)) T0.map_subtype_subset).some
      -- The ultrafilter on finite subsets of T
      let u := Ultrafilter.of (Filter.atTop : Filter (Finset T))
      -- Register structure and nonemptiness as instances (use letI for transparency)
      letI hstruc : ∀ T0, L.MSStructure ((getModel T0).Carrier) := fun T0 => (getModel T0).struc
      letI hnonempty : ∀ T0 s, Nonempty ((getModel T0).Carrier s) :=
        fun T0 s => (getModel T0).nonempty'
      have h' : @Theory.Model _ L (Ultraproduct (fun T0 => (getModel T0).Carrier) u)
          (Ultraproduct.structure (fun T0 => (getModel T0).Carrier) u) T := by
        refine ⟨fun φ hφ => ?_⟩
        apply (@Ultraproduct.sentence_realize Sorts (Finset T) (fun T0 => (getModel T0).Carrier) L
          hstruc u hnonempty φ).mpr
        refine Filter.Eventually.filter_mono (Ultrafilter.of_le _) ?_
        rw [Filter.eventually_atTop]
        refine ⟨{⟨φ, hφ⟩}, fun s hs => ?_⟩
        have hmem : φ ∈ (s.map (Function.Embedding.subtype fun x => x ∈ T) : L.Theory) := by
          simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe,
            Subtype.exists, exists_and_right, exists_eq_right]
          exact ⟨hφ, hs (Finset.mem_singleton_self _)⟩
        exact @Theory.realize_sentence_of_mem _ _ _
          (getModel s).struc _ (getModel s).is_model _ hmem
      exact ⟨MSModelType.mk (Ultraproduct (fun T0 => (getModel T0).Carrier) u)
        (struc := Ultraproduct.structure _ u) (is_model := h')
        (nonempty' := Ultraproduct.instNonemptyUltraproduct _)⟩⟩

theorem isSatisfiable_directed_union_iff {ι : Type*} [Nonempty ι] {T : ι → L.Theory}
    (h : Directed (· ⊆ ·) T) : Theory.IsSatisfiable (⋃ i, T i) ↔ ∀ i, (T i).IsSatisfiable := by
  refine ⟨fun h' i => h'.mono (Set.subset_iUnion _ _), fun h' => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable, IsFinitelySatisfiable]
  intro T0 hT0
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_biUnion hT0
  exact (h' i).mono hi

/-- If a theory has a model where a given sort admits enough distinct constants, then the theory
with those constants is satisfiable. -/
theorem isSatisfiable_union_distinctConstantsAtSortTheory_of_card_le (T : L.Theory) {t : Sorts}
    (s : Set (α t)) (M : Fam.{w'} Sorts) [L.MSStructure M] [M ⊨ T]
    [∀ s, Nonempty (M s)]
    (h : Cardinal.lift.{w'} (Cardinal.mk s) ≤ Cardinal.lift.{u'} (Cardinal.mk (M t))) :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsAtSortTheory t s).IsSatisfiable := by
  classical
  haveI : Inhabited (M t) := Classical.inhabited_of_nonempty (inferInstance : Nonempty (M t))
  rw [Cardinal.lift_mk_le'] at h
  let f : s ↪ M t := h.some
  let g : α t → M t := Function.extend (fun x : s => (x : α t)) (fun x => f x) default
  let hconstStr : (constantsOn α).MSStructure M :=
    constantsOn.structure ⟨ fun s' a => by
      classical
      by_cases hst : s' = t
      · cases hst
        exact g a
      · exact Classical.choice (inferInstance )⟩
  letI : (constantsOn α).MSStructure M := hconstStr
  have : M ⊨ (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsAtSortTheory t s := by
    refine ((LHom.onTheory_model _ _).2 inferInstance).union ?_
    rw [model_distinctConstantsAtSortTheory]
    intro a ha b hb hab
    have hcon_apply (i : α t) : (L.con t i : M t) = g i := by
      -- interpret constants via the chosen `constantsOn` structure
      change
        @MSStructure.funMap _ (L.sum (constantsOn α)) M _ _ _ (Sum.inr i : L[[α]].Constants t)
          (default : Signature.nil.Interpret M) = g i
      have hsum :
          MSStructure.funMap (L := L.sum (constantsOn α)) (Sum.inr i : L[[α]].Constants t)
              (default : Signature.nil.Interpret M) =
            MSStructure.funMap (L := constantsOn α) (σ := ⦃⦄) i default  := by
        simpa using
          congrArg (fun fn => fn (default : Signature.nil.Interpret M))
            (funMap_sumInr (L₁ := L) (L₂ := constantsOn α) (S' := M)
              (σ := Signature.nil) (t := t) (f := (i : (constantsOn α).Functions .nil t)))
      have hconst : @MSStructure.funMap _ (constantsOn α) M hconstStr ⦃⦄ _ i default = g i := by
        change dite (t = t) (fun h : t = t => h ▸ g i) _ = g i
        exact dif_pos rfl

      exact hsum.trans hconst
    have hab' : g a = g b := by
      exact (hcon_apply a).symm.trans (hab.trans (hcon_apply b))
    have hfa : g a = f ⟨a, ha⟩ := by
      simpa [g] using
        (Subtype.coe_injective.extend_apply (g := fun x : s => f x) (e' := default)
          ⟨a, ha⟩)
    have hfb : g b = f ⟨b, hb⟩ := by
      simpa [g] using
        (Subtype.coe_injective.extend_apply (g := fun x : s => f x) (e' := default)
          ⟨b, hb⟩)
    have : f ⟨a, ha⟩ = f ⟨b, hb⟩ := by simpa [hfa, hfb] using hab'
    exact congrArg Subtype.val (f.injective this)
  haveI : M ⊨ (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsAtSortTheory t s := this
  exact
    Theory.Model.isSatisfiable
      (T := (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsAtSortTheory t s) (M := M)

theorem isSatisfiable_union_distinctConstantsAtSortTheory_of_infinite (T : L.Theory) {t : Sorts}
    (s : Set (α t)) (M : Fam.{w'} Sorts) [L.MSStructure M] [M ⊨ T]
    [∀ s, Nonempty (M s)] [Infinite (M t)] :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsAtSortTheory t s).IsSatisfiable := by
  classical
    rw [distinctConstantsAtSortTheory_eq_iUnion, Set.union_iUnion, isSatisfiable_directed_union_iff]
    · intro u
      apply isSatisfiable_union_distinctConstantsAtSortTheory_of_card_le (T := T) (t := t)
        (s := ((u.map (Function.Embedding.subtype fun x => x ∈ s) : Finset (α t)) : Set (α t)))
        (M := M)
      -- lift both sides through a common universe to avoid mismatch
      let u' : Finset (α t) := u.map (Function.Embedding.subtype fun x => x ∈ s)
      have h1 :
          Cardinal.lift.{w'} (Cardinal.mk ((u' : Finset (α t)) : Set (α t))) ≤
            Cardinal.lift.{w'} (Cardinal.aleph0) := by
        simp only [SetLike.coe_sort_coe, Cardinal.mk_fintype, Fintype.card_coe,
          Cardinal.lift_natCast, Cardinal.lift_aleph0, Cardinal.natCast_le_aleph0]
      have h2 :
          Cardinal.lift.{w'} (Cardinal.aleph0) ≤ Cardinal.lift.{u'} (Cardinal.mk (M t)) := by
        -- lift the standard `ℵ₀ ≤` inequality
        simp only [Cardinal.lift_aleph0, ge_iff_le, Cardinal.aleph0_le_lift, Cardinal.aleph0_le_mk]
      exact h1.trans h2
    · refine Monotone.directed_le ?_
      refine monotone_const.union ?_
      refine (monotone_distinctConstantsAtSortTheory (L := L) (α := α) t).comp ?_
      intro u v huv
      refine Finset.coe_subset.2 ?_
      exact
        (Finset.map_subset_map (f := Function.Embedding.subtype fun x => x ∈ s)).2 huv

/-- If a theory has a model with enough room in each sort for a `DepSet` of constants, then the
expanded theory asserting those constants are distinct is satisfiable. -/
theorem isSatisfiable_union_distinctConstantsTheory_of_card_le (T : L.Theory)
    (S : DepSet α) (M : Fam.{w'} Sorts) [L.MSStructure M] [M ⊨ T]
    [∀ s, Nonempty (M s)]
    (h : ∀ s, Cardinal.lift.{w'} (Cardinal.mk (S s)) ≤ Cardinal.lift.{u'} (Cardinal.mk (M s))) :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory S).IsSatisfiable := by
  classical
  let f : ∀ s, S s ↪ M s := fun s => by
    have hs := h s
    rw [Cardinal.lift_mk_le'] at hs
    exact hs.some
  let c : α →ₛ M :=
    ⟨fun s a =>
      Function.extend (fun x : S s => (x : α s)) (fun x => f s x)
        (fun _ : α s => Classical.choice (inferInstance : Nonempty (M s))) a⟩
  let hconstStr : (constantsOn α).MSStructure M := constantsOn.structure c
  letI : (constantsOn α).MSStructure M := hconstStr
  have : M ⊨ (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory S := by
    refine ((LHom.onTheory_model _ _).2 inferInstance).union ?_
    rw [model_distinctConstantsTheory]
    intro t a ha b hb hab
    have hcon_apply (i : α t) : (L.con t i : M t) = c t i := by
      change
        @MSStructure.funMap _ (L.sum (constantsOn α)) M _ ⦃⦄ _ (Sum.inr i)
          (default : Signature.nil.Interpret M) = c t i
      have hsum :
          MSStructure.funMap (L := L.sum (constantsOn α)) (σ := ⦃⦄) (Sum.inr i)
              (default : Signature.nil.Interpret M) =
            MSStructure.funMap (L := constantsOn α) (σ := ⦃⦄) i (default : Signature.nil.Interpret M) := by
        simpa using
          congrArg (fun fn => fn (default : Signature.nil.Interpret M))
            (funMap_sumInr (L₁ := L) (L₂ := constantsOn α) (S' := M)
              (σ := Signature.nil) (t := t) (f := (i : (constantsOn α).Functions .nil t)))
      have hconst :
          @MSStructure.funMap _ (constantsOn α) M hconstStr ⦃⦄ _ i
              (default : Signature.nil.Interpret M) = c t i := by
        simp only [PUnit.default_eq_unit, Fam.FamMap.mk_apply, c]
        rfl
      exact hsum.trans hconst
    have hab' : c t a = c t b := by
      exact (hcon_apply a).symm.trans (hab.trans (hcon_apply b))
    have hfa : c t a = f t ⟨a, ha⟩ := by
      simpa [c] using
        (Subtype.coe_injective.extend_apply (g := fun x : S t => f t x)
          (e' := fun _ : α t => Classical.choice (inferInstance : Nonempty (M t)))) ⟨a, ha⟩
    have hfb : c t b = f t ⟨b, hb⟩ := by
      simpa [c] using
        (Subtype.coe_injective.extend_apply (g := fun x : S t => f t x)
          (e' := fun _ : α t => Classical.choice (inferInstance : Nonempty (M t)))) ⟨b, hb⟩
    have : f t ⟨a, ha⟩ = f t ⟨b, hb⟩ := by simpa [hfa, hfb] using hab'
    exact congrArg Subtype.val ((f t).injective this)
  haveI : M ⊨ (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory S := this
  exact Theory.Model.isSatisfiable
    (T := (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory S) (M := M)

/-- If `M` is infinite at every sort where `S` is nonempty, then the constants in `S` can be made
pairwise distinct (within each sort) over `M`. -/
theorem isSatisfiable_union_distinctConstantsTheory_of_infinite_on_nonempty_sorts (T : L.Theory)
    (S : DepSet α) (M : Fam.{w'} Sorts) [L.MSStructure M] [M ⊨ T]
    [∀ s, Nonempty (M s)]
    (hInf : ∀ s, (S s).Nonempty → Infinite (M s)) :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory S).IsSatisfiable := by
  classical
  rw [distinctConstantsTheory_eq_iUnion, Set.union_iUnion, isSatisfiable_directed_union_iff]
  · intro u
    let Su : DepSet α :=
      DepSet.ofSigma (α := α)
        ((((u.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) : Set (Sigma α)))
    have hSuS : Su ⊆ S := by
      intro x hx
      change x ∈
          ((((u.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) :
            Set (Sigma α))) at hx
      simp only [Finset.mem_coe, Finset.mem_map, Function.Embedding.coe_subtype] at hx
      rcases hx with ⟨y, hyu, hEq⟩
      simpa [hEq] using y.2
    apply isSatisfiable_union_distinctConstantsTheory_of_card_le (T := T) (S := Su) (M := M)
    intro t
    rcases (Su t).eq_empty_or_nonempty with hSuEmpty | hSuNonempty
    · simp only [hSuEmpty, Cardinal.mk_eq_zero, Cardinal.lift_zero, zero_le]
    have hSuFinite : Su.IsFinite := by
      exact DepSet.ofSigma_finset_isFinite
        (((u.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)))
    have hSigmaFinite : Finite (Sigma (Su : Fam Sorts)) :=
      (DepSet.isFinite_iff_finite_sigma (S := Su)).1 hSuFinite
    have hSortFinite : Finite (Su t) := by
      letI : Finite (Sigma (Su : Fam Sorts)) := hSigmaFinite
      refine Finite.of_injective (f := fun x : Su t => (⟨t, x⟩ : Sigma (Su : Fam Sorts))) ?_
      intro x y hxy
      cases hxy
      rfl
    letI : Fintype (Su t) := Fintype.ofFinite (Su t)
    have h1 :
        Cardinal.lift.{w'} (Cardinal.mk (Su t)) ≤ Cardinal.lift.{w'} (Cardinal.aleph0) := by
      simp only [Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_aleph0,
        Cardinal.natCast_le_aleph0]
    have hStNonempty : (S t).Nonempty := by
      exact Set.Nonempty.mono ((DepSet.le_def.mp hSuS) t) hSuNonempty
    haveI : Infinite (M t) := hInf t hStNonempty
    have h2 :
        Cardinal.lift.{w'} (Cardinal.aleph0) ≤ Cardinal.lift.{u'} (Cardinal.mk (M t)) := by
      simp only [Cardinal.lift_aleph0, ge_iff_le, Cardinal.aleph0_le_lift, Cardinal.aleph0_le_mk]
    exact h1.trans h2
  · refine Monotone.directed_le ?_
    refine monotone_const.union ?_
    refine (monotone_distinctConstantsTheory (L := L) (α := α)).comp ?_
    intro u v huv
    change
      DepSet.ofSigma (α := α)
          ((((u.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) :
            Set (Sigma α))) ⊆
        DepSet.ofSigma (α := α)
          ((((v.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) :
            Set (Sigma α)))
    change
      ((((u.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) :
        Set (Sigma α))) ⊆
      ((((v.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) :
        Set (Sigma α)))
    refine Finset.coe_subset.2 ?_
    exact (Finset.map_subset_map (f := Function.Embedding.subtype fun x => x ∈ S)).2 huv

/-- If every sort of a model is infinite, then any `DepSet` of constants can be made pairwise
distinct (within each sort) over that model. -/
theorem isSatisfiable_union_distinctConstantsTheory_of_infinite (T : L.Theory)
    (S : DepSet α) (M : Fam.{w'} Sorts) [L.MSStructure M] [M ⊨ T]
    [∀ s, Nonempty (M s)] [∀ s, Infinite (M s)] :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory S).IsSatisfiable := by
  apply isSatisfiable_union_distinctConstantsTheory_of_infinite_on_nonempty_sorts
    (L := L) (α := α) (T := T) (S := S) (M := M)
  intro s _hs
  infer_instance

/-- Any theory with an infinite model in a fixed sort has arbitrarily large models
in the sum of sorts. -/
theorem exists_large_model_of_infinite_model (T : L.Theory) (t : Sorts) (κ : Cardinal.{w})
    (M : Fam.{w'} Sorts) [L.MSStructure M] [M ⊨ T] [∀ s, Nonempty (M s)]
    [Infinite (M t)] :
    ∃ N : Theory.MSModelType.{u, v, z, max u v z w} T,
      Cardinal.lift.{max u v z w} κ ≤
        Cardinal.lift.{w} (Cardinal.mk (Σ s, N.Carrier s)) := by
  classical
  let α' : Fam.{w} Sorts := ⟨fun s => if h : s = t then κ.out else PUnit⟩
  obtain ⟨N⟩ :=
    (isSatisfiable_union_distinctConstantsAtSortTheory_of_infinite (L := L) (α := α') (T := T) (t := t)
      (s := (Set.univ : Set (α' t))) (M := M))
  letI : L[[α']].MSStructure N.Carrier := N.struc
  letI : L.MSStructure N.Carrier := (L.lhomWithConstants α').reduct N.Carrier
  have hT' : N.Carrier ⊨ (L.lhomWithConstants α').onTheory T :=
    @Theory.Model.mono _ _ _ N.struc _ _ N.is_model Set.subset_union_left
  haveI hT : N.Carrier ⊨ T := (LHom.onTheory_model (φ := L.lhomWithConstants α') T).1 hT'
  refine
    ⟨MSModelType.mk N.Carrier (struc := (L.lhomWithConstants α').reduct N.Carrier)
      (is_model := hT) (nonempty' := N.nonempty'), ?_⟩
  have hdistinct :
      N.Carrier ⊨ L.distinctConstantsAtSortTheory t (Set.univ : Set (α' t)) :=
    @Theory.Model.mono _ _ _ N.struc _ _ N.is_model Set.subset_union_right
  have hcard :
      Cardinal.lift.{max u v z w} κ ≤ Cardinal.lift.{w} (Cardinal.mk (N.Carrier t)) := by
    refine _root_.trans (Cardinal.lift_le.2 (le_of_eq (Cardinal.mk_out κ).symm)) ?_
    -- use the distinct constants to bound `κ.out` by `N.Carrier t`
    simpa [Cardinal.mk_out, dite_eq_ite, Fam.mk_apply, Cardinal.mk_univ, α',
      ge_iff_le] using
      (card_le_of_model_distinctConstantsAtSortTheory (L := L) (α := α') (s := t) (S :=
        (Set.univ : Set (α' t))) (M := N.Carrier))
  have hSigma :
      Cardinal.lift.{w} (Cardinal.mk (N.Carrier t)) ≤
        Cardinal.lift.{w} (Cardinal.mk (Σ s, N.Carrier s)) := by
    refine Cardinal.lift_le.2 ?_
    refine
      Cardinal.mk_le_of_injective (f := fun x : N.Carrier t => (Sigma.mk t x)) ?_
    intro x y hxy
    cases hxy
    rfl
  exact hcard.trans hSigma

theorem isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset {ι : Type*} (T : ι → L.Theory) :
    IsSatisfiable (⋃ i, T i) ↔ ∀ s : Finset ι, IsSatisfiable (⋃ i ∈ s, T i) := by
  classical
    refine
      ⟨fun h s => h.mono (Set.iUnion_mono fun _ => Set.iUnion_subset_iff.2 fun _ => refl _),
        fun h => ?_⟩
    rw [isSatisfiable_iff_isFinitelySatisfiable]
    intro s hs
    rw [Set.iUnion_eq_iUnion_finset] at hs
    obtain ⟨t, ht⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion (by
      exact Monotone.directed_le fun t1 t2 (h : ∀ ⦃x⦄, x ∈ t1 → x ∈ t2) =>
        Set.iUnion_mono fun _ => Set.iUnion_mono' fun h1 => ⟨h h1, refl _⟩) hs
    exact (h t).mono ht

end Theory

/-! ### Löwenheim–Skolem (many-sorted, size measured by `Σ s, M s`) -/

variable (L)
open Cardinal

/-- A version of the Downward Löwenheim–Skolem theorem for many-sorted structures, measured by
the cardinality of `Σ s, M s`. -/
theorem exists_elementaryEmbedding_card_eq_of_le [DecidableEq Sorts]
    (M : Fam.{w'} Sorts) [L.MSStructure M] [∀ s, Nonempty (M s)]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ)
    (h2 : Cardinal.lift (#Sorts) + Cardinal.lift.{w} L.card ≤
      Cardinal.lift.{max u v z} κ)
    (h3 : Cardinal.lift.{max w' z} κ ≤ Cardinal.lift.{w} (Cardinal.mk (Σ s, M s))) :
    ∃ S : MSStructureType.{u, v, z, w} L, Nonempty (S ↪ₑ[L] M) ∧
      (#(Σ s, S.1 s)) = Cardinal.lift.{z} κ := by
  obtain ⟨S, _, hS⟩ := exists_elementarySubstructure_card_eq L ∅ κ h1 (by simp) h2 h3
  have hSmallSigma : Small.{w} (Σ s, S.1 s) := by
    rw [← lift_inj.{_, w + 1}, lift_lift, lift_lift] at hS
    exact small_iff_lift_mk_lt_univ.2 (lt_of_eq_of_lt hS κ.lift_lt_univ')
  let Sf : Fam.{w'} Sorts := S
  have hSmallSort : ∀ s, Small.{w} (Sf s) := by
    intro s
    haveI : Small.{w} (Σ s', Sf s') := by
      simpa [Sf] using hSmallSigma
    refine small_of_injective
      (f := fun x : Sf s => (Sigma.mk s x : Σ s', Sf s')) ?_
    intro x y hxy
    cases hxy
    rfl
  letI : L.MSStructure Sf := by
    simpa [Sf] using (ElementarySubstructure.inducedMSStructure (L := L) (M := M) S)
  haveI : ∀ s, Nonempty (Sf s) := by
    intro s
    letI : Nonempty (M s) := (‹∀ s, Nonempty (M s)› s)
    simpa [Sf] using (S.elementarilyEquivalent.symm.nonempty (s := s))
  let N : Fam.{w} Sorts := ⟨fun s => Shrink.{w} (Sf s)⟩
  let e : Sf ≃ₛ (N : Fam.{w} Sorts) := by
    refine Fam.MSEquiv.fromEquivs ?_
    intro s
    letI : Small.{w} (Sf s) := hSmallSort s
    exact equivShrink (Sf s)
  let S' : MSStructureType.{u, v, z, w} L :=
    Fam.MSEquiv.bundledInduced (Sorts := Sorts) (M := Sf) (N := N) (L := L) e
  refine
    ⟨S',
      ⟨S.subtype.comp
        ((Fam.MSEquiv.bundledInducedEquiv
          (Sorts := Sorts) (M := Sf) (N := N) (L := L) e).symm.toElementaryEmbedding)⟩,
      lift_inj.1 (_root_.trans ?_ (by
        simpa [lift_lift] using congrArg (Cardinal.lift.{max w w' z}) hS))⟩
  simp only [S', N, Sf, Fam.MSEquiv.bundledInduced, mk_sigma, lift_sum]
  apply congrArg Cardinal.sum
  funext s
  letI : Small.{w} (Sf s) := hSmallSort s
  exact Cardinal.lift_mk_eq'.2 ⟨(equivShrink (Sf s)).symm⟩
section

/-- Upward Löwenheim–Skolem (multisorted; size measured by `Σ s, M s`):
if `κ` bounds the language+sorts and the size of `M`, and some sort of `M` is infinite,
then `M` has an elementary extension of size `κ` (measured by the sum of sorts). -/
theorem exists_elementaryEmbedding_card_eq_of_ge [DecidableEq Sorts]
    (M : Fam.{w'} Sorts) [L.MSStructure M] [∀ s, Nonempty (M s)]
    {t : Sorts} [Infinite (M t)]
    (κ : Cardinal.{w})
    (hLang :
      Cardinal.lift.{max u v w} (#Sorts) +
          Cardinal.lift.{w} L.card ≤
        Cardinal.lift.{max u v z} κ)
    (hM :
      Cardinal.lift.{w} (Cardinal.mk (Σ s, M s)) ≤
        Cardinal.lift.{max w' z} κ) :
    ∃ N : MSStructureType.{u, v, z, w}  L,
      Nonempty (M ↪ₑ[L] N.Carrier) ∧
      (Cardinal.mk (Σ s, N.Carrier s)) = Cardinal.lift.{z} κ
        := by
  classical
  have h1 : ℵ₀ ≤ κ := by
    have hSigmaInf : Infinite (Σ s, M s) := by
      refine Infinite.of_injective (f := fun x : M t => Sigma.mk t x) ?_
      intro x y hxy
      cases hxy
      rfl
    exact (Cardinal.aleph0_le_lift.1 <|
      (Cardinal.aleph0_le_lift.2 (Cardinal.aleph0_le_mk (Σ s, M s))).trans hM)
  have hConstCard : (constantsOn M).card ≤ Cardinal.mk (Σ s, M s) := by
    let f : (constantsOn M).Symbols → Σ s, M s := fun x =>
      match x with
      | Sum.inl ⟨σ, s, c⟩ =>
          match σ with
          | .nil => ⟨s, c⟩
          | .of _ => nomatch c
          | .prod _ _ => nomatch c
      | Sum.inr ⟨_, r⟩ => nomatch r
    refine Cardinal.mk_le_of_injective (f := f) ?_
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            rcases x with ⟨σx, sx, cx⟩
            rcases y with ⟨σy, sy, cy⟩
            cases σx <;> cases σy
            · simp only [constantsOn_Functions, constantsOnFunc, constantsOn_Relations,
              constantsOnFunc.eq_1, hxy, f]
            · cases cy
            · cases cy
            · cases cx
            · cases cx
            · cases cx
            · cases cx
            · cases cx
            · cases cx
        | inr y =>
            rcases y with ⟨σy, ry⟩
            cases ry
    | inr x =>
        rcases x with ⟨σx, rx⟩
        cases rx
  have hWCcard :
      Cardinal.lift.{w} (L[[M]]).card ≤
        Cardinal.lift.{max w w'} L.card + Cardinal.lift.{max u v w} (Cardinal.mk (Σ s, M s)) := by
    have hsum :
        (L[[M]]).card = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} (constantsOn M).card := by
      simpa [MSLanguage.withConstants] using
        (MSLanguage.card_sum (L := L) (L' := constantsOn M))
    rw [hsum]
    have hConstCard' : Cardinal.lift.{w} ((constantsOn M).card) ≤ Cardinal.lift.{w} (Cardinal.mk (Σ s, M s)) :=
      Cardinal.lift_le.2 hConstCard
    have hConstCard'' :
        Cardinal.lift.{max u v w} ((constantsOn M).card) ≤
          Cardinal.lift.{max u v w} (Cardinal.mk (Σ s, M s)) := by
      exact Cardinal.lift_le.mpr hConstCard
    have hAdd :
        Cardinal.lift.{w} (Cardinal.lift.{w'} L.card) +
            Cardinal.lift.{w} (Cardinal.lift.{max u v} ((constantsOn M).card))
          ≤
        Cardinal.lift.{max w w'} L.card + Cardinal.lift.{max u v w} (Cardinal.mk (Σ s, M s)) := by
      exact add_le_add (by simp [lift_lift]) (by simpa [lift_lift] using hConstCard'')
    simpa [Cardinal.lift_add, lift_lift] using hAdd
  have hLang' :
      Cardinal.lift.{max u v w} (#Sorts) +
          Cardinal.lift.{w} L.card ≤
        Cardinal.lift.{max u v z} κ := by
    exact hLang
  have hM' :
      Cardinal.lift.{w} (Cardinal.mk (Σ s, M s)) ≤
        Cardinal.lift.{max w' z} κ := by
    exact hM
  have h2 :
      Cardinal.lift (#Sorts) + Cardinal.lift.{w} (L[[M]]).card ≤
        Cardinal.lift.{max u v w' z} κ := by
    have hLang'' :
        Cardinal.lift (#Sorts) + Cardinal.lift.{max w w'} L.card ≤
          Cardinal.lift.{max u v w' z} κ := by
      have h := Cardinal.lift_le.mpr hLang
      simpa [Cardinal.lift_add, lift_lift, max_assoc, max_left_comm, max_comm] using h
    have hM'' :
        Cardinal.lift.{max u v w} (Cardinal.mk (Σ s, M s)) ≤
          Cardinal.lift.{max u v w' z} κ := by
      have h := Cardinal.lift_le.mpr hM
      simpa [lift_lift, max_assoc, max_left_comm, max_comm] using h
    calc
      Cardinal.lift (#Sorts) + Cardinal.lift.{w} (L[[M]]).card
          ≤ Cardinal.lift (#Sorts) +
              (Cardinal.lift.{max w w'} L.card + Cardinal.lift.{max u v w} (Cardinal.mk (Σ s, M s))) := by
            exact add_le_add_right hWCcard _
      _ = (Cardinal.lift (#Sorts) + Cardinal.lift.{max w w'} L.card) +
            Cardinal.lift.{max u v w} (Cardinal.mk (Σ s, M s)) := by
            rw [add_assoc]
      _ ≤ Cardinal.lift.{max u v w' z} κ + Cardinal.lift.{max u v w' z} κ := by
            exact add_le_add hLang'' hM''
      _ = Cardinal.lift.{max u v w' z} κ := by
            have hk : Cardinal.aleph0 ≤ Cardinal.lift.{max u v w' z} κ :=
              Cardinal.aleph0_le_lift.mpr h1
            simpa [lift_lift, max_assoc, max_left_comm, max_comm] using
              (by rw [Cardinal.add_eq_max hk, max_self] :
                Cardinal.lift.{max u v w' z} κ + Cardinal.lift.{max u v w' z} κ =
                  Cardinal.lift.{max u v w' z} κ)
  obtain ⟨N0, hN0⟩ :=
    Theory.exists_large_model_of_infinite_model (L := L[[M]]) (T := L.elementaryDiagram M) (t := t)
      (κ := κ) (M := M)
  obtain ⟨S, hEmb, hNκ⟩ :=
    exists_elementaryEmbedding_card_eq_of_le (L := L[[M]]) (M := N0.Carrier) κ h1 h2 (by
      simpa [lift_lift] using hN0)
  have hSdiag : (S : Fam Sorts) ⊨ L.elementaryDiagram M := by
    rcases hEmb with ⟨f⟩
    letI : (N0.Carrier : Fam Sorts) ⊨ L.elementaryDiagram M := N0.is_model
    exact (f.theory_model_iff (L.elementaryDiagram M)).2 inferInstance
  let Ndiag : (L.elementaryDiagram M).MSModelType :=
    Theory.Model.bundled (L := L[[M]]) (T := L.elementaryDiagram M) (M := (S : Fam Sorts)) hSdiag
  letI : L.MSStructure (Ndiag : Fam Sorts) := (L.lhomWithConstants M).reduct (Ndiag : Fam Sorts)
  let N := (⟨(Ndiag : Fam Sorts)⟩ : MSStructureType.{u, v, z, w} L)
  refine ⟨N, ?_, ?_⟩
  · refine ⟨?_⟩
    simpa [N] using
      (ElementaryEmbedding.ofModelsElementaryDiagram (L := L) (M := M) (N := (Ndiag : Fam Sorts)))
  · simpa [N, Ndiag, lift_lift] using hNκ

/-- A multisorted Löwenheim–Skolem dichotomy at cardinal `κ` (size measured by `Σ s, M s`):
either a size-`κ` structure elementarily embeds into `M`, or `M` elementarily embeds into one. -/
theorem exists_elementaryEmbedding_card_eq [DecidableEq Sorts]
    (M : Fam.{w'} Sorts) [L.MSStructure M] [∀ s, Nonempty (M s)]
    {t : Sorts} [Infinite (M t)]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ)
    (h2 :
      Cardinal.lift.{max u v w} (#Sorts) +
          Cardinal.lift.{w} L.card ≤
        Cardinal.lift.{max u v z} κ) :
    ∃ N : MSStructureType.{u, v, z, w} L,
      (Nonempty (N ↪ₑ[L] M) ∨ Nonempty (M ↪ₑ[L] N)) ∧
        (Cardinal.mk (Σ s, N.Carrier s)) = Cardinal.lift.{z} κ := by
  cases le_or_gt (Cardinal.lift.{max w' z} κ) (Cardinal.lift.{w} (Cardinal.mk (Σ s, M s))) with
  | inl h =>
      obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_le
        (L := L) (M := M) κ h1 h2 h
      exact ⟨N, Or.inl hN1, hN2⟩
  | inr h =>
      obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_ge
        (L := L) (M := M) (t := t) κ h2 (le_of_lt h)
      exact ⟨N, Or.inr hN1, hN2⟩

/-- A consequence of multisorted Löwenheim–Skolem: if one sort of `M` is infinite, then for any
large enough infinite `κ` there is a size-`κ` structure elementarily equivalent to `M`
(size measured by `Σ s, M s`). -/
theorem exists_elementarilyEquivalent_card_eq [DecidableEq Sorts]
    (M : Fam.{w'} Sorts) [L.MSStructure M] [∀ s, Nonempty (M s)]
    {t : Sorts} [Infinite (M t)]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ)
    (h2 :
      Cardinal.lift.{max u v w} (#Sorts) +
          Cardinal.lift.{w} L.card ≤
        Cardinal.lift.{max u v z} κ) :
    ∃ N : MSStructureType.{u, v, z, w} L,
      ((M : Fam Sorts) ≅[L] (N : Fam Sorts)) ∧
        (Cardinal.mk (Σ s, N.Carrier s)) = Cardinal.lift.{z} κ := by
  obtain ⟨N, hNdir, hNκ⟩ := exists_elementaryEmbedding_card_eq
    (L := L) (M := M) (t := t) κ h1 h2
  rcases hNdir with hNM | hMN
  · exact ⟨N, hNM.some.elementarilyEquivalent.symm, hNκ⟩
  · exact ⟨N, hMN.some.elementarilyEquivalent, hNκ⟩

end

variable {L}

namespace Theory

variable {T : L.Theory}

/-- A multisorted model-cardinality consequence of Löwenheim–Skolem:
if `T` has some model with an infinite sort, then `T` has a model of any sufficiently large
infinite cardinality (measured by `Σ s, M s`). -/
theorem exists_model_card_eq [DecidableEq Sorts]
    (h : ∃ (M : Theory.MSModelType.{u, v, z, w'} T) (t : Sorts), Infinite (((M : Fam Sorts) t)))
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ)
    (h2 :
      Cardinal.lift.{max u v w} (#Sorts) +
          Cardinal.lift.{w} L.card ≤
        Cardinal.lift.{max u v z} κ) :
    ∃ N : Theory.MSModelType.{u, v, z, w} T,
      Cardinal.mk (Σ s, N.Carrier s) = Cardinal.lift.{z} κ := by
  rcases h with ⟨M, t, _⟩
  obtain ⟨N, hN, hNκ⟩ := exists_elementarilyEquivalent_card_eq
    (L := L) (M := (M : Fam Sorts)) (t := t) κ h1 h2
  let N' : T.MSModelType := hN.toModel (T := T) (M := M)
  exact ⟨N', by simpa [N'] using hNκ⟩

end Theory

namespace Theory

variable (T : L.Theory)

/-- A theory models a bounded formula when all canonical bundled nonempty models realize it. -/
def ModelsBoundedFormula {α : Fam.{u'} Sorts} {σ : Signature Sorts} (φ : L.BoundedFormula α σ) : Prop :=
  ∀ (M : Theory.MSModelType.{u, v, z, max u u' v z} T)
    (v : α →ₛ (M : Fam Sorts)) (xs : σ.Interpret (M : Fam Sorts)),
    φ.Realize v xs

infixl:51 " ⊨ᵇ " => ModelsBoundedFormula

variable {T}
theorem models_formula_iff {α : Fam.{u'} Sorts} {φ : L.Formula α} :
    T ⊨ᵇ φ ↔
      ∀ (M : Theory.MSModelType.{u, v, z, max u u' v z} T) (v : α →ₛ (M : Fam Sorts)),
        φ.Realize v := by
  constructor
  · intro h M v
    simpa [Theory.ModelsBoundedFormula, Formula.Realize] using
      h M v (default : Signature.nil.Interpret (M : Fam Sorts))
  · intro h M v xs
    cases xs
    simpa [Theory.ModelsBoundedFormula, Formula.Realize] using h M v

theorem models_sentence_iff {φ : L.Sentence} :
    T ⊨ᵇ φ ↔ ∀ M : Theory.MSModelType.{u, v, z, max u v z} T, (M : Fam Sorts) ⊨ φ := by
  rw [models_formula_iff]
  constructor
  · intro h M
    exact h M (default : Fam.EmptyFam →ₛ (M : Fam Sorts))
  · intro h M v
    have hv : v = (default : Fam.EmptyFam →ₛ (M : Fam Sorts)) := by
      ext s x
      cases x
    subst hv
    exact h M

theorem isSatisfiable_iff_not_models_bot :
    T.IsSatisfiable ↔ ¬ T ⊨ᵇ (⊥ : L.Sentence) := by
  constructor
  · intro hcons hbot
    obtain ⟨M⟩ := hcons
    have hbotM : (M : Fam Sorts) ⊨ (⊥ : L.Sentence) := (models_sentence_iff (T := T)).1 hbot M
    simp only [Sentence.realize_bot] at hbotM
  · intro hcons
    by_contra hs
    apply hcons
    rw [models_sentence_iff]
    intro M
    exfalso
    exact hs ⟨M⟩

theorem models_sentence_of_mem {φ : L.Sentence} (h : φ ∈ T) : T ⊨ᵇ φ :=
  (models_sentence_iff (T := T)).2 fun _ => Theory.realize_sentence_of_mem (T := T) h

/-- The semantic consequence closure of a theory. -/
def closure (T : L.Theory) : L.Theory :=
  { φ | T ⊨ᵇ φ }

@[simp] theorem mem_closure_iff {φ : L.Sentence} :
    φ ∈ Theory.closure (L := L) T ↔ T ⊨ᵇ φ := by
  rfl

theorem subset_closure : T ⊆ Theory.closure (L := L) T := by
  intro φ hφ
  exact Theory.models_sentence_of_mem (T := T) hφ

@[simp] theorem top_mem_closure :
    (⊤ : L.Sentence) ∈ Theory.closure (L := L) T := by
  rw [Theory.mem_closure_iff, Theory.models_sentence_iff]
  intro M
  simp [Sentence.realize_top]

theorem bot_mem_closure_iff_not_isSatisfiable :
    (⊥ : L.Sentence) ∈ Theory.closure (L := L) T ↔ ¬ T.IsSatisfiable := by
  rw [Theory.mem_closure_iff]
  constructor
  · intro hbot hs
    exact ((Theory.isSatisfiable_iff_not_models_bot (T := T)).1 hs) hbot
  · intro hbot
    by_contra hnot
    exact hbot ((Theory.isSatisfiable_iff_not_models_bot (T := T)).2 hnot)

theorem closure_inf_mem {φ ψ : L.Sentence}
    (hφ : φ ∈ Theory.closure (L := L) T)
    (hψ : ψ ∈ Theory.closure (L := L) T) :
    (φ ⊓ ψ) ∈ Theory.closure (L := L) T := by
  rw [Theory.mem_closure_iff] at hφ hψ ⊢
  rw [Theory.models_sentence_iff] at hφ hψ ⊢
  intro M
  simpa [Sentence.realize_inf] using And.intro (hφ M) (hψ M)

@[simp] theorem closure_inf_mem_iff {φ ψ : L.Sentence} :
    (φ ⊓ ψ) ∈ Theory.closure (L := L) T ↔
      φ ∈ Theory.closure (L := L) T ∧ ψ ∈ Theory.closure (L := L) T := by
  constructor
  · intro h
    rw [Theory.mem_closure_iff] at h
    rw [Theory.mem_closure_iff, Theory.mem_closure_iff]
    rw [Theory.models_sentence_iff] at h ⊢
    constructor
    · intro M
      have hMInf : (M : Fam Sorts) ⊨ (φ ⊓ ψ) := h M
      have hM : ((M : Fam Sorts) ⊨ φ) ∧ ((M : Fam Sorts) ⊨ ψ) := by
        simpa [Sentence.realize_inf] using hMInf
      exact hM.1
    · intro M v xs
      have hMInf : (M : Fam Sorts) ⊨ (φ ⊓ ψ) := h M
      have hM : ((M : Fam Sorts) ⊨ φ) ∧ ((M : Fam Sorts) ⊨ ψ) := by
        simpa [Sentence.realize_inf] using hMInf
      simp only [(Unique.default_eq v).symm, (Unique.default_eq xs).symm, PUnit.default_eq_unit]
      simp only [Sentence.Realize, Formula.Realize, PUnit.default_eq_unit] at hM
      exact hM.2
  · rintro ⟨hφ, hψ⟩
    exact Theory.closure_inf_mem (L := L) (T := T) hφ hψ

theorem closure_sup_mem_of_left {φ ψ : L.Sentence}
    (hφ : φ ∈ Theory.closure (L := L) T) :
    (φ ⊔ ψ) ∈ Theory.closure (L := L) T := by
  rw [Theory.mem_closure_iff] at hφ ⊢
  rw [Theory.models_sentence_iff] at hφ ⊢
  intro M
  simpa [Sentence.realize_sup] using Or.inl (hφ M)

theorem closure_sup_mem_of_right {φ ψ : L.Sentence}
    (hψ : ψ ∈ Theory.closure (L := L) T) :
    (φ ⊔ ψ) ∈ Theory.closure (L := L) T := by
  rw [Theory.mem_closure_iff] at hψ ⊢
  rw [Theory.models_sentence_iff] at hψ ⊢
  intro M
  simpa [Sentence.realize_sup] using Or.inr (hψ M)

theorem closure_sup_mem {φ ψ : L.Sentence}
    (hφ : φ ∈ Theory.closure (L := L) T)
    (_hψ : ψ ∈ Theory.closure (L := L) T) :
    (φ ⊔ ψ) ∈ Theory.closure (L := L) T :=
  Theory.closure_sup_mem_of_left (L := L) (T := T) (ψ := ψ) hφ

theorem closure_sup_mem_of_or {φ ψ : L.Sentence}
    (h : φ ∈ Theory.closure (L := L) T ∨ ψ ∈ Theory.closure (L := L) T) :
    (φ ⊔ ψ) ∈ Theory.closure (L := L) T := by
  rcases h with hφ | hψ
  · exact Theory.closure_sup_mem_of_left (L := L) (T := T) (ψ := ψ) hφ
  · exact Theory.closure_sup_mem_of_right (L := L) (T := T) (φ := φ) hψ

/-- Entailing a sentence implication is equivalent to saying every model of `T`
turns a realization of the antecedent into a realization of the consequent. -/
theorem models_sentence_imp_iff {φ ψ : L.Sentence} :
    T ⊨ᵇ (φ ⟹ ψ) ↔
      ∀ M : Theory.MSModelType.{u, v, z, max u v z} T,
        ((M : Fam Sorts) ⊨ φ → (M : Fam Sorts) ⊨ ψ) := by
  rw [models_sentence_iff]
  constructor
  · intro h M
    exact (Sentence.realize_imp (M := (M : Fam Sorts)) (φ := φ) (ψ := ψ)).1 (h M)
  · intro h M
    exact (Sentence.realize_imp (M := (M : Fam Sorts)) (φ := φ) (ψ := ψ)).2 (h M)

/-- A semantically entailed implication gives implication between semantic entailments. -/
theorem models_sentence_imp {φ ψ : L.Sentence} :
    T ⊨ᵇ (φ ⟹ ψ) → (T ⊨ᵇ φ → T ⊨ᵇ ψ) := by
  intro himp hφ
  rw [models_sentence_iff] at himp hφ ⊢
  intro M
  exact ((Sentence.realize_imp (M := (M : Fam Sorts)) (φ := φ) (ψ := ψ)).1 (himp M)) (hφ M)

theorem closure_mp {φ ψ : L.Sentence}
    (hφ : φ ∈ Theory.closure (L := L) T)
    (himp : (φ ⟹ ψ) ∈ Theory.closure (L := L) T) :
    ψ ∈ Theory.closure (L := L) T := by
  rw [Theory.mem_closure_iff] at hφ himp ⊢
  exact Theory.models_sentence_imp (T := T) himp hφ

/-- Left projection of conjunction, as semantic entailment modulo `T`. -/
theorem models_sentence_inf_le_left {φ ψ : L.Sentence} :
    T ⊨ᵇ ((φ ⊓ ψ) ⟹ φ) := by
  rw [models_sentence_iff]
  intro M
  rw [Sentence.realize_imp, Sentence.realize_inf]
  exact fun h => h.1

/-- Right projection of conjunction, as semantic entailment modulo `T`. -/
theorem models_sentence_inf_le_right {φ ψ : L.Sentence} :
    T ⊨ᵇ ((φ ⊓ ψ) ⟹ ψ) := by
  rw [models_sentence_iff]
  intro M
  rw [Sentence.realize_imp, Sentence.realize_inf]
  exact fun h => h.2

/-- Conjunction introduction, as semantic entailment modulo `T`. -/
theorem models_sentence_le_inf {φ ψ χ : L.Sentence}
    (hφ : T ⊨ᵇ (χ ⟹ φ)) (hψ : T ⊨ᵇ (χ ⟹ ψ)) :
    T ⊨ᵇ (χ ⟹ (φ ⊓ ψ)) := by
  rw [models_sentence_iff] at hφ hψ ⊢
  intro M
  rw [Sentence.realize_imp, Sentence.realize_inf]
  intro hχ
  exact
    ⟨((Sentence.realize_imp (M := (M : Fam Sorts)) (φ := χ) (ψ := φ)).1 (hφ M)) hχ,
      ((Sentence.realize_imp (M := (M : Fam Sorts)) (φ := χ) (ψ := ψ)).1 (hψ M)) hχ⟩

/-- Every sentence semantically entails `⊤` modulo `T`. -/
theorem models_sentence_le_top {φ : L.Sentence} :
    T ⊨ᵇ (φ ⟹ (⊤ : L.Sentence)) := by
  rw [models_sentence_iff]
  intro M
  rw [Sentence.realize_imp, Sentence.realize_top]
  intro _hφ
  trivial

/-- `⊥` semantically entails every sentence modulo `T`. -/
theorem models_sentence_bot_le {φ : L.Sentence} :
    T ⊨ᵇ ((⊥ : L.Sentence) ⟹ φ) := by
  rw [models_sentence_iff]
  intro M
  rw [Sentence.realize_imp, Sentence.realize_bot]
  intro hFalse
  exact False.elim hFalse

/-- Semantic modus ponens packaged as an entailed implication. -/
theorem models_sentence_mp_entails {φ ψ : L.Sentence} :
    T ⊨ᵇ (((φ ⊓ (φ ⟹ ψ)) : L.Sentence) ⟹ ψ) := by
  rw [models_sentence_iff]
  intro M
  rw [Sentence.realize_imp, Sentence.realize_inf, Sentence.realize_imp]
  intro h
  exact h.2 h.1

/-- A sentence conjoined with its negation semantically entails `⊥` modulo `T`. -/
theorem models_sentence_inf_compl_le_bot {φ : L.Sentence} :
    T ⊨ᵇ ((φ ⊓ φ.not) ⟹ (⊥ : L.Sentence)) := by
  rw [models_sentence_iff]
  intro M
  rw [Sentence.realize_imp, Sentence.realize_inf, Sentence.realize_not, Sentence.realize_bot]
  intro h
  exact h.2 h.1

/-- `⊤` semantically entails excluded middle modulo `T`. -/
theorem models_sentence_top_le_sup_compl {φ : L.Sentence} :
    T ⊨ᵇ ((⊤ : L.Sentence) ⟹ (φ ⊔ φ.not)) := by
  rw [models_sentence_iff]
  intro M
  rw [Sentence.realize_imp, Sentence.realize_top, Sentence.realize_sup, Sentence.realize_not]
  intro _
  by_cases hφ : (M : Fam Sorts) ⊨ φ
  · exact Or.inl hφ
  · exact Or.inr hφ

theorem models_iff_not_satisfiable (φ : L.Sentence) :
    T ⊨ᵇ φ ↔ ¬Theory.IsSatisfiable (T ∪ {φ.not}) := by
  rw [models_sentence_iff, Theory.IsSatisfiable]
  refine
    ⟨fun h1 h2 =>
      (Sentence.realize_not _).1
        (Theory.realize_sentence_of_mem (T := T ∪ {Formula.not φ})
          (Set.subset_union_right (Set.mem_singleton _)))
        (by
          have hsub : (h2.some : Fam Sorts) ⊨ T := (h2.some.is_model).mono Set.subset_union_left
          let Msub : Theory.MSModelType.{u, v, z, max u v z} T := Theory.Model.bundled (T := T) hsub
          exact h1 Msub),
      fun h M => ?_⟩
  contrapose! h
  rw [← Sentence.realize_not] at h
  letI : ∀ s, Nonempty (((M : Theory.MSModelType.{u, v, z, max u v z} T) : Fam Sorts) s) :=
    fun s => M.nonempty' (s := s)
  refine ⟨Theory.Model.bundled (T := T ∪ {φ.not}) (M := (M : Fam Sorts)) ?_⟩
  exact (M.is_model).union (by simpa using h)


theorem ModelsBoundedFormula.realize_sentence {φ : L.Sentence} (h : T ⊨ᵇ φ)
    (M : Fam.{w'} Sorts)
    [L.MSStructure M] [M ⊨ T] [∀ s, Nonempty (M s)] : M ⊨ φ := by
  rw [models_iff_not_satisfiable] at h
  contrapose! h
  have : M ⊨ T ∪ {Formula.not φ} := by
    refine (inferInstance : M ⊨ T).union ?_
    simpa [Sentence.realize_not] using h
  exact Theory.Model.isSatisfiable (T := T ∪ {Formula.not φ}) (M := M)

theorem models_of_models_theory {T' : L.Theory}
    (h : ∀ ψ : L.Sentence, ψ ∈ T' → T ⊨ᵇ ψ)
    {α : Fam.{u'} Sorts} {σ : Signature Sorts} {φ : L.BoundedFormula α σ} (hφ : T' ⊨ᵇ φ) :
    T ⊨ᵇ φ := by
  intro M v xs
  have hM : M ⊨ T' := T'.model_iff.2 (fun ψ hψ => (h ψ hψ).realize_sentence M)
  let M' : Theory.MSModelType.{u, v, z, max u u' v z} T' := Theory.Model.bundled (T := T') hM
  exact hφ M' v xs

theorem closure_mono {T' : L.Theory} (hTT' : T ⊆ T') :
    Theory.closure (L := L) T ⊆ Theory.closure (L := L) T' := by
  intro φ hφ
  rw [Theory.mem_closure_iff] at hφ ⊢
  exact Theory.models_of_models_theory (T := T') (T' := T)
    (fun ψ hψ => Theory.models_sentence_of_mem (T := T') (hTT' hψ)) hφ

theorem closure_idem :
    Theory.closure (L := L) (Theory.closure (L := L) T) = Theory.closure (L := L) T := by
  ext φ
  constructor
  · intro hφ
    rw [Theory.mem_closure_iff] at hφ ⊢
    exact Theory.models_of_models_theory (T := T) (T' := Theory.closure (L := L) T)
      (fun ψ hψ => (Theory.mem_closure_iff (L := L) (T := T) (φ := ψ)).1 hψ) hφ
  · intro hφ
    exact (Theory.subset_closure (L := L) (T := Theory.closure (L := L) T)) hφ

/-- A multisorted compactness-style consequence:
a sentence is modeled by `T` iff some finite subtheory already models it. -/
theorem models_iff_finset_models {φ : L.Sentence} :
    T ⊨ᵇ φ ↔ ∃ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T ∧ (T0 : L.Theory) ⊨ᵇ φ := by
  simp only [models_iff_not_satisfiable]
  rw [isSatisfiable_iff_isFinitelySatisfiable, Theory.IsFinitelySatisfiable]
  contrapose!
  letI := Classical.decEq (Sentence L)
  constructor
  · intro h T0 hT0
    simpa using h (T0 ∪ {Formula.not φ})
      (by
        simp only [Finset.coe_union, Finset.coe_singleton]
        exact Set.union_subset_union hT0 (Set.Subset.refl _))
  · intro h T0 hT0
    exact Theory.IsSatisfiable.mono (h (T0.erase (Formula.not φ)) (by simpa using hT0))
      (by simp)

/-- A theory is complete when it is satisfiable and models each sentence or its negation. -/
def IsComplete (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, T ⊨ᵇ φ ∨ T ⊨ᵇ φ.not

namespace IsComplete

theorem models_not_iff (h : T.IsComplete) (φ : L.Sentence) : T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ := by
  rcases h.2 φ with hφ | hφn
  · simp only [hφ, not_true, iff_false]
    rw [models_sentence_iff, not_forall]
    refine ⟨h.1.some, ?_⟩
    simp only [Sentence.realize_not, Classical.not_not]
    exact (models_sentence_iff (T := T)).1 hφ _
  · simp only [hφn, true_iff]
    intro hφ
    rw [models_sentence_iff] at *
    exact hφn h.1.some (hφ _)

theorem realize_sentence_iff [DecidableEq Sorts] (h : T.IsComplete) (φ : L.Sentence)
    (M : Fam.{w'} Sorts) [L.MSStructure M] [M ⊨ T] [∀ s, Nonempty (M s)] :
    M ⊨ φ ↔ T ⊨ᵇ φ := by
  rcases h.2 φ with hφ | hφn
  · exact iff_of_true (hφ.realize_sentence M) hφ
  · exact
      iff_of_false ((Sentence.realize_not M).1 (hφn.realize_sentence M))
        ((h.models_not_iff φ).1 hφn)

/-- A complete theory is the `completeTheory` of one of its models. -/
theorem eq_complete_theory [DecidableEq Sorts] (h : T.IsComplete)
    (M : Fam.{w'} Sorts) [L.MSStructure M] [M ⊨ T] [∀ s, Nonempty (M s)] :
    {φ | T ⊨ᵇ φ} = L.completeTheory M := by
  ext φ
  simp only [Set.mem_setOf_eq, L.mem_completeTheory]
  refine ⟨fun h_models => h_models.realize_sentence M, fun h_realize => ?_⟩
  cases h.2 φ with
  | inl hT => exact hT
  | inr hT =>
      have : M ⊨ φ.not := hT.realize_sentence M
      rw [Sentence.realize_not] at this
      contradiction

/-- A theory is complete iff it is satisfiable and all canonical bundled models are elementarily
equivalent. -/
theorem isComplete_iff_models_elementarily_equivalent [DecidableEq Sorts] :
    T.IsComplete ↔ T.IsSatisfiable ∧
      ∀ (M N : Theory.MSModelType.{u, v, z, max u v z} T),
        ((M : Fam Sorts) ≅[L] (N : Fam Sorts)) := by
  constructor
  · intro hcomp
    refine ⟨hcomp.1, ?_⟩
    intro M N
    rw [ElementarilyEquivalent, ← hcomp.eq_complete_theory (M := (M : Fam Sorts)),
      ← hcomp.eq_complete_theory (M := (N : Fam Sorts))]
  · rintro ⟨hsat, h⟩
    refine ⟨hsat, ?_⟩
    intro φ
    obtain ⟨M⟩ := hsat
    by_cases hφ : (M : Fam Sorts) ⊨ φ
    · left
      exact (models_sentence_iff (T := T)).2 fun N => (elementarilyEquivalent_iff.1 (h M N) φ).1 hφ
    · right
      exact (models_sentence_iff (T := T)).2 fun N => (Sentence.realize_not _).2
        (mt (elementarilyEquivalent_iff.1 (h M N) φ).2 hφ)

/-- If a theory is complete, all of its (nonempty) models are elementarily equivalent. -/
theorem models_elementarily_equivalent [DecidableEq Sorts]
    (h : T.IsComplete)
    (M : Fam.{w'} Sorts) (N: Fam.{w''} Sorts) [L.MSStructure M] [L.MSStructure N]
    [M ⊨ T] [N ⊨ T] [∀ s, Nonempty (M s)] [∀ s, Nonempty (N s)] :
    (M ≅[L] N) := by
  rw [ElementarilyEquivalent, ← h.eq_complete_theory (M := M), ← h.eq_complete_theory (M := N)]

end IsComplete

/-- A theory is maximal when it is satisfiable and contains each sentence or its negation.
Maximal theories are complete. -/
def IsMaximal (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, φ ∈ T ∨ φ.not ∈ T

theorem IsMaximal.isComplete (h : T.IsMaximal) : T.IsComplete :=
  h.imp_right (forall_imp fun _ => Or.imp models_sentence_of_mem models_sentence_of_mem)

theorem IsMaximal.mem_or_not_mem (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ∨ φ.not ∈ T :=
  h.2 φ

theorem IsMaximal.mem_of_models (h : T.IsMaximal) {φ : L.Sentence} (hφ : T ⊨ᵇ φ) : φ ∈ T := by
  refine (h.mem_or_not_mem φ).resolve_right fun con => ?_
  rw [models_iff_not_satisfiable, Set.union_singleton, Set.insert_eq_of_mem con] at hφ
  exact hφ h.1

theorem IsMaximal.mem_iff_models (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ↔ T ⊨ᵇ φ :=
  ⟨models_sentence_of_mem, h.mem_of_models⟩

end Theory

namespace completeTheory

variable (L) (M : Fam.{w'} Sorts)
variable [L.MSStructure M]

theorem isSatisfiable [DecidableEq Sorts] [∀ s, Nonempty (M s)] : (L.completeTheory M).IsSatisfiable :=
  Theory.Model.isSatisfiable (T := L.completeTheory M) (M := M)

theorem mem_or_not_mem (φ : L.Sentence) :
    φ ∈ L.completeTheory M ∨ φ.not ∈ L.completeTheory M := by
  simp_rw [completeTheory, Set.mem_setOf_eq, Sentence.Realize, Formula.realize_not, or_not]

theorem isMaximal [DecidableEq Sorts] [∀ s, Nonempty (M s)] : (L.completeTheory M).IsMaximal :=
  ⟨isSatisfiable L M, mem_or_not_mem L M⟩

theorem isComplete [DecidableEq Sorts] [∀ s, Nonempty (M s)] : (L.completeTheory M).IsComplete :=
  (completeTheory.isMaximal L M).isComplete

end completeTheory

namespace Cardinal

variable (κ : Cardinal.{w}) (T : L.Theory)

/-- A theory is `κ`-categorical (multisorted version) if any two canonical bundled models of total
size `κ` (measured by `Σ s, M s`) are isomorphic. -/
def Categorical : Prop :=
  ∀ M N : Theory.MSModelType.{u, v, z, w} T,
    Cardinal.mk (Σ s, M.Carrier s) = Cardinal.lift.{z} κ →
      Cardinal.mk (Σ s, N.Carrier s) = Cardinal.lift.{z} κ →
        Nonempty ((M : Fam Sorts) ≃[L] (N : Fam Sorts))

/-- A multisorted Łoś–Vaught test: categoricity in an infinite cardinal implies completeness, under
the assumption that every model has some infinite sort. -/
theorem Categorical.isComplete [DecidableEq Sorts]
    (h : Categorical (κ := κ) (T := T)) (h1 : ℵ₀ ≤ κ)
    (h2 :
      Cardinal.lift.{max u v w} (#Sorts) + Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v z} κ)
    (hS : T.IsSatisfiable)
    (hT : ∀ M : Theory.MSModelType.{u, v, z, max u v z} T, ∃ t : Sorts, Infinite (((M : Fam Sorts) t))) :
    T.IsComplete := by
  refine ⟨hS, fun φ => by
    obtain ⟨M0⟩ := hS
    obtain ⟨t0, hInf0⟩ := hT M0
    obtain ⟨_, hκ⟩ := Theory.exists_model_card_eq (L := L) (T := T) ⟨M0, t0, hInf0⟩ κ h1 h2
    rw [Theory.models_sentence_iff, Theory.models_sentence_iff]
    by_contra! hcontra
    rcases hcontra with ⟨⟨MF, hMF⟩, MT, hMT⟩
    rw [Sentence.realize_not, Classical.not_not] at hMT
    refine hMF ?_
    obtain ⟨tT, hInfT⟩ := hT MT
    obtain ⟨tF, hInfF⟩ := hT MF
    obtain ⟨NT, MNT, hNT⟩ := exists_elementarilyEquivalent_card_eq (L := L) (M := (MT : Fam Sorts))
      (t := tT) κ h1 h2
    obtain ⟨NF, MNF, hNF⟩ := exists_elementarilyEquivalent_card_eq (L := L) (M := (MF : Fam Sorts))
      (t := tF) κ h1 h2
    have hNT' : Cardinal.mk (Σ s, NT.Carrier s) = Cardinal.lift.{z} κ := by simpa using hNT
    have hNF' : Cardinal.mk (Σ s, NF.Carrier s) = Cardinal.lift.{z} κ := by simpa using hNF
    obtain ⟨TF⟩ := h (MNT.toModel (T := T)) (MNF.toModel (T := T)) hNT' hNF'
    exact
      ((MNT.realize_sentence φ).trans
        ((StrongHomClass.realize_sentence TF φ).trans (MNF.realize_sentence φ).symm)).1 hMT⟩

/-- In the empty multisorted language, categoricity by total size `#(Σ s, M s)` is valid in the
one-sort case (expressed as `[Unique Sorts]`). Without this hypothesis it is false in general:
total size does not determine the per-sort cardinal profile. -/
theorem empty_theory_categorical_of_unique [Unique Sorts]
    (T : ((MSLanguage.empty : MSLanguage Sorts).Theory)) :
    Categorical (κ := κ) (T := T) := by
  intro M N hM hN
  rw [MSLanguage.empty.nonempty_equiv_iff]
  intro s
  have hs : s = default := Subsingleton.elim _ _
  subst hs
  simp only [Cardinal.lift_id]
  have hM0 : Cardinal.lift.{max w z} (Cardinal.mk (M.Carrier default)) = Cardinal.lift.{z} κ := by
    have hSigma : Cardinal.lift.{max w z} (Cardinal.mk (M.Carrier default)) =
        Cardinal.mk (Σ t : Sorts, M.Carrier t) := by
      simpa using Cardinal.mk_congr_lift ((Equiv.uniqueSigma (fun t => M.Carrier t)).symm)
    calc
      Cardinal.lift.{max w z} (Cardinal.mk (M.Carrier default)) = Cardinal.mk (Σ t : Sorts, M.Carrier t) := hSigma
      _ = Cardinal.lift.{z} κ := hM
  have hN0 : Cardinal.lift.{max w z} (Cardinal.mk (N.Carrier default)) = Cardinal.lift.{z} κ := by
    have hSigma : Cardinal.lift.{max w z} (Cardinal.mk (N.Carrier default)) =
        Cardinal.mk (Σ t : Sorts, N.Carrier t) := by
      simpa using Cardinal.mk_congr_lift ((Equiv.uniqueSigma (fun t => N.Carrier t)).symm)
    calc
      Cardinal.lift.{max w z} (Cardinal.mk (N.Carrier default)) = Cardinal.mk (Σ t : Sorts, N.Carrier t) := hSigma
      _ = Cardinal.lift.{z} κ := hN
  exact Cardinal.lift_inj.mp (hM0.trans hN0.symm)

/-- A one-sort (via `[Unique Sorts]`) empty-language instance of the multisorted Łoś–Vaught test. -/
theorem empty_infiniteTheory_isComplete_of_unique [DecidableEq Sorts] [Unique Sorts] :
    (((MSLanguage.empty : MSLanguage Sorts).infiniteTheory (default : Sorts))).IsComplete := by
  let L0 : MSLanguage Sorts := MSLanguage.empty
  let T0 : L0.Theory := L0.infiniteTheory (default : Sorts)
  have hcat : Categorical (κ := (Cardinal.aleph0 : Cardinal.{0})) (T := T0) :=
    empty_theory_categorical_of_unique (κ := (Cardinal.aleph0 : Cardinal.{0})) T0
  have h2 :
      Cardinal.lift.{0} (#Sorts) + Cardinal.lift.{0} L0.card ≤ Cardinal.lift.{z} (Cardinal.aleph0 : Cardinal.{0}) := by
    have hSorts : Cardinal.lift.{0} (Cardinal.mk Sorts) = 1 := by
      simp only [mk_fintype, Fintype.card_unique, Nat.cast_one, lift_uzero]
    rw [show (#Sorts) = Cardinal.mk Sorts by rfl, MSLanguage.card_empty, Cardinal.lift_zero, hSorts]
    simp only [add_zero, lift_aleph0, one_le_aleph0]
  have hS : T0.IsSatisfiable := by
    let M : Fam Sorts := ⟨fun _ => ℕ⟩
    letI : L0.MSStructure M := MSLanguage.emptyStructure
    letI : ∀ s, Nonempty (M s) := fun s => by
      change Nonempty ℕ
      exact ⟨0⟩
    letI : Infinite (M default) := by
      change Infinite ℕ
      infer_instance
    letI : M ⊨ T0 := MSLanguage.model_infiniteTheory L0 (s := default)
    exact Theory.Model.isSatisfiable (T := T0) (M := M)
  have hT : ∀ M : Theory.MSModelType.{0, 0, z, max 0 0 z} T0,
      ∃ t : Sorts, Infinite (((M : Fam Sorts) t)) := by
    intro M
    refine ⟨default, ?_⟩
    exact (MSLanguage.model_infiniteTheory_iff (L := L0) (M := (M : Fam Sorts)) (s := default)).1 M.is_model
  simpa [L0, T0] using
    (Categorical.isComplete (κ := (Cardinal.aleph0 : Cardinal.{0})) (T := T0) hcat
      (show (Cardinal.aleph0 : Cardinal.{0}) ≤ Cardinal.aleph0 by rfl) h2 hS hT)

end Cardinal

namespace Theory

variable {T : L.Theory}

theorem models_formula_iff_onTheory_models_equivSentence {φ : L.Formula α} :
    T ⊨ᵇ φ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ Formula.equivSentence φ := by
  refine ⟨fun h => models_sentence_iff.2 (fun M => ?_),
    fun h => models_formula_iff.2 (fun M v => ?_)⟩
  · letI := (L.lhomWithConstants α).reduct M
    have : (L.lhomWithConstants α).IsExpansionOn M := LHom.isExpansionOn_reduct _ _
      -- why doesn't that instance just work?
    rw [Formula.realize_equivSentence]
    have : M ⊨ T := (LHom.onTheory_model _ _).1 M.is_model -- why isn't M.is_model inferInstance?
    let M' := Theory.MSModelType.of T M
    exact h M' ⟨fun s a => (L.con s a : M.Carrier s)⟩  _
  · letI : (constantsOn α).MSStructure M := constantsOn.structure v
    have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
    exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)

theorem ModelsBoundedFormula.realize_formula {φ : L.Formula α} (h : T ⊨ᵇ φ) (M : Fam Sorts)
    [L.MSStructure M] [M ⊨ T] [∀ s, Nonempty (M s)] {v : α →ₛ M} : φ.Realize v := by
  rw [models_formula_iff_onTheory_models_equivSentence] at h
  letI : (constantsOn α).MSStructure M := constantsOn.structure v
  have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
  exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)
/-
theorem models_toFormula_iff [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ} {φ : L.BoundedFormula α σ} :
    T ⊨ᵇ φ.localize.toFormula ↔ T ⊨ᵇ φ := by
  refine ⟨fun h M v xs => ?_, ?_⟩
  · have h' : φ.localize.toFormula.Realize _ _ := h.realize_formula M
    simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
    exact h'
  · simp only [models_formula_iff, BoundedFormula.realize_toFormula]
    exact fun h M v => h M _ _

theorem ModelsBoundedFormula.realize_boundedFormula
    {φ : L.BoundedFormula α n} (h : T ⊨ᵇ φ) (M : Type*)
    [L.MSStructure M] [M ⊨ T] [Nonempty M] {v : α → M} {xs : Fin n → M} : φ.Realize v xs := by
  have h' : φ.toFormula.Realize (Sum.elim v xs) := (models_toFormula_iff.2 h).realize_formula M
  simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
  exact h'


 -/
end Theory
