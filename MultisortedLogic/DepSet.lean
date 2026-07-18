import MultisortedLogic.Fam
universe u v w z u' v' w'

namespace MSFirstOrder

open Fam

variable {base : Type u} {α : Fam.{v} base}

/-- A dependent family of sets over a fixed base. -/
structure DepSet (α : Fam.{v} base) where
  carrier : ∀ s, Set (α s)

instance : CoeFun (DepSet α) (fun _ => ∀ s, Set (α s)) :=
  ⟨DepSet.carrier⟩

namespace DepSet

/-- View a dependent set as a set on `Sigma α`. -/
def sigma (S : DepSet α) : Set (Sigma α) :=
  Sigma.uncurry S

lemma sigma_uncurry (S : DepSet α) : S.sigma = (Set.univ).sigma (S.carrier) := by
  rw [sigma]
  ext x : 1
  simp_all only [Set.mem_sigma_iff, Set.mem_univ, true_and]
  obtain ⟨fst, snd⟩ := x
  simp_all only
  rfl

/-- View a set on `Sigma α` as a dependent set. -/
def ofSigma (S : Set (Sigma α)) : DepSet α :=
   ⟨Sigma.curry S⟩

lemma sigma_ofSigma (S : Set (Sigma α)) : (ofSigma S).sigma = S := by
  rfl

lemma ofSigma_sigma (S : DepSet α) : ofSigma (S.sigma) = S := by
  rfl

/-- Coerce a `DepSet` to a set on `Sigma α` via `sigma`. -/
instance : SetLike (DepSet α) (Sigma α) where
  coe := DepSet.sigma
  coe_injective := by
    intro S T h
    rcases S with ⟨X⟩
    rcases T with ⟨Y⟩
    rw[mk.injEq]
    ext s x
    have hx : ((⟨s, x⟩ : Sigma α) ∈ ((⟨X⟩ : DepSet α ).sigma : Set (Sigma α))) ↔
              ((⟨s, x⟩ : Sigma α) ∈ ((⟨Y⟩ : DepSet α ).sigma : Set (Sigma α))) := by
      simp_all only
    repeat' rw [DepSet.sigma] at hx
    simp_all only
    exact hx

@[simp]
theorem mem_sigma {S : DepSet α} {s : base} {x : α s} :
    (⟨s, x⟩ : Sigma α) ∈ S ↔ x ∈ S s :=
  Iff.rfl


/-- LE instance is inherited from the SetLike instance. -/
instance : PartialOrder (DepSet α) := .ofSetLike (DepSet α) (Sigma α)

instance : HasSubset (DepSet α) := ⟨(· ≤ ·)⟩

theorem le_def {S T : DepSet α} : S ≤ T ↔ ∀ s, S s ⊆ T s := by
  constructor
  · intro h s x hx
    have : (⟨s, x⟩ : Sigma α) ∈ (T : DepSet α) := h (by simpa using hx)
    simpa using this
  · intro h x hx
    rcases x with ⟨s, x⟩
    have : x ∈ T s := h s (by simpa using hx)
    simpa using this

lemma subset_intro_mem_eq {S T : DepSet α} : S ⊆ T ↔ ∀ s, S s ⊆ T s := by
  change   S ≤ T ↔ ∀ s, S s ⊆ T s
  exact le_def

instance emptyInst : EmptyCollection (DepSet α) :=
  ⟨⟨fun s ↦ (∅ : Set (α s))⟩⟩

@[simp]
lemma empty_eq_empty_set : (∅ : DepSet α) = (∅ : Set (Sigma α)) := by
  rfl

@[simp]
lemma empty_at_sort (s : base) : (∅ : DepSet α) s = ∅ := by
  rfl

protected def insert (x : Sigma α) (S : DepSet α) : DepSet α :=
  ofSigma (Set.insert x (S : Set (Sigma α)))

instance insertInst : Insert (Sigma α) (DepSet α) := ⟨DepSet.insert⟩

@[simp] lemma mem_insert {x y : Sigma α} {S : DepSet α} :
    y ∈ (insert x S : DepSet α) ↔ y = x ∨ y ∈ S := by
  change y ∈ insert x S.sigma ↔ y = x ∨ y ∈ S.sigma
  simp only [Set.mem_insert_iff]

@[simp] lemma mem_insert_fiber {s : base} {a : α s} {x : Sigma α} {S : DepSet α} :
    a ∈ (insert x S) s ↔ (⟨s,a⟩ : Sigma α) = x ∨ a ∈ S s := by
  simpa [mem_sigma] using (mem_insert (x := x) (y := (⟨s,a⟩ : Sigma α)) (S := S))

protected def singleton (x : Sigma α) : DepSet α :=
  ofSigma (Set.singleton x)

instance instSingleton : Singleton (Sigma α) (DepSet α) := ⟨DepSet.singleton⟩

@[simp] lemma mem_singleton {x y : Sigma α} :
  y ∈ (DepSet.singleton (α := α) x) ↔ y = x := Eq.to_iff rfl

@[simp] lemma mem_singleton' {x y : Sigma α} :
  y ∈ ({x} : DepSet α) ↔ y = x := by
  simp only [singleton, mem_singleton]

protected def union (S₁ S₂ : DepSet α) : DepSet α := ofSigma (S₁ ∪ S₂)

instance : Union (DepSet α) := ⟨DepSet.union⟩

protected def inter (S₁ S₂ : DepSet α) : DepSet α := ofSigma (S₁ ∩ S₂)

instance : Inter (DepSet α) := ⟨DepSet.inter⟩

protected def compl (S : DepSet α) : DepSet α := ofSigma Sᶜ

instance : Compl (DepSet α) := ⟨DepSet.compl⟩

protected def diff (S T : DepSet α) : DepSet α := ofSigma (S \ T)

instance : SDiff (DepSet α) := ⟨DepSet.diff⟩

/-- Two dependent sets are equal if they agree on every sort. -/
@[ext]
theorem ext {S T : DepSet α} (h : ∀ s x, x ∈ S s ↔ x ∈ T s) : S = T := by
  cases S with
  | mk Scarrier =>
    cases T with
    | mk Tcarrier =>
      have hcarrier : Scarrier = Tcarrier := by
        funext s
        apply Set.ext
        intro x
        exact h s x
      cases hcarrier
      rfl

/-- Order Isomorphism from DepSet α to Set (Sigma α), which can be used to cleanly transport
  class instances such as DistribLattice. -/
def sigmaOrderIso : DepSet α ≃o Set (Sigma α) where
  toEquiv :=
  { toFun := fun S => (S : Set (Sigma α))
    invFun := DepSet.ofSigma
    left_inv := by intro S; simp_all only; rfl
    right_inv := by intro S; simp_all only; rfl}
  map_rel_iff' := by
    intro A B
    rfl

instance instDistribLattice : DistribLattice (DepSet α) where
  sup := (· ∪ ·)
  inf := (· ∩ ·)
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := fun _ => le_rfl
  le_trans := fun A B C hAB hBC => Set.Subset.trans hAB hBC
  le_antisymm := fun A B hAB hBA => SetLike.ext' (Set.Subset.antisymm hAB hBA)
  le_sup_left := fun A B => Set.subset_union_left
  le_sup_right := fun A B => Set.subset_union_right
  sup_le := fun A B C hAC hBC => Set.union_subset hAC hBC
  inf_le_left := fun A B => Set.inter_subset_left
  inf_le_right := fun A B => Set.inter_subset_right
  le_inf := fun A B C hAB hAC => Set.subset_inter hAB hAC
  le_sup_inf := by
    intro A B C x hx
    rcases hx with ⟨hxA_or_B, hxA_or_C⟩
    cases hxA_or_B with
    | inl hxA => exact Or.inl hxA
    | inr hxB =>
      cases hxA_or_C with
      | inl hxA => exact Or.inl hxA
      | inr hxC => exact Or.inr ⟨hxB, hxC⟩

/-- Set-theoretic supremum of dependent sets, pointwise by existential membership. -/
instance instSupSet : SupSet (DepSet α) where
  sSup S := ⟨fun s => {x | ∃ T ∈ S, x ∈ T s}⟩

/-- Set-theoretic infimum of dependent sets, pointwise by universal membership. -/
instance instInfSet : InfSet (DepSet α) where
  sInf S := ⟨fun s => {x | ∀ T ∈ S, x ∈ T s}⟩

instance : UsesSetNotationForOrder (DepSet α) :=
  by exact { }

@[simp]
theorem mem_sSup {S : Set (DepSet α)} {s : base} {x : α s} :
    x ∈ (sSup S : DepSet α) s ↔ ∃ T ∈ S, x ∈ T s :=
  Iff.rfl

@[simp]
theorem mem_sInf {S : Set (DepSet α)} {s : base} {x : α s} :
    x ∈ (sInf S : DepSet α) s ↔ ∀ T ∈ S, x ∈ T s :=
  Iff.rfl

/-- Unordered union of a set of dependent sets, analogous to `Set.sUnion`. -/
def sUnion (S : Set (DepSet α)) : DepSet α :=
  sSup S

/-- Unordered intersection of a set of dependent sets, analogous to `Set.sInter`. -/
def sInter (S : Set (DepSet α)) : DepSet α :=
  sInf S

@[simp] theorem sUnion_eq_sSup (S : Set (DepSet α)) :
    sUnion S = (sSup S : DepSet α) := rfl

@[simp] theorem sInter_eq_sInf (S : Set (DepSet α)) :
    sInter S = (sInf S : DepSet α) := rfl

@[simp]
theorem mem_sUnion {S : Set (DepSet α)} {s : base} {x : α s} :
    x ∈ (sUnion S) s ↔ ∃ T ∈ S, x ∈ T s := by
  simp only [sUnion, mem_sSup]

@[simp]
theorem mem_sInter {S : Set (DepSet α)} {s : base} {x : α s} :
    x ∈ (sInter S) s ↔ ∀ T ∈ S, x ∈ T s := by
  simp only [sInter, mem_sInf]

@[simp]
theorem mem_iSup {ι : Sort*} {S : ι → DepSet α} {s : base} {x : α s} :
    x ∈ (⨆ i, S i : DepSet α) s ↔ ∃ i, x ∈ S i s := by
  constructor
  · intro hx
    rcases hx with ⟨T, hT, hxT⟩
    rcases hT with ⟨i, rfl⟩
    exact ⟨i, hxT⟩
  · rintro ⟨i, hx⟩
    exact ⟨S i, ⟨i, rfl⟩, hx⟩

@[simp]
theorem mem_iInf {ι : Sort*} {S : ι → DepSet α} {s : base} {x : α s} :
    x ∈ (⨅ i, S i : DepSet α) s ↔ ∀ i, x ∈ S i s := by
  constructor
  · intro hx i
    exact hx (S i) ⟨i, rfl⟩
  · intro hx T hT
    rcases hT with ⟨i, rfl⟩
    exact hx i

@[simp]
theorem iSup_apply {ι : Sort*} {S : ι → DepSet α} (s : base) :
    ((⨆ i, S i : DepSet α) s) = ⋃ i, S i s := by
  ext x
  simp only [Set.mem_iUnion, mem_iSup]

@[simp]
theorem iInf_apply {ι : Sort*} {S : ι → DepSet α} (s : base) :
    ((⨅ i, S i : DepSet α) s) = ⋂ i, S i s := by
  ext x
  simp only [Set.mem_iInter, mem_iInf]

/-- Indexed union of dependent sets. -/
def iUnion {ι : Sort*} (S : ι → DepSet α) : DepSet α :=
  ⨆ i, S i

/-- Indexed intersection of dependent sets. -/
def iInter {ι : Sort*} (S : ι → DepSet α) : DepSet α :=
  ⨅ i, S i

@[simp] theorem iUnion_eq_iSup {ι : Sort*} (S : ι → DepSet α) :
    DepSet.iUnion S = (⨆ i, S i : DepSet α) := rfl

@[simp] theorem iInter_eq_iInf {ι : Sort*} (S : ι → DepSet α) :
    DepSet.iInter S = (⨅ i, S i : DepSet α) := rfl

theorem subset_iff {S T : DepSet α} :
    S ⊆ T ↔ ∀ s, S s ⊆ T s := by
  constructor
  · intro h s x
    simpa only [mem_sigma] using h (x := (⟨s, x⟩ : Sigma α))
  · intro h x hx
    obtain ⟨fst, snd⟩ := x
    simp_all only [mem_sigma]
    apply h
    simp_all only

theorem subsetFam {S T : DepSet α} (h : S ⊆ T) : ∀ s, S s ⊆ T s :=
  (subset_iff (S := S) (T := T)).1 h

theorem _root_.Eq.subdepset {A B : DepSet α} : A = B → A ⊆ B := by
  intro h x
  simp_all only [implies_true]

abbrev univ : DepSet α := ofSigma Set.univ

@[simp] lemma univ_carrier {s : base} : (univ : DepSet α).carrier s = Set.univ := by
  rfl

@[simp]
lemma univ_eq_univ : (DepSet.univ (α := α) : Set (Sigma α )) = Set.univ := by
  rfl

@[simp]
lemma mem_univ {s : base} {a : α s} : a ∈ univ s := by
  simp only [univ_carrier, Set.mem_univ]

/-- `powerset S` is the set of all dependent subsets of `S`. -/
def powerset (S : DepSet α) : Set (DepSet α) := {T | T ⊆ S}

/-- The image of `S : DepSet α` by a family map `f : α →ₛ β`, applied sort by sort. -/
def image {β : Fam.{w} base} (f : α →ₛ β) (S : DepSet α) : DepSet β :=
  ⟨fun s => f s '' S s⟩

@[simp] theorem image_apply {β : Fam.{w} base} (f : α →ₛ β) (S : DepSet α) (s : base) :
    (image f S) s = f s '' S s := rfl

@[simp] theorem mem_image {β : Fam.{w} base} {f : α →ₛ β} {S : DepSet α}
    {s : base} {y : β s} :
    y ∈ (image f S) s ↔ ∃ x ∈ S s, f s x = y := Iff.rfl

/-- A dependent set is nonempty if it contains at least one element at some sort. It should be used
in theorem assumptions instead of `∃ s x, x ∈ S s` or `S ≠ ⊥` as it gives access to a nice API
thanks to the dot notation. -/
protected def Nonempty (S : DepSet α) : Prop :=
  ∃ (s : base) (x : α s), x ∈ S s

instance instBoundedOrder : BoundedOrder (DepSet α) where
  bot := ∅
  top := univ
  bot_le _ _ := by apply Set.empty_subset _
  le_top _ _ := by apply Set.subset_univ _

instance : HasSSubset (DepSet α) :=
  ⟨(· < ·)⟩

@[simp]
theorem top_eq_univ : (⊤ : DepSet α) = univ :=
  rfl

@[simp]
theorem bot_eq_empty : (⊥ : DepSet α) = ∅ :=
  rfl

@[simp]
theorem sup_eq_union (S T : DepSet α) : S ⊔ T = S ∪ T :=
  rfl

@[simp]
theorem inf_eq_inter (S T : DepSet α) : S ⊓ T = S ∩ T :=
  rfl

@[simp]
theorem le_eq_subset : ((· ≤ ·) : DepSet α → DepSet α → Prop) = (· ⊆ ·) :=
  rfl

@[simp]
theorem lt_eq_ssubset : ((· < ·) : DepSet α → DepSet α → Prop) = (· ⊂ ·) :=
  rfl

theorem le_iff_subset {S T : DepSet α} : S ≤ T ↔ S ⊆ T :=
  Iff.rfl

theorem lt_iff_ssubset {S T : DepSet α} : S < T ↔ S ⊂ T :=
  Iff.rfl


/-! ### Subset and strict subset relations -/

instance : @Std.Refl (DepSet α) (· ⊆ ·) :=
  show Std.Refl (· ≤ ·) by infer_instance

instance : IsTrans (DepSet α) (· ⊆ ·) :=
  show IsTrans (DepSet α) (· ≤ ·) by infer_instance

instance : Trans ((· ⊆ ·) : DepSet α → DepSet α → Prop) (· ⊆ ·) (· ⊆ ·) :=
  show Trans (· ≤ ·) (· ≤ ·) (· ≤ ·) by infer_instance

instance : @Std.Antisymm (DepSet α) (· ⊆ ·) :=
  show Std.Antisymm (· ≤ ·) by infer_instance

instance : @Std.Irrefl (DepSet α) (· ⊂ ·) :=
  show Std.Irrefl (· < ·) by infer_instance

instance : IsTrans (DepSet α) (· ⊂ ·) :=
  show IsTrans (DepSet α) (· < ·) by infer_instance

instance : Trans ((· ⊂ ·) : DepSet α → DepSet α → Prop) (· ⊆ ·) (· ⊂ ·) :=
  show Trans (· < ·) (· ≤ ·) (· < ·) by infer_instance

instance : Trans ((· ⊆ ·) : DepSet α → DepSet α → Prop) (· ⊂ ·) (· ⊂ ·) :=
  show Trans (· ≤ ·) (· < ·) (· < ·) by infer_instance

instance : @Std.Asymm (DepSet α) (· ⊂ ·) :=
  show Std.Asymm (· < ·) by infer_instance

instance : IsNonstrictStrictOrder (DepSet α) (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩


/-- The underlying family of subtypeVals of a dependent set. -/
protected def Subtype (S : DepSet α) : Fam base := ⟨fun s => S s⟩

instance : CoeTC (DepSet α) (Fam base) := ⟨DepSet.Subtype⟩

/-Maybe make this a simp?-/
lemma coe_fam_apply (S : DepSet α) (s : base) :
  ( (S : Fam base) s ) = { x : α s // x ∈ S s } := rfl

/-- The pointwise coercion map from a dependent subtype family to the ambient family. -/
abbrev subtypeVal (S : DepSet α) : (S : Fam base) →ₛ α :=
  ⟨fun _ x => x.1⟩

/-- The inclusion map from a dependent subset to a dependent superset. -/
def inclusion {S T : DepSet α} (h : S ⊆ T) : S.Subtype →ₛ T.Subtype :=
  ⟨fun s x => ⟨x.1, subsetFam h s x.2⟩⟩

@[simp]
theorem inclusion_apply {S T : DepSet α} (h : S ⊆ T) (s : base) (x : S.Subtype s) :
    inclusion h s x = ⟨x.1, (subsetFam h s x.2)⟩ :=
  rfl

theorem inclusion_injective {S T : DepSet α} (h : S ⊆ T) (s : base) :
    Function.Injective (inclusion h s) := by
  intro x y hxy
  apply Subtype.ext
  injection hxy

@[simp]
theorem subtypeVal_inclusion {S T : DepSet α} (h : S ⊆ T) :
    T.subtypeVal ∘ₛ inclusion h = S.subtypeVal := by
  ext s x
  rfl

theorem inclusion_trans {S T U : DepSet α} (hST : S ⊆ T) (hTU : T ⊆ U) :
    inclusion (subset_trans hST hTU) = inclusion hTU ∘ₛ inclusion hST := by
  ext s x
  rfl

instance : Inhabited (DepSet α) :=
  ⟨∅⟩

instance emptyIsEmpty : ∀ s, IsEmpty ((∅ : DepSet α) s) := by
  intro s
  simp_all only [empty_at_sort, Set.isEmpty_coe_sort]

instance SubtypeEmptyIsEmpty : ∀ s, IsEmpty ((∅ : DepSet α).Subtype s) := by
  intro s
  unfold DepSet.Subtype
  constructor
  intro a ; cases a ; case mk x => cases x

@[trans]
theorem mem_of_mem_of_subset {s : base} {x : α s} {A B : DepSet α} (hx : x ∈ A s) (h : A ⊆ B) :
    x ∈ B s := subsetFam h s hx

variable {A B : DepSet α}

@[grind =]
theorem subset_def : (A ⊆ B) = ∀ s x, x ∈ A s → x ∈ B s := by
  simp only [subset_iff, eq_iff_iff]; rfl

@[grind =]
theorem ssubset_def : (A ⊂ B) = (A ⊆ B ∧ ¬B ⊆ A) :=
  rfl

@[trans]
theorem Subset.trans {A B C : DepSet α} (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := Trans.trans hAB hBC

theorem Subset.antisymm {A B : DepSet α} (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B :=
  Std.Antisymm.antisymm A B hAB hBA

theorem Subset.antisymm_iff {A B : DepSet α} : A = B ↔ A ⊆ B ∧ B ⊆ A :=
  ⟨fun e => ⟨e.subdepset, e.symm.subdepset⟩, fun ⟨hAB, hBA⟩ => Subset.antisymm hAB hBA⟩

-- an alternative name
theorem eq_of_subset_of_subset {A B : DepSet α} : A ⊆ B → B ⊆ A → A = B :=
  Subset.antisymm

theorem mem_of_subset_of_mem {s : base} {a : α s} (h : A ⊆ B) : a ∈ A s → a ∈ B s := by
  apply subsetFam h s

theorem notMem_subset {a} (h : A ⊆ B) : a ∉ B → a ∉ A :=
  mt <| mem_of_subset_of_mem h

theorem not_subset : ¬A ⊆ B ↔ ∃ (s: base), ∃ a ∈ A s, a ∉ B s := by
  simp only [subset_def, not_forall, exists_prop]

theorem not_top_subset : ¬⊤ ⊆ A ↔ ∃ (s: base), ∃ a, a ∉ A s := by
  rw[not_subset (A:= ⊤) (B:= A)]
  simp_all only [top_eq_univ, mem_univ, true_and]

lemma eq_of_forall_subset_iff (h : ∀ u, A ⊆ u ↔ B ⊆ u) : A = B := eq_of_forall_ge_iff h

/-! ### Definition of strict subsets `A ⊂ B` and basic properties. -/

protected theorem eq_or_ssubset_of_subset (h : A ⊆ B) : A = B ∨ A ⊂ B :=
  eq_or_lt_of_le h

theorem exists_of_ssubset {A B : DepSet α} (h : A ⊂ B) : ∃ s, ∃ x ∈ B s, x ∉ A s :=
  not_subset.1 h.2

protected theorem ssubset_iff_subset_ne {A B : DepSet α} : A ⊂ B ↔ A ⊆ B ∧ A ≠ B :=
  @lt_iff_le_and_ne (DepSet α) _ A B

theorem ssubset_iff_of_subset {A B : DepSet α} (h : A ⊆ B) : A ⊂ B ↔ ∃ s, ∃ x ∈ B s, x ∉ A s :=by
  simpa only [SetLike.coe_ssubset_coe, lt_eq_ssubset, SetLike.mem_coe, Sigma.exists,
    mem_sigma] using Set.ssubset_iff_of_subset (α := Sigma α) h

theorem ssubset_iff_exists {A B : DepSet α} : A ⊂ B ↔ A ⊆ B ∧ ∃ s, ∃ x ∈ B s, x ∉ A s :=
  ⟨fun h ↦ ⟨h.le, DepSet.exists_of_ssubset h⟩,
  fun ⟨h1, h2⟩ ↦ (DepSet.ssubset_iff_of_subset h1).mpr h2⟩

protected theorem ssubset_of_ssubset_of_subset {A B C : DepSet α} (hAB : A ⊂ B)
    (hBC : B ⊆ C) : A ⊂ C :=
  ⟨Subset.trans hAB.1 hBC, fun hCA => hAB.2 (Subset.trans hBC hCA)⟩

protected theorem ssubset_of_subset_of_ssubset {A B C : DepSet α} (hAB : A ⊆ B)
    (hBC : B ⊂ C) : A ⊂ C :=
  ⟨Subset.trans hAB hBC.1, fun hCA => hBC.2 (Subset.trans hCA hAB)⟩

theorem notMem_empty {s : base} (x : α s) : x ∉ (∅ : DepSet α) s :=
  id


/-!

### Universal set.

In Lean `@univ α` (or `univ : DepSet α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/


@[simp]
theorem univ_eq_empty_iff : (univ : DepSet α) = ∅ ↔ IsEmpty (Sigma α) := by
  constructor
  · intro h
    refine ⟨?f⟩
    intro x
    have hx : x.2 ∈ (univ : DepSet α) x.1 := mem_univ (s:=x.1) (a:=x.2)
    have hx' : x.2 ∈ (∅ : DepSet α) x.1 := by simp_all only [empty_at_sort, Set.mem_empty_iff_false]
    simp_all only [empty_at_sort, Set.mem_empty_iff_false]
  · intro h
    ext s x
    exact (False.elim (h.false ⟨s, x⟩))

theorem empty_ne_univ [Nonempty (Sigma α)] : (∅ : DepSet α) ≠ univ := by
  intro h
  exact Set.empty_ne_univ <| congrArg DepSet.sigma h

@[simp, grind ←]
theorem subset_univ (A : DepSet α) : A ⊆ univ := by
  change (A : Set (Sigma α) ) ⊆ Set.univ
  simp only [Set.subset_univ]

@[simp, grind =]
theorem univ_subset_iff {A : DepSet α} : univ ⊆ A ↔ A = univ :=
  @top_le_iff _ _ _ A

alias ⟨eq_univ_of_univ_subset, _⟩ := univ_subset_iff

theorem eq_univ_iff_forall {A : DepSet α} : A = univ ↔ ∀ s, ∀ x : α s, x ∈ A s := by
  constructor
  · intro h s x
    simp [h]
  · intro h
    apply eq_univ_of_univ_subset
    simp_all only [univ_subset_iff]
    ext s x : 1
    simp_all only [univ_carrier, Set.mem_univ]

theorem eq_univ_of_forall {A : DepSet α} : (∀ s, ∀ x : α s, x ∈ A s) → A = univ :=
  eq_univ_iff_forall.2

theorem eq_univ_of_subset {A B : DepSet α} (h : A ⊆ B) (hA : A = univ) : B = univ :=
  eq_univ_of_univ_subset <| (hA ▸ h : univ ⊆ B)

theorem exists_mem_of_nonempty [Nonempty (Sigma α)] :
    ∃ s, ∃ x : α s, x ∈ (univ : DepSet α) s := by
  rcases ‹Nonempty (Sigma α)› with ⟨⟨s, x⟩⟩
  exact ⟨s, x, mem_univ (s:=s) (a:=x)⟩

theorem ne_univ_iff_exists_notMem (A : DepSet α) : A ≠ univ ↔ ∃ s, ∃ a, a ∉ A s := by
  classical
  simp [eq_univ_iff_forall, not_forall]

theorem not_subset_iff_exists_mem_notMem {A B : DepSet α} :
    ¬A ⊆ B ↔ ∃ s, ∃ x, x ∈ A s ∧ x ∉ B s := by
  classical
  simpa [exists_prop] using (not_subset (A:=A) (B:=B))

-- NOTE: `univ_unique` uses `Unique` on a family; no direct DepSet analogue.
-- theorem univ_unique [Unique (Sigma α)] : @DepSet.univ base α = {default} := ...

theorem ssubset_univ_iff {A : DepSet α} : A ⊂ univ ↔ A ≠ univ :=
  lt_top_iff_ne_top

instance nontrivial_of_nonempty [Nonempty (Sigma α)] : Nontrivial (DepSet α) :=
  ⟨⟨∅, univ, empty_ne_univ⟩⟩

/-! ### Lemmas about union -/

theorem mem_union_left {s : base} {x : α s} {A : DepSet α} (B : DepSet α) :
    x ∈ A s → x ∈ (A ∪ B) s :=
  Or.inl

theorem mem_union_right {s : base} {x : α s} {B : DepSet α} (A : DepSet α) :
    x ∈ B s → x ∈ (A ∪ B) s :=
  Or.inr

theorem mem_or_mem_of_mem_union {s : base} {x : α s} {A B : DepSet α} (H : x ∈ (A ∪ B) s) :
    x ∈ A s ∨ x ∈ B s :=
  H

theorem MemUnion.elim {s : base} {x : α s} {A B : DepSet α} {P : Prop} (H₁ : x ∈ (A ∪ B) s)
    (H₂ : x ∈ A s → P) (H₃ : x ∈ B s → P) : P :=
  Or.elim H₁ H₂ H₃

@[simp, grind =, push]
theorem mem_union {s : base} (x : α s) (A B : DepSet α) :
    x ∈ (A ∪ B) s ↔ x ∈ A s ∨ x ∈ B s :=
  Iff.rfl

@[simp]
theorem union_self (A : DepSet α) : A ∪ A = A :=
  ext fun _ _ => or_self_iff

@[simp]
theorem union_empty (A : DepSet α) : A ∪ ∅ = A :=
  ext fun _ _ => iff_of_eq (or_false _)

@[simp]
theorem empty_union (A : DepSet α) : ∅ ∪ A = A :=
  ext fun _ _ => iff_of_eq (false_or _)

theorem union_comm (A B : DepSet α) : A ∪ B = B ∪ A :=
  ext fun _ _ => or_comm

theorem union_assoc (A B C : DepSet α) : A ∪ B ∪ C = A ∪ (B ∪ C) :=
  ext fun _ _ => or_assoc

instance union_isAssoc : Std.Associative (α := DepSet α) (· ∪ ·) :=
  ⟨union_assoc⟩

instance union_isComm : Std.Commutative (α := DepSet α) (· ∪ ·) :=
  ⟨union_comm⟩

theorem union_left_comm (A B C : DepSet α) : A ∪ (B ∪ C) = B ∪ (A ∪ C) :=
  ext fun _ _ => or_left_comm

theorem union_right_comm (A B C : DepSet α) : A ∪ B ∪ C = A ∪ C ∪ B :=
  ext fun _ _ => or_right_comm

@[simp]
theorem union_eq_left {A B : DepSet α} : A ∪ B = A ↔ B ⊆ A :=
  sup_eq_left

@[simp]
theorem union_eq_right {A B : DepSet α} : A ∪ B = B ↔ A ⊆ B :=
  sup_eq_right

theorem union_eq_self_of_subset_left {A B : DepSet α} (h : A ⊆ B) : A ∪ B = B :=
  union_eq_right.mpr h

theorem union_eq_self_of_subset_right {A B : DepSet α} (h : B ⊆ A) : A ∪ B = A :=
  union_eq_left.mpr h

@[simp]
theorem subset_union_left {A B : DepSet α} : A ⊆ A ∪ B := Set.subset_union_left

@[simp]
theorem subset_union_right {A B : DepSet α} : B ⊆ A ∪ B := Set.subset_union_right

theorem union_subset {A B C : DepSet α} (hA : A ⊆ C) (hB : B ⊆ C) : A ∪ B ⊆ C :=
  Set.union_subset hA hB

@[simp]
theorem union_subset_iff {A B C : DepSet α} : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  simpa using (sup_le_iff : A ⊔ B ≤ C ↔ A ≤ C ∧ B ≤ C)

@[gcongr]
theorem union_subset_union {A₁ A₂ B₁ B₂ : DepSet α} (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) :
    A₁ ∪ B₁ ⊆ A₂ ∪ B₂ := Set.union_subset_union hA hB

/-
theorem subset_union_of_subset_left {A B : DepSet α} (h : A ⊆ B) (C : DepSet α) : A ⊆ B ∪ C := by
  apply Set.subset_union_of_subset_left
  simp_all only [SetLike.coe_subset_coe, le_eq_subset]

theorem subset_union_of_subset_right {A C : DepSet α} (h : A ⊆ C) (B : DepSet α) : A ⊆ B ∪ C := by
  intro s x hx
  exact Or.inr (h s hx)

theorem union_congr_left {A B C : DepSet α} (hB : B ⊆ A ∪ C) (hC : C ⊆ A ∪ B) : A ∪ B = A ∪ C :=
  sup_congr_left hB hC

theorem union_congr_right {A B C : DepSet α} (hA : A ⊆ B ∪ C) (hB : B ⊆ A ∪ C) : A ∪ C = B ∪ C :=
  sup_congr_right hA hB

theorem union_eq_union_iff_left {A B C : DepSet α} : A ∪ B = A ∪ C ↔ B ⊆ A ∪ C ∧ C ⊆ A ∪ B :=
  sup_eq_sup_iff_left

theorem union_eq_union_iff_right {A B C : DepSet α} : A ∪ C = B ∪ C ↔ A ⊆ B ∪ C ∧ B ⊆ A ∪ C :=
  sup_eq_sup_iff_right
-/

@[simp]
theorem union_empty_iff {A B : DepSet α} : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ := by
  simpa using (sup_eq_bot_iff : A ⊔ B = ⊥ ↔ A = ⊥ ∧ B = ⊥)

@[simp]
theorem union_univ (A : DepSet α) : A ∪ univ = univ := sup_top_eq _

@[simp]
theorem univ_union (A : DepSet α) : univ ∪ A = univ := top_sup_eq _

@[simp]
theorem ssubset_union_left_iff {A B : DepSet α} : A ⊂ A ∪ B ↔ ¬ B ⊆ A :=
  left_lt_sup

@[simp]
theorem ssubset_union_right_iff {A B : DepSet α} : B ⊂ A ∪ B ↔ ¬ A ⊆ B :=
  right_lt_sup

/-! ### Lemmas about intersection -/

-- NOTE: `inter_def` uses set-builder notation; no direct DepSet analogue.
-- theorem inter_def {A B : DepSet α} : A ∩ B = { a | a ∈ A ∧ a ∈ B } := rfl

@[simp, mfld_simps, grind =, push]
theorem mem_inter_iff {s : base} (x : α s) (A B : DepSet α) :
    x ∈ (A ∩ B) s ↔ x ∈ A s ∧ x ∈ B s :=
  Iff.rfl

theorem mem_inter {s : base} {x : α s} {A B : DepSet α} (hA : x ∈ A s) (hB : x ∈ B s) :
    x ∈ (A ∩ B) s :=
  ⟨hA, hB⟩

theorem mem_of_mem_inter_left {s : base} {x : α s} {A B : DepSet α} (h : x ∈ (A ∩ B) s) :
    x ∈ A s :=
  h.left

theorem mem_of_mem_inter_right {s : base} {x : α s} {A B : DepSet α} (h : x ∈ (A ∩ B) s) :
    x ∈ B s :=
  h.right

@[simp]
theorem inter_self (A : DepSet α) : A ∩ A = A :=
  ext fun _ _ => and_self_iff

@[simp]
theorem inter_empty (A : DepSet α) : A ∩ ∅ = ∅ :=
  ext fun _ _ => iff_of_eq (and_false _)

@[simp]
theorem empty_inter (A : DepSet α) : ∅ ∩ A = ∅ :=
  ext fun _ _ => iff_of_eq (false_and _)

theorem inter_comm (A B : DepSet α) : A ∩ B = B ∩ A :=
  ext fun _ _ => and_comm

theorem inter_assoc (A B C : DepSet α) : A ∩ B ∩ C = A ∩ (B ∩ C) :=
  ext fun _ _ => and_assoc

instance inter_isAssoc : Std.Associative (α := DepSet α) (· ∩ ·) :=
  ⟨inter_assoc⟩

instance inter_isComm : Std.Commutative (α := DepSet α) (· ∩ ·) :=
  ⟨inter_comm⟩

theorem inter_left_comm (A B C : DepSet α) : A ∩ (B ∩ C) = B ∩ (A ∩ C) :=
  ext fun _ _ => and_left_comm

theorem inter_right_comm (A B C : DepSet α) : A ∩ B ∩ C = A ∩ C ∩ B :=
  ext fun _ _ => and_right_comm

@[simp, mfld_simps]
theorem inter_subset_left {A B : DepSet α} : A ∩ B ⊆ A := by
  apply Set.inter_subset_left

@[simp]
theorem inter_subset_right {A B : DepSet α} : A ∩ B ⊆ B := by
  apply Set.inter_subset_right

@[simp]
theorem subset_inter_iff {A B C : DepSet α} : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  simpa using (le_inf_iff : C ≤ A ⊓ B ↔ C ≤ A ∧ C ≤ B)

@[simp] lemma inter_eq_left {A B : DepSet α} : A ∩ B = A ↔ A ⊆ B := inf_eq_left

@[simp] lemma inter_eq_right {A B : DepSet α} : A ∩ B = B ↔ B ⊆ A := inf_eq_right

@[simp] lemma left_eq_inter {A B : DepSet α} : A = A ∩ B ↔ A ⊆ B := left_eq_inf

@[simp] lemma right_eq_inter {A B : DepSet α} : B = A ∩ B ↔ B ⊆ A := right_eq_inf

theorem inter_eq_self_of_subset_left {A B : DepSet α} : A ⊆ B → A ∩ B = A :=
  inter_eq_left.mpr

theorem inter_eq_self_of_subset_right {A B : DepSet α} : B ⊆ A → A ∩ B = B :=
  inter_eq_right.mpr

theorem inter_congr_left {A B C : DepSet α} (hB : A ∩ C ⊆ B) (hC : A ∩ B ⊆ C) : A ∩ B = A ∩ C :=
  inf_congr_left hB hC

theorem inter_congr_right {A B C : DepSet α} (hA : B ∩ C ⊆ A) (hB : A ∩ C ⊆ B) : A ∩ C = B ∩ C :=
  inf_congr_right hA hB

theorem inter_eq_inter_iff_left {A B C : DepSet α} : A ∩ B = A ∩ C ↔ A ∩ C ⊆ B ∧ A ∩ B ⊆ C :=
  inf_eq_inf_iff_left

theorem inter_eq_inter_iff_right {A B C : DepSet α} : A ∩ C = B ∩ C ↔ B ∩ C ⊆ A ∧ A ∩ C ⊆ B :=
  inf_eq_inf_iff_right

@[simp, mfld_simps]
theorem inter_univ (A : DepSet α) : A ∩ univ = A := inf_top_eq _

@[simp, mfld_simps]
theorem univ_inter (A : DepSet α) : univ ∩ A = A := top_inf_eq _

@[gcongr]
theorem inter_subset_inter {A₁ A₂ B₁ B₂ : DepSet α} (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) :
    A₁ ∩ B₁ ⊆ A₂ ∩ B₂ := by
 apply Set.inter_subset_inter hA hB

@[simp]
theorem inter_ssubset_right_iff {A B : DepSet α} : A ∩ B ⊂ B ↔ ¬ B ⊆ A :=
  inf_lt_right

@[simp]
theorem inter_ssubset_left_iff {A B : DepSet α} : A ∩ B ⊂ A ↔ ¬ A ⊆ B :=
  inf_lt_left

/-! ### Distributivity laws -/

theorem inter_union_distrib_left (A B C : DepSet α) : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C :=
  inf_sup_left _ _ _

theorem union_inter_distrib_right (A B C : DepSet α) : (A ∪ B) ∩ C = A ∩ C ∪ B ∩ C :=
  inf_sup_right _ _ _

theorem union_inter_distrib_left (A B C : DepSet α) : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) :=
  sup_inf_left _ _ _

theorem inter_union_distrib_right (A B C : DepSet α) : A ∩ B ∪ C = (A ∪ C) ∩ (B ∪ C) :=
  sup_inf_right _ _ _

theorem union_union_distrib_left (A B C : DepSet α) : A ∪ (B ∪ C) = A ∪ B ∪ (A ∪ C) :=
  sup_sup_distrib_left _ _ _

theorem union_union_distrib_right (A B C : DepSet α) : A ∪ B ∪ C = A ∪ C ∪ (B ∪ C) :=
  sup_sup_distrib_right _ _ _

theorem inter_inter_distrib_left (A B C : DepSet α) : A ∩ (B ∩ C) = A ∩ B ∩ (A ∩ C) :=
  inf_inf_distrib_left _ _ _

theorem inter_inter_distrib_right (A B C : DepSet α) : A ∩ B ∩ C = A ∩ C ∩ (B ∩ C) :=
  inf_inf_distrib_right _ _ _

theorem union_union_union_comm (A B C D : DepSet α) : A ∪ B ∪ (C ∪ D) = A ∪ C ∪ (B ∪ D) :=
  sup_sup_sup_comm _ _ _ _

theorem inter_inter_inter_comm (A B C D : DepSet α) : A ∩ B ∩ (C ∩ D) = A ∩ C ∩ (B ∩ D) :=
  inf_inf_inf_comm _ _ _ _

@[simp]
lemma union_ofSigma {S T : Set (Sigma α)} :
  ofSigma (S ∪ T) = ofSigma S ∪ ofSigma T := by
  rfl

@[simp]
lemma inter_ofSigma {S T : Set (Sigma α)} :
  ofSigma (S ∩ T) = ofSigma S ∩ ofSigma T := by
  rfl

/-! ### Finiteness of DepSets -/

/-- A DepSet is finite if its sigma type is finite. -/
def IsFinite (S : DepSet α) : Prop := Finite S

/-- A DepSet constructed from a Finset is finite. -/
theorem ofSigma_finset_isFinite (F : Finset (Sigma α)) :
    (DepSet.ofSigma (α := α) (F : Set (Sigma α))).IsFinite := by
  unfold IsFinite
  unfold ofSigma
  exact Finset.finite_toSet F

/-- The empty DepSet is finite. -/
theorem bot_isFinite : (⊥ : DepSet α).IsFinite := by
  reduce
  apply Finite.intro (n:= 0)
  exact ⟨default, default, by intro h; rcases h with ⟨x, y⟩; simp at y
         ,by intro h; rcases h with ⟨x, y⟩; simp at y ⟩

/-- If S ⊆ T and T is finite, then S is finite. -/
theorem subset_isFinite {S T : DepSet α} (h : S ⊆ T) (hT : T.IsFinite) : S.IsFinite := by
  apply Set.Finite.subset hT
  simp_all only [SetLike.coe_subset_coe]

/-- The union of two finite DepSets is finite. -/
theorem sup_isFinite {S T : DepSet α} (hS : S.IsFinite) (hT : T.IsFinite) :
    (S ⊔ T).IsFinite := Set.Finite.sup hS hT

/-- Connection to Finite on the coerced Fam. -/
theorem isFinite_iff_finite_sigma (S : DepSet α) :
    S.IsFinite ↔ Finite (Sigma (S : Fam base)) :=
  by
    classical
    unfold IsFinite
    let e : (S : Type _) ≃ Sigma (S : Fam base) :=
    { toFun := fun x => by
        rcases x with ⟨⟨s, a⟩, hx⟩
        refine ⟨s, ⟨a, ?_⟩⟩
        simpa [mem_sigma] using hx
      invFun := fun y => by
        rcases y with ⟨s, ya⟩
        rcases ya with ⟨a, ha⟩
        refine ⟨⟨s, a⟩, ?_⟩
        simpa [mem_sigma] using ha
      left_inv := by
        intro x
        rcases x with ⟨⟨s, a⟩, hx⟩
        rfl
      right_inv := by
        intro y
        rcases y with ⟨s, ya⟩
        rcases ya with ⟨a, ha⟩
        rfl }
    constructor
    · intro h
      haveI : Finite (S : Type _) := h
      -- turn finite into fintype, transport along the equivalence, then back to finite
      letI : Fintype (S : Type _) := Fintype.ofFinite (S : Type _)
      letI : Fintype (Sigma (S : Fam base)) := Fintype.ofEquiv (S : Type _) e
      exact (by infer_instance : Finite (Sigma (S : Fam base)))
    · intro h
      haveI : Finite (Sigma (S : Fam base)) := h
      letI : Fintype (Sigma (S : Fam base)) := Fintype.ofFinite (Sigma (S : Fam base))
      letI : Fintype (S : Type _) := Fintype.ofEquiv (Sigma (S : Fam base)) e.symm
      exact (by infer_instance : Finite (S : Type _))


end DepSet


section dep_setlike

/-!
### `DepSetLike` — a typeclass for types that behave like dependent families of sets

This mirrors Mathlib's `SetLike` but for the many-sorted setting. The canonical coercion
is `F → DepSet α`, analogous to `SetLike.coe : A → Set B`. All derived operations
(`Subtype`, `subtypeVal`, `ext`, coercion to `Fam base`) route through `DepSet`'s
existing API.
-/

/-- A typeclass for types that behave like dependent families of sets over `α`.
    The canonical data is a coercion to `DepSet α`, which must be injective.
    This mirrors `SetLike` from Mathlib. -/
class DepSetLike (F : Type*) {base : outParam (Type*)} (α : outParam (Fam base)) where
  /-- The coercion from `F` to `DepSet α`. -/
  protected toDepSet : F → DepSet α
  /-- The coercion is injective. -/
  protected toDepSet_injective : Function.Injective toDepSet

attribute [coe] DepSetLike.toDepSet

namespace DepSetLike

variable {base : Type*} {α : Fam base} {F : Type*} [DepSetLike F α]

instance instCoeDepSet : CoeTC F (DepSet α) where
  coe := DepSetLike.toDepSet

instance instCoeFun : CoeFun F (fun _ => ∀ s, Set (α s)) where
  coe S := (DepSetLike.toDepSet S).carrier

instance (priority := 100) instCoeSortedTypes : CoeTC F (Fam base) :=
  ⟨fun S => (DepSetLike.toDepSet S).Subtype⟩

/-- Access the carrier of a `DepSetLike` element at a given sort. -/
def carrier (S : F) : ∀ s, Set (α s) :=
  (DepSetLike.toDepSet S).carrier

@[simp]
theorem carrier_toDepSet (S : F) : (DepSetLike.toDepSet S).carrier = carrier S := rfl

/-- The subtypeVal family, routed through `DepSet.Subtype`. -/
def toFam (S : F) : Fam base :=
  (DepSetLike.toDepSet S).Subtype

@[simp]
theorem toFam_apply (S : F) (s : base) :
    toFam S s = { x : α s // x ∈ carrier S s } := rfl

/-- The pointwise `Subtype.val` map, routed through `DepSet.subtypeVal`. -/
def subtypeValVal (S : F) : toFam S →ₛ α :=
  (DepSetLike.toDepSet S).subtypeVal

@[simp]
theorem subtypeValVal_apply (S : F) (s : base) (x : toFam S s) :
    subtypeValVal S s x = x.1 := rfl

/-- Two elements of a `DepSetLike` type are equal iff they have the same members everywhere. -/
theorem ext {S T : F} (h : ∀ s x, x ∈ carrier S s ↔ x ∈ carrier T s) : S = T :=
  DepSetLike.toDepSet_injective (DepSet.ext h)

/-! ### Ordering and Membership -/

/-- Inherit the partial order from `DepSet` via the coercion. -/
instance instPartialOrder : PartialOrder F :=
  PartialOrder.lift (fun S => (S : DepSet α)) (DepSetLike.toDepSet_injective)

/-- Use `⊆` as notation for the inherited order. -/
instance instHasSubset : HasSubset F := ⟨fun S T => S ≤ T⟩

/-- Inherit membership of `Sigma α` from the coerced `DepSet`. -/
instance instMembershipSigma : Membership (Sigma α) F :=
  ⟨fun S x => x ∈ (S : DepSet α)⟩

@[simp] lemma le_def {S T : F} : S ≤ T ↔ ((S : DepSet α) ≤ (T : DepSet α)) := Iff.rfl

@[simp] lemma subset_def {S T : F} : S ⊆ T ↔ ((S : DepSet α) ⊆ (T : DepSet α)) := Iff.rfl

@[simp] lemma mem_def {x : Sigma α} {S : F} : x ∈ S ↔ x ∈ (S : DepSet α) := Iff.rfl

end DepSetLike

end dep_setlike

end MSFirstOrder
