import MultisortedLogic.Basic

/-
Based on the corresponding Mathlib file Mathlib\ModelTheory\LanguageMap.lean
which was authored by 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn,
and is released under the Apache 2.0 license.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/
universe u v z u' v' z' w w'

namespace MSFirstOrder
namespace MSLanguage

open MSStructure Cardinal Fam

variable {Sorts : Type z} (L : MSLanguage.{u, v, z} Sorts) (L' : MSLanguage.{u', v', z} Sorts)
variable {M : Sorts → Type w} [L.MSStructure M]


variable (σ : List Sorts)
/-- A language homomorphism maps the symbols of one language to symbols of another. -/
structure LHom where
  /-- The mapping of functions -/
  onFunction : ∀ ⦃σ t⦄, L.Functions σ t → L'.Functions σ t := by
    exact fun {σ t} => isEmptyElim
  /-- The mapping of relations -/
  onRelation : ∀ ⦃σ⦄, L.Relations σ → L'.Relations σ :=by
    exact fun {σ} => isEmptyElim

--@[inherit_doc FirstOrder.Language.LHom]
infixl:10 " →ᴸ " => LHom
-- \^L

variable {L L'}

namespace LHom

variable (ϕ : L →ᴸ L')

/-- Pulls a structure back along a language map. -/
def reduct (M : Sorts → Type*) [L'.MSStructure M] : L.MSStructure M where
  funMap f xs := funMap (ϕ.onFunction f) xs
  RelMap r xs := RelMap (ϕ.onRelation r) xs

/-- The identity language homomorphism. -/
@[simps]
protected def id (L : MSLanguage Sorts) : L →ᴸ L :=
  ⟨fun _σ _t => id, fun _σ => id⟩

instance : Inhabited (L →ᴸ L) :=
  ⟨LHom.id L⟩

/-- The inclusion of the left factor into the sum of two languages. -/
@[simps]
protected def sumInl : L →ᴸ L.sum L' :=
  ⟨fun _σ _t => Sum.inl, fun _σ => Sum.inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
@[simps]
protected def sumInr : L' →ᴸ L.sum L' :=
  ⟨fun _σ _t => Sum.inr, fun _σ => Sum.inr⟩

variable (L L')

/-- The inclusion of an empty language into any other language. -/
@[simps]
protected def ofIsEmpty [L.IsAlgebraic] [L.IsRelational] : L →ᴸ L' where

variable {L L'} {L'' : MSLanguage Sorts}

@[ext]
protected theorem funext {F G : L →ᴸ L'} (h_fun : F.onFunction = G.onFunction)
    (h_rel : F.onRelation = G.onRelation) : F = G := by
  obtain ⟨Ff, Fr⟩ := F
  obtain ⟨Gf, Gr⟩ := G
  simp only [mk.injEq]
  exact And.intro h_fun h_rel

instance [L.IsAlgebraic] [L.IsRelational] : Unique (L →ᴸ L') :=
  ⟨⟨LHom.ofIsEmpty L L'⟩, fun _ => LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- The composition of two language homomorphisms. -/
@[simps]
def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
  ⟨fun _σ _t F => g.1 (f.1 F), fun _σ R => g.2 (f.2 R)⟩

-- added ᴸ to avoid clash with function composition
@[inherit_doc]
local infixl:60 " ∘ᴸ " => LHom.comp
-- \^L

@[simp]
theorem id_comp (F : L →ᴸ L') : LHom.id L' ∘ᴸ F = F := by
  cases F
  rfl

@[simp]
theorem comp_id (F : L →ᴸ L') : F ∘ᴸ LHom.id L = F := by
  cases F
  rfl

theorem comp_assoc {L3 : MSLanguage Sorts} (F : L'' →ᴸ L3) (G : L' →ᴸ L'') (H : L →ᴸ L') :
    F ∘ᴸ G ∘ᴸ H = F ∘ᴸ (G ∘ᴸ H) :=
  rfl

section SumElim

variable (ψ : L'' →ᴸ L')

/-- A language map defined on two factors of a sum. -/
@[simps]
protected def sumElim : L.sum L'' →ᴸ L' where
  onFunction _σ _t := Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _σ  := Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

theorem sumElim_comp_inl (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInl = ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

theorem sumElim_comp_inr (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInr = ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

theorem sumElim_inl_inr : LHom.sumInl.sumElim LHom.sumInr = LHom.id (L.sum L') :=
  LHom.funext (funext₂ fun _σ _t => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)

theorem comp_sumElim {L3 : MSLanguage Sorts} (θ : L' →ᴸ L3) :
    θ ∘ᴸ ϕ.sumElim ψ = (θ ∘ᴸ ϕ).sumElim (θ ∘ᴸ ψ) :=
  LHom.funext (funext₂ fun _σ _t => Sum.comp_elim _ _ _) (funext fun _σ => Sum.comp_elim _ _ _)

end SumElim

section SumMap

variable {L₁ L₂ : MSLanguage Sorts} (ψ : L₁ →ᴸ L₂)

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps]
def sumMap : L.sum L₁ →ᴸ L'.sum L₂ where
  onFunction _σ _t := Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _σ    := Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

@[simp]
theorem sumMap_comp_inl : ϕ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

@[simp]
theorem sumMap_comp_inr : ϕ.sumMap ψ ∘ᴸ LHom.sumInr = LHom.sumInr ∘ᴸ ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

end SumMap

/-- A language homomorphism is injective when all the maps between symbol types are. -/
protected structure Injective : Prop where
  onFunction {σ : List Sorts} {t} : Function.Injective fun f : L.Functions σ t => onFunction ϕ f
  onRelation {σ : List Sorts} : Function.Injective fun R : L.Relations σ => onRelation ϕ R


/-- Pulls an `L`-structure along a language map `ϕ : L →ᴸ L'`, and then expands it
  to an `L'`-structure arbitrarily. -/
noncomputable def defaultExpansion (ϕ : L →ᴸ L')
    [∀ (σ t) (f : L'.Functions σ t),
    Decidable (f ∈ Set.range fun f : L.Functions σ t => onFunction ϕ f)]
    [∀ (σ) (r : L'.Relations σ), Decidable (r ∈ Set.range fun r : L.Relations σ => onRelation ϕ r)]
    (M : Sorts → Type*) [∀ s, Inhabited (M s)] [L.MSStructure M] : L'.MSStructure M where
  funMap {σ t} f xs :=
    if h' : f ∈ Set.range fun f : L.Functions σ t => onFunction ϕ f then funMap h'.choose xs
    else default
  RelMap {σ} r xs :=
    if h' : r ∈ Set.range fun r : L.Relations σ => onRelation ϕ r then RelMap h'.choose xs
    else default

/-- A language homomorphism is an expansion on a structure if it commutes with the interpretation of
all symbols on that structure. -/
class IsExpansionOn (M : Sorts → Type*) [L.MSStructure M] [L'.MSStructure M] : Prop where
  map_onFunction :
    ∀ {σ t} (f : L.Functions σ t) (x : SortedTuple σ M),
    funMap (ϕ.onFunction f) x = funMap f x := by
      exact fun {n} => isEmptyElim
  map_onRelation :
    ∀ {σ} (R : L.Relations σ) (x : SortedTuple σ M), RelMap (ϕ.onRelation R) x = RelMap R x := by
      exact fun {n} => isEmptyElim

@[simp]
theorem map_onFunction {M : Sorts → Type*} [L.MSStructure M] [L'.MSStructure M]
    [ϕ.IsExpansionOn M] {σ} {t} (f : L.Functions σ t) (x : SortedTuple σ M) :
    funMap (ϕ.onFunction f) x = funMap f x := IsExpansionOn.map_onFunction f x

@[simp]
theorem map_onRelation {M : Sorts → Type*} [L.MSStructure M] [L'.MSStructure M]
    [ϕ.IsExpansionOn M] {σ} (R : L.Relations σ) (x : SortedTuple σ M) :
    RelMap (ϕ.onRelation R) x = RelMap R x := IsExpansionOn.map_onRelation R x

instance id_isExpansionOn (M : Sorts → Type*) [L.MSStructure M] : IsExpansionOn (LHom.id L) M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

instance ofIsEmpty_isExpansionOn (M : Sorts → Type*) [L.MSStructure M] [L'.MSStructure M]
    [L.IsAlgebraic] [L.IsRelational] : IsExpansionOn (LHom.ofIsEmpty L L') M where


instance sumElim_isExpansionOn {L'' : MSLanguage Sorts} (ψ : L'' →ᴸ L') (M : Sorts → Type*)
    [L.MSStructure M] [L'.MSStructure M] [L''.MSStructure M]
    [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] : (ϕ.sumElim ψ).IsExpansionOn M :=
  ⟨fun f _xs => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

instance sumMap_isExpansionOn {L₁ L₂ : MSLanguage Sorts} (ψ : L₁ →ᴸ L₂) (M : Sorts → Type*)
    [L.MSStructure M] [L'.MSStructure M] [L₁.MSStructure M] [L₂.MSStructure M]
    [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] : (ϕ.sumMap ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

instance sumInl_isExpansionOn (M : Sorts → Type*) [L.MSStructure M] [L'.MSStructure M] :
    (LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

instance sumInr_isExpansionOn (M : Sorts → Type*) [L.MSStructure M] [L'.MSStructure M] :
    (LHom.sumInr : L' →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

@[simp]
theorem funMap_sumInl [(L.sum L').MSStructure M]
    [(LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M] {σ} {t}
    {f : L.Functions σ t} {x : SortedTuple σ M} :
    @funMap Sorts (L.sum L') M _ σ t (Sum.inl f) x = funMap f x :=
  (LHom.sumInl : L →ᴸ L.sum L').map_onFunction f x

@[simp]
theorem funMap_sumInr [(L'.sum L).MSStructure M]
    [(LHom.sumInr : L →ᴸ L'.sum L).IsExpansionOn M] {σ} {t}
    {f : L.Functions σ t} {x : SortedTuple σ M} :
    @funMap Sorts (L'.sum L) M _ σ t (Sum.inr f) x = funMap f x :=
  (LHom.sumInr : L →ᴸ L'.sum L).map_onFunction f x

theorem sumInl_injective : (LHom.sumInl : L →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inl_injective h, fun h => Sum.inl_injective h⟩

theorem sumInr_injective : (LHom.sumInr : L' →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inr_injective h, fun h => Sum.inr_injective h⟩

instance (priority := 100) isExpansionOn_reduct (ϕ : L →ᴸ L') (M : Sorts → Type*)
    [L'.MSStructure M] :  @IsExpansionOn Sorts L L' ϕ M (ϕ.reduct M) _ :=
  letI := ϕ.reduct M
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

theorem Injective.isExpansionOn_default {ϕ : L →ᴸ L'}
    [∀ (σ t) (f : L'.Functions σ t),
    Decidable (f ∈ Set.range fun f : L.Functions σ t => ϕ.onFunction f)]
    [∀ (σ) (r : L'.Relations σ), Decidable (r ∈ Set.range fun r : L.Relations σ => ϕ.onRelation r)]
    (h : ϕ.Injective) (M : Sorts → Type*) [∀ s, Inhabited (M s)] [L.MSStructure M] :
    @IsExpansionOn Sorts L L' ϕ M _ (ϕ.defaultExpansion M) := by
  letI := ϕ.defaultExpansion M
  refine ⟨fun {σ t} f xs => ?_, fun {σ} r xs => ?_⟩
  · have hf : ϕ.onFunction f ∈ Set.range fun f : L.Functions σ t => ϕ.onFunction f := ⟨f, rfl⟩
    refine (dif_pos hf).trans ?_
    rw [h.onFunction hf.choose_spec]
  · have hr : ϕ.onRelation r ∈ Set.range fun r : L.Relations σ => ϕ.onRelation r := ⟨r, rfl⟩
    refine (dif_pos hr).trans ?_
    rw [h.onRelation hr.choose_spec]

end LHom

/-- A language equivalence maps the symbols of one language to symbols of another bijectively. -/
structure LEquiv (L L' : MSLanguage Sorts) where
  /-- The forward language homomorphism -/
  toLHom : L →ᴸ L'
  /-- The inverse language homomorphism -/
  invLHom : L' →ᴸ L
  left_inv : invLHom.comp toLHom = LHom.id L
  right_inv : toLHom.comp invLHom = LHom.id L'

@[inherit_doc] infixl:10 " ≃ᴸ " => LEquiv

namespace LEquiv

variable (L) in
/-- The identity equivalence from a first-order language to itself. -/
@[simps]
protected def refl : L ≃ᴸ L :=
  ⟨LHom.id L, LHom.id L, LHom.comp_id _, LHom.comp_id _⟩

instance : Inhabited (L ≃ᴸ L) :=
  ⟨LEquiv.refl L⟩

variable {L'' : MSLanguage Sorts} (e' : L' ≃ᴸ L'') (e : L ≃ᴸ L')

/-- The inverse of an equivalence of first-order languages. -/
@[simps]
protected def symm : L' ≃ᴸ L :=
  ⟨e.invLHom, e.toLHom, e.right_inv, e.left_inv⟩

/-- The composition of equivalences of first-order languages. -/
@[simps, trans]
protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
  ⟨e'.toLHom.comp e.toLHom, e.invLHom.comp e'.invLHom, by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e'.invLHom, e'.left_inv, LHom.id_comp, e.left_inv], by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e.toLHom, e.right_inv, LHom.id_comp, e'.right_inv]⟩

end LEquiv

section ConstantsOn

variable (α : Sorts → Type u')

/-- The type of functions for a Multisorted language consisting only of constant symbols. -/
@[simp]
def constantsOnFunc : (σ : List Sorts) → (t : Sorts) → Type u'
  | [], t => α t
  | _,  _ => PEmpty

/-- A language with constants indexed by a type. -/
@[simps]
def constantsOn : MSLanguage.{u', 0, z} Sorts := ⟨constantsOnFunc α, fun _ => Empty⟩

variable {α}

@[simp]
theorem constantsOn_constants : (constantsOn α).Constants = α :=
  rfl

instance isAlgebraic_constantsOn : IsAlgebraic (constantsOn α) := by
  unfold constantsOn
  infer_instance

instance isEmpty_functions_constantsOn_succ {σ : List Sorts} {s : Sorts} {t : Sorts} :
    IsEmpty ((constantsOn α).Functions (s :: σ) t) :=
  inferInstanceAs (IsEmpty PEmpty)

instance isRelational_constantsOn [_ie : ∀ t, IsEmpty (α t)] : IsRelational (constantsOn α) :=
  fun σ t => List.casesOn σ (_ie t) inferInstance


-- TODO: prove this
/-
theorem card_constantsOn : (constantsOn α).card = #(Σ s, (α s)) := by
  simp [card_eq_card_functions_add_card_relations, sum_nat_eq_add_sum_succ]
-/

/-- Gives a `constantsOn α` structure to a type by assigning each constant a value. -/
def constantsOn.structure (f : α →ₛ M) : (constantsOn α).MSStructure M where
  funMap := fun {σ} {t} c _ =>
    match σ, c with
    | [], c => (f t) c

variable {β : Sorts → Type v'}

/-- A map between index types induces a map between constant languages. -/
def LHom.constantsOnMap (f : α →ₛ β) : constantsOn α →ᴸ constantsOn β where
  onFunction := fun {σ} {t} c =>
    match σ, c with
    | [], c => (f t) c

-- todo: priority for notation ∘ₛ might be too strong, as the notation fβ ∘ₛ f = fα fails
theorem constantsOnMap_isExpansionOn {f : α →ₛ β} {fα : α →ₛ M} {fβ : β →ₛ M} (h : (fβ ∘ₛ f) = fα) :
    @LHom.IsExpansionOn Sorts _ _ (LHom.constantsOnMap f) M (constantsOn.structure fα)
      (constantsOn.structure fβ) := by
  letI := constantsOn.structure fα
  letI := constantsOn.structure fβ
  exact
    ⟨fun {σ} {t} => List.casesOn σ
    (fun F _x => (congr_fun (congr_fun h t) F :)) fun t σ F => isEmptyElim F,
    fun R => isEmptyElim R⟩

end ConstantsOn

section WithConstants

variable (L)

section

variable (α : Sorts → Type w')

/-- Extends a language with a constant for each element of a parameter set in `M`. -/
def withConstants : MSLanguage.{max u w', v} Sorts :=
  L.sum (constantsOn α)

@[inherit_doc MSFirstOrder.MSLanguage.withConstants]
scoped[MSFirstOrder] notation:95 L "[[" α "]]" => MSLanguage.withConstants L α

/- TODO: prove this
@[simp]
theorem card_withConstants :
    L[[α]].card = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} #(Σ s, α s) := by
  rw [withConstants, card_sum, card_constantsOn]
-/

/-- The language map adding constants. -/
@[simps!]
def lhomWithConstants : L →ᴸ L[[α]] :=
  LHom.sumInl

theorem lhomWithConstants_injective : (L.lhomWithConstants α).Injective :=
  LHom.sumInl_injective

variable {α} (s : Sorts)

/-- The constant symbol in a particular sort indexed by a particular element. -/
protected def con (a : α s) : L[[α]].Constants s :=
  Sum.inr a

variable {L} (α)

/-- Adds constants to a language map. -/
def LHom.addConstants {L' : MSLanguage Sorts} (φ : L →ᴸ L') : L[[α]] →ᴸ L'[[α]] :=
  φ.sumMap (LHom.id _)

/-- Structure from constants. -/
instance paramsStructure (A : (s : Sorts) → Set (α s)) :
    -- elaborate A so that lean coerces it to a map Sorts → Type w'
    (constantsOn (fun s => A s : Sorts → Type w')).MSStructure α :=
  -- again, Lean does the coercions for us, at the cost of some elaboration
  constantsOn.structure (fun _ => fun a => a)

variable (L)

/-- The language map removing an empty constant set. -/
@[simps]
def LEquiv.addEmptyConstants [ie : ∀ s, IsEmpty (α s)] : L ≃ᴸ L[[α]] where
  toLHom := lhomWithConstants L α
  invLHom := LHom.sumElim (LHom.id L) (LHom.ofIsEmpty (constantsOn α) L)
  left_inv := by rw [lhomWithConstants, LHom.sumElim_comp_inl]
  right_inv := by
    simp only [LHom.comp_sumElim, lhomWithConstants, LHom.comp_id]
    exact _root_.trans (congr rfl (Subsingleton.elim _ _)) LHom.sumElim_inl_inr

variable {α} {β : Sorts → Type*}

@[simp]
theorem withConstants_funMap_sumInl [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
    {σ} {t} {f : L.Functions σ t} {x : SortedTuple σ M} :
    @funMap _ (L[[α]]) M _ σ t (Sum.inl f) x = funMap f x :=
  (lhomWithConstants L α).map_onFunction f x


@[simp]
theorem withConstants_relMap_sumInl [L[[α]].MSStructure M] [(lhomWithConstants L α).IsExpansionOn M]
    {σ} {R : L.Relations σ} {x : SortedTuple σ M} :
    @RelMap _ (L[[α]]) M _ σ (Sum.inl R) x = RelMap R x :=
  (lhomWithConstants L α).map_onRelation R x

/-- The language map extending the constant set. -/
def lhomWithConstantsMap (f : famMap α β) : L[[α]] →ᴸ L[[β]] :=
  LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)

@[simp]
theorem LHom.map_constants_comp_sumInl {f : famMap α β} :
    (L.lhomWithConstantsMap f).comp LHom.sumInl = L.lhomWithConstants β := by ext <;> rfl
end

open MSFirstOrder

instance constantsOnSelfStructure : (constantsOn M).MSStructure M :=
  constantsOn.structure (fun _ => id)

instance withConstantsSelfStructure : L[[M]].MSStructure M :=
  MSLanguage.sumStructure _ _ M

instance withConstants_self_expansion : (lhomWithConstants L M).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

variable (α : Sorts → Type*) [(constantsOn α).MSStructure M]

instance withConstantsStructure : L[[α]].MSStructure M :=
  MSLanguage.sumStructure _ _ _

instance withConstants_expansion : (L.lhomWithConstants α).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

instance addEmptyConstants_is_expansion_on' :
    (LEquiv.addEmptyConstants L (fun s => (∅ : Set (M s)))).toLHom.IsExpansionOn M :=
  L.withConstants_expansion _

instance addEmptyConstants_symm_isExpansionOn :
    (LEquiv.addEmptyConstants L (fun s => (∅ : Set (M s)))).symm.toLHom.IsExpansionOn M :=
  LHom.sumElim_isExpansionOn _ _ _

instance addConstants_expansion {L' : MSLanguage Sorts} [L'.MSStructure M] (φ : L →ᴸ L')
    [φ.IsExpansionOn M] : (φ.addConstants α).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ M

@[simp]
theorem withConstants_funMap_sumInr {s : Sorts} {a : α s} {x : SortedTuple [] M} :
    @funMap _ (L[[α]]) M _ _ _ (Sum.inr a : L[[α]].Functions [] s) x = L.con s a := by
  rw [Unique.eq_default x]
  exact (LHom.sumInr : constantsOn α →ᴸ L.sum _).map_onFunction _ _


variable {α} (A : (s : Sorts) → Set (M s))

@[simp]
theorem coe_con {s : Sorts} {a : A s} : (L.con (α := fun s => A s) s a : M s) = a :=
  rfl

variable {A} {B : (s : Sorts) → Set (M s)} (h : ∀ s, A s ⊆ B s)

instance constantsOnMap_inclusion_isExpansionOn :
    (LHom.constantsOnMap (fun s => Set.inclusion (h s))).IsExpansionOn M :=
  constantsOnMap_isExpansionOn rfl

instance map_constants_inclusion_isExpansionOn :
    (L.lhomWithConstantsMap (fun s => Set.inclusion (h s))).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ _

end WithConstants

end MSLanguage

end MSFirstOrder
