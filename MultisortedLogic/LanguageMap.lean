/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Semantics

/-!
# Maps of languages, sums of languages, and constants

## Main declarations

* `L.sum L'`: the disjoint union of the symbols of two languages. An `L`-structure and an
  `L'`-structure on the same carriers form an `L.sum L'`-structure (`sumStructure`).
* `LHom`, written `L →ᴸ L'`: a map sending symbols to symbols of the same arity. It translates
  terms, formulas and theories (`LHom.onTerm`, `LHom.onFormula`, `LHom.onTheory`), and these
  realize as before on structures where the map is an expansion (`LHom.IsExpansionOn`).
  Also `LHom.id`, `LHom.comp`, `LHom.sumInl`, `LHom.sumInr`, `LHom.sumMap`, the reduct of a
  structure along a map (`LHom.reduct`), and the default expansion along an injective map
  (`LHom.defaultExpansion`).
* `constantsOn α`: a constant of sort `t` for every `a : α t`. `L[[α]]` is `L.sum (constantsOn α)`,
  with the inclusion `lhomWithConstants` and the renaming `lhomWithConstantsMap`. A valuation
  `v : ∀ s, α s → M s` gives the `L[[α]]`-structure `withConstantsStructure v`, and every
  `L[[α]]`-structure is of this form (`withConstantsStructure_reduct`).

## References

This file was originally based on `Mathlib/ModelTheory/LanguageMap.lean`, by Aaron Anderson, Jesse
Michael Han and Floris van Doorn.
-/

@[expose] public section

universe u v u' v' w z u'' v'' u₁ v₁ u₂ v₂

namespace ManySorted.Language

open Arity Structure

variable {S : Type z}

/-! ### Sums of languages -/

/-- The disjoint union of the symbols of two languages. -/
protected abbrev sum (L : Language.{u, v} S) (L' : Language.{u', v'} S) :
    Language.{max u u', max v v'} S where
  Functions σ t := L.Functions σ t ⊕ L'.Functions σ t
  Relations σ := L.Relations σ ⊕ L'.Relations σ

variable {L : Language.{u, v} S} {L' : Language.{u', v'} S} {M : S → Type w}

/-- Two structures on the same carriers, one for each summand, form a structure for the sum. -/
instance sumStructure [L.Structure M] [L'.Structure M] : (L.sum L').Structure M where
  funMap f x := Sum.elim (fun f => funMap f x) (fun f => funMap f x) f
  RelMap R x := Sum.elim (fun R => RelMap R x) (fun R => RelMap R x) R

section sumStructure

variable [L.Structure M] [L'.Structure M]

@[simp]
theorem funMap_sumInl {σ : Arity S} {t : S} (f : L.Functions σ t) (x : M [^] σ) :
    funMap (L := L.sum L') (Sum.inl f) x = funMap f x := rfl

@[simp]
theorem funMap_sumInr {σ : Arity S} {t : S} (f : L'.Functions σ t) (x : M [^] σ) :
    funMap (L := L.sum L') (Sum.inr f) x = funMap f x := rfl

@[simp]
theorem relMap_sumInl {σ : Arity S} (R : L.Relations σ) (x : M [^] σ) :
    RelMap (L := L.sum L') (Sum.inl R) x ↔ RelMap R x := Iff.rfl

@[simp]
theorem relMap_sumInr {σ : Arity S} (R : L'.Relations σ) (x : M [^] σ) :
    RelMap (L := L.sum L') (Sum.inr R) x ↔ RelMap R x := Iff.rfl

end sumStructure

/-! ### Maps of languages -/

variable (L L') in
/-- A map of languages: function and relation symbols to symbols of the same arity. -/
structure LHom where
  /-- The image of a function symbol. -/
  onFunction : ∀ ⦃σ t⦄, L.Functions σ t → L'.Functions σ t
  /-- The image of a relation symbol. -/
  onRelation : ∀ ⦃σ⦄, L.Relations σ → L'.Relations σ

@[inherit_doc] scoped[ManySorted] infixl:10 " →ᴸ " => ManySorted.Language.LHom

namespace LHom

variable (φ : L →ᴸ L')

/-- Translate a tuple of terms along a map of languages. -/
def onTerm {Γ : Arity S} : ∀ {σ}, L.Term Γ σ → L'.Term Γ σ
  | _, .var i => .var i
  | _, .func f ts => .func (φ.onFunction f) (onTerm ts)
  | _, .nil => .nil
  | _, .prod t₁ t₂ => .prod (onTerm t₁) (onTerm t₂)

/-- Translate a formula along a map of languages. -/
def onFormula : ∀ {σ}, L.Formula σ → L'.Formula σ
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (φ.onTerm t₁) (φ.onTerm t₂)
  | _, .rel R ts => .rel (φ.onRelation R) (φ.onTerm ts)
  | _, .imp φ₁ φ₂ => .imp (onFormula φ₁) (onFormula φ₂)
  | _, .all τ φ₁ => .all τ (onFormula φ₁)

/-- Translate a theory along a map of languages. -/
def onTheory (T : L.Theory) : L'.Theory :=
  φ.onFormula '' T

theorem mem_onTheory {T : L.Theory} {ψ : L'.Sentence} :
    ψ ∈ φ.onTheory T ↔ ∃ θ ∈ T, φ.onFormula θ = ψ :=
  Iff.rfl

variable (M) in
/-- `φ` is an expansion on `M`: the `L'`-structure interprets the image of each symbol of `L` as
the `L`-structure interprets the symbol. -/
class IsExpansionOn [L.Structure M] [L'.Structure M] : Prop where
  map_onFunction : ∀ {σ t} (f : L.Functions σ t) (x : M [^] σ),
    funMap (φ.onFunction f) x = funMap f x
  map_onRelation : ∀ {σ} (R : L.Relations σ) (x : M [^] σ),
    RelMap (φ.onRelation R) x ↔ RelMap R x

section expansion

variable [L.Structure M] [L'.Structure M] [φ.IsExpansionOn M]

@[simp]
theorem realize_onTerm {Γ : Arity S} (xs : M [^] Γ) :
    ∀ {σ} (t : L.Term Γ σ), (φ.onTerm t).realize xs = t.realize xs
  | _, .var _ => rfl
  | _, .func f ts => by
    simp only [onTerm, Term.realize_func, realize_onTerm xs ts, IsExpansionOn.map_onFunction]
  | _, .nil => rfl
  | _, .prod t₁ t₂ => by
    simp only [onTerm, Term.realize_prod, realize_onTerm xs t₁, realize_onTerm xs t₂]

@[simp]
theorem realize_onFormula : ∀ {σ} (ψ : L.Formula σ) (xs : M [^] σ),
    (φ.onFormula ψ).Realize xs ↔ ψ.Realize xs
  | _, .falsum, _ => Iff.rfl
  | _, .equal _ _, _ => by simp only [onFormula, Formula.realize_equal, realize_onTerm]
  | _, .rel _ _, _ => by
    simp only [onFormula, Formula.realize_rel, realize_onTerm, IsExpansionOn.map_onRelation]
  | _, .imp ψ₁ ψ₂, xs => by
    simp only [onFormula, Formula.realize_imp, realize_onFormula ψ₁ xs, realize_onFormula ψ₂ xs]
  | _, .all _ ψ, _ => by simp only [onFormula, Formula.realize_all, realize_onFormula ψ]

@[simp]
theorem onTheory_model (T : L.Theory) : M ⊨ φ.onTheory T ↔ M ⊨ T := by
  simp only [Theory.model_iff, onTheory, Set.forall_mem_image, Sentence.realize_def,
    realize_onFormula]

end expansion

variable (M) in
/-- The reduct of an `L'`-structure to `L` along `φ`. -/
@[instance_reducible]
def reduct [L'.Structure M] : L.Structure M where
  funMap f x := funMap (φ.onFunction f) x
  RelMap R x := RelMap (φ.onRelation R) x

/-- A map of languages is an expansion on the reduct along it. -/
theorem isExpansionOn_reduct [L'.Structure M] :
    @IsExpansionOn _ _ _ M φ (φ.reduct M) _ :=
  @IsExpansionOn.mk _ _ _ M φ (φ.reduct M) _ (fun _ _ => rfl) (fun _ _ => Iff.rfl)

variable (L L') in
/-- The inclusion of the left summand. -/
@[simps]
protected def sumInl : L →ᴸ L.sum L' := ⟨fun _ _ => Sum.inl, fun _ => Sum.inl⟩

variable (L L') in
/-- The inclusion of the right summand. -/
@[simps]
protected def sumInr : L' →ᴸ L.sum L' := ⟨fun _ _ => Sum.inr, fun _ => Sum.inr⟩

instance [L.Structure M] [L'.Structure M] : (LHom.sumInl L L').IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩

instance [L.Structure M] [L'.Structure M] : (LHom.sumInr L L').IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩

end LHom

/-- An `L.sum L'`-structure is the sum of its two reducts. -/
theorem sumStructure_reduct (inst : (L.sum L').Structure M) :
    @sumStructure _ L L' M ((LHom.sumInl L L').reduct M) ((LHom.sumInr L L').reduct M) = inst := by
  rcases inst with ⟨F, R⟩
  simp only [sumStructure]
  congr
  · funext σ t f x
    rcases f with f | f <;> rfl
  · funext σ R x
    rcases R with R | R <;> rfl

/-! ### Constants -/

/-- Constant symbols of sort `t` for the names `α`: function symbols `⦃⦄ → t`. The sort `t` is a
parameter, not an index, so that it does not raise the universe. -/
inductive ConstantSymbol (α : S → Type u'') (t : S) : Arity S → Type u''
  | mk (a : α t) : ConstantSymbol α t ⦃⦄

/-- The name a constant symbol stands for. -/
def ConstantSymbol.name {α : S → Type u''} {t : S} : ∀ {σ}, ConstantSymbol α t σ → α t
  | _, .mk a => a

variable (α : S → Type u'')

/-- The language with a constant of sort `t` for every `a : α t`, and no relation symbols.

A definition rather than an `abbrev`: unfolding it in `simp`'s index made the `simp` lemmas about
`Sum.inl` symbols of `L[[α]]`, such as `funMap_sumInl`, never apply. -/
def constantsOn : Language.{u'', 0} S where
  Functions σ t := ConstantSymbol α t σ
  Relations _ := Empty

variable {α}

/-- Interpret the constants by a valuation of the names. -/
@[instance_reducible]
def constantsOnStructure (v : ∀ s, α s → M s) : (constantsOn α).Structure M where
  funMap c _ := v _ (ConstantSymbol.name c)
  RelMap R _ := nomatch R

variable (L α) in
/-- The expansion of `L` by a constant of sort `t` for every `a : α t`. -/
abbrev withConstants : Language.{max u u'', v} S := L.sum (constantsOn α)

@[inherit_doc] scoped[ManySorted] notation:max L "[[" α "]]" =>
  ManySorted.Language.withConstants L α

/-- Interpret the constants of `L[[α]]` by a valuation of the names.

Not an instance, since `v` is data. `simp` sees through it with `funMap_sumInl`,
`relMap_sumInl` and `funMap_con`. -/
@[instance_reducible]
def withConstantsStructure [L.Structure M] (v : ∀ s, α s → M s) : L[[α]].Structure M :=
  @sumStructure _ L (constantsOn α) M _ (constantsOnStructure v)

/-- The valuation of the names read off an `L[[α]]`-structure. -/
def constants [L[[α]].Structure M] : ∀ s, α s → M s :=
  fun _ a => funMap (L := L[[α]]) (Sum.inr (.mk a)) PUnit.unit

/-- The constants of an `L[[α]]`-structure interpret `constantsOn α` as its right reduct. -/
theorem constantsOnStructure_constants (inst : L[[α]].Structure M) :
    constantsOnStructure (constants (L := L)) = (LHom.sumInr L (constantsOn α)).reduct M := by
  unfold constantsOnStructure LHom.reduct
  congr 1
  · funext σ t c x
    cases c
    rfl
  · funext σ R x
    exact nomatch R

/-- An `L[[α]]`-structure is its `L`-reduct with its constants. -/
theorem withConstantsStructure_reduct (inst : L[[α]].Structure M) :
    @withConstantsStructure _ L M α ((LHom.sumInl L (constantsOn α)).reduct M)
      (constants (L := L)) = inst := by
  unfold withConstantsStructure
  rw [constantsOnStructure_constants]
  exact sumStructure_reduct inst

/-! ### Identity, composition and sums of maps of languages -/

namespace LHom

variable {L'' : Language.{u₁, v₁} S}

/-- Two maps of languages are equal when they agree on the function and on the relation
symbols. -/
@[ext]
protected theorem funext {F G : L →ᴸ L'} (h_fun : F.onFunction = G.onFunction)
    (h_rel : F.onRelation = G.onRelation) : F = G := by
  cases F
  cases G
  congr

variable (L) in
/-- The identity map of a language. -/
@[simps]
protected def id : L →ᴸ L :=
  ⟨fun _ _ f => f, fun _ R => R⟩

instance : Inhabited (L →ᴸ L) :=
  ⟨LHom.id L⟩

/-- The composition of maps of languages. -/
@[simps]
def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
  ⟨fun _ _ c => g.onFunction (f.onFunction c), fun _ R => g.onRelation (f.onRelation R)⟩

@[inherit_doc]
local infixl:60 " ∘ᴸ " => LHom.comp

@[simp]
theorem id_comp (F : L →ᴸ L') : LHom.id L' ∘ᴸ F = F :=
  rfl

@[simp]
theorem comp_id (F : L →ᴸ L') : F ∘ᴸ LHom.id L = F :=
  rfl

theorem comp_assoc {L₃ : Language.{u₂, v₂} S} (F : L'' →ᴸ L₃) (G : L' →ᴸ L'') (H : L →ᴸ L') :
    F ∘ᴸ G ∘ᴸ H = F ∘ᴸ (G ∘ᴸ H) :=
  rfl

section SumElim

variable (φ : L →ᴸ L') (ψ : L'' →ᴸ L')

/-- The map from a sum of languages that is `φ` on the left summand and `ψ` on the right one. -/
@[simps]
protected def sumElim : L.sum L'' →ᴸ L' where
  onFunction _ _ := Sum.elim (fun f => φ.onFunction f) fun f => ψ.onFunction f
  onRelation _ := Sum.elim (fun R => φ.onRelation R) fun R => ψ.onRelation R

theorem sumElim_comp_inl : φ.sumElim ψ ∘ᴸ LHom.sumInl L L'' = φ :=
  rfl

theorem sumElim_comp_inr : φ.sumElim ψ ∘ᴸ LHom.sumInr L L'' = ψ :=
  rfl

theorem comp_sumElim {L₃ : Language.{u₂, v₂} S} (θ : L' →ᴸ L₃) :
    θ ∘ᴸ φ.sumElim ψ = (θ ∘ᴸ φ).sumElim (θ ∘ᴸ ψ) :=
  LHom.funext (funext₂ fun _ _ => Sum.comp_elim _ _ _) (funext fun _ => Sum.comp_elim _ _ _)

end SumElim

theorem sumElim_inl_inr : (LHom.sumInl L L').sumElim (LHom.sumInr L L') = LHom.id (L.sum L') :=
  LHom.funext (funext₂ fun _ _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)

section SumMap

variable {L₁ : Language.{u₁, v₁} S} {L₂ : Language.{u₂, v₂} S} (φ : L →ᴸ L₁) (ψ : L' →ᴸ L₂)

/-- The map of sums of languages that is `φ` on the left summand and `ψ` on the right one. -/
@[simps]
def sumMap : L.sum L' →ᴸ L₁.sum L₂ where
  onFunction _ _ := Sum.map (fun f => φ.onFunction f) fun f => ψ.onFunction f
  onRelation _ := Sum.map (fun R => φ.onRelation R) fun R => ψ.onRelation R

@[simp]
theorem sumMap_comp_inl : φ.sumMap ψ ∘ᴸ LHom.sumInl L L' = LHom.sumInl L₁ L₂ ∘ᴸ φ :=
  rfl

@[simp]
theorem sumMap_comp_inr : φ.sumMap ψ ∘ᴸ LHom.sumInr L L' = LHom.sumInr L₁ L₂ ∘ᴸ ψ :=
  rfl

end SumMap

/-- A map of languages is injective when it is injective on the function and on the relation
symbols. -/
protected structure Injective (φ : L →ᴸ L') : Prop where
  onFunction {σ : Arity S} {t : S} : Function.Injective fun f : L.Functions σ t => φ.onFunction f
  onRelation {σ : Arity S} : Function.Injective fun R : L.Relations σ => φ.onRelation R

theorem sumInl_injective : (LHom.sumInl L L').Injective :=
  ⟨fun h => Sum.inl_injective h, fun h => Sum.inl_injective h⟩

theorem sumInr_injective : (LHom.sumInr L L').Injective :=
  ⟨fun h => Sum.inr_injective h, fun h => Sum.inr_injective h⟩

/-! ### Expansions -/

section expansion

variable (φ : L →ᴸ L') [L.Structure M] [L'.Structure M]

@[simp]
theorem map_onFunction [φ.IsExpansionOn M] {σ : Arity S} {t : S} (f : L.Functions σ t)
    (x : M [^] σ) : funMap (φ.onFunction f) x = funMap f x :=
  IsExpansionOn.map_onFunction f x

@[simp]
theorem map_onRelation [φ.IsExpansionOn M] {σ : Arity S} (R : L.Relations σ) (x : M [^] σ) :
    RelMap (φ.onRelation R) x ↔ RelMap R x :=
  IsExpansionOn.map_onRelation R x

omit [L'.Structure M] in
instance id_isExpansionOn : (LHom.id L).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩

instance sumElim_isExpansionOn (ψ : L'' →ᴸ L') [L''.Structure M] [φ.IsExpansionOn M]
    [ψ.IsExpansionOn M] : (φ.sumElim ψ).IsExpansionOn M :=
  ⟨fun f x => by rcases f with f | f; exacts [φ.map_onFunction f x, ψ.map_onFunction f x],
    fun R x => by rcases R with R | R; exacts [φ.map_onRelation R x, ψ.map_onRelation R x]⟩

instance sumMap_isExpansionOn {L₁ : Language.{u₁, v₁} S} {L₂ : Language.{u₂, v₂} S}
    (ψ : L₁ →ᴸ L₂) [L₁.Structure M] [L₂.Structure M] [φ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (φ.sumMap ψ).IsExpansionOn M :=
  ⟨fun f x => by rcases f with f | f; exacts [φ.map_onFunction f x, ψ.map_onFunction f x],
    fun R x => by rcases R with R | R; exacts [φ.map_onRelation R x, ψ.map_onRelation R x]⟩

end expansion

/-! ### Default expansions -/

section defaultExpansion

variable (φ : L →ᴸ L')
  [∀ (σ t) (f : L'.Functions σ t),
    Decidable (f ∈ Set.range fun f : L.Functions σ t => φ.onFunction f)]
  [∀ (σ) (R : L'.Relations σ), Decidable (R ∈ Set.range fun R : L.Relations σ => φ.onRelation R)]

variable (M) in
/-- An `L`-structure expanded along `φ` to an `L'`-structure: a symbol in the image of `φ` is
interpreted as one of its preimages, and the other symbols by default values and `False`. -/
@[instance_reducible]
noncomputable def defaultExpansion [∀ s, Inhabited (M s)] [L.Structure M] : L'.Structure M where
  funMap {σ t} f x :=
    if h : f ∈ Set.range fun f : L.Functions σ t => φ.onFunction f then funMap h.choose x
    else default
  RelMap {σ} R x :=
    if h : R ∈ Set.range fun R : L.Relations σ => φ.onRelation R then RelMap h.choose x
    else False

variable {φ} in
/-- An injective map of languages is an expansion on the default expansion along it. -/
theorem Injective.isExpansionOn_default (h : φ.Injective) (M : S → Type w)
    [∀ s, Inhabited (M s)] [L.Structure M] :
    @IsExpansionOn _ _ _ M φ _ (φ.defaultExpansion M) := by
  let := φ.defaultExpansion M
  refine ⟨fun {σ t} f x => ?_, fun {σ} R x => ?_⟩
  · have hf : φ.onFunction f ∈ Set.range fun f : L.Functions σ t => φ.onFunction f := ⟨f, rfl⟩
    refine (dite_eq_left hf).trans ?_
    rw [h.onFunction hf.choose_spec]
  · have hR : φ.onRelation R ∈ Set.range fun R : L.Relations σ => φ.onRelation R := ⟨R, rfl⟩
    refine Iff.of_eq ((dite_eq_left hR).trans ?_)
    rw [h.onRelation hR.choose_spec]

end defaultExpansion

/-! ### Identity and composition on terms and formulas -/

@[simp]
theorem id_onTerm {Γ : Arity S} : ∀ {σ} (t : L.Term Γ σ), (LHom.id L).onTerm t = t
  | _, .var _ => rfl
  | _, .func _ ts => congrArg (Term.func _) (id_onTerm ts)
  | _, .nil => rfl
  | _, .prod t₁ t₂ => congrArg₂ Term.prod (id_onTerm t₁) (id_onTerm t₂)

@[simp]
theorem comp_onTerm (g : L' →ᴸ L'') (f : L →ᴸ L') {Γ : Arity S} :
    ∀ {σ} (t : L.Term Γ σ), (g ∘ᴸ f).onTerm t = g.onTerm (f.onTerm t)
  | _, .var _ => rfl
  | _, .func _ ts => congrArg (Term.func _) (comp_onTerm g f ts)
  | _, .nil => rfl
  | _, .prod t₁ t₂ => congrArg₂ Term.prod (comp_onTerm g f t₁) (comp_onTerm g f t₂)

@[simp]
theorem id_onFormula : ∀ {σ} (ψ : L.Formula σ), (LHom.id L).onFormula ψ = ψ
  | _, .falsum => rfl
  | _, .equal t₁ t₂ => congrArg₂ Formula.equal (id_onTerm t₁) (id_onTerm t₂)
  | _, .rel R ts => congrArg (Formula.rel R) (id_onTerm ts)
  | _, .imp ψ₁ ψ₂ => congrArg₂ Formula.imp (id_onFormula ψ₁) (id_onFormula ψ₂)
  | _, .all τ ψ => congrArg (Formula.all τ) (id_onFormula ψ)

@[simp]
theorem comp_onFormula (g : L' →ᴸ L'') (f : L →ᴸ L') :
    ∀ {σ} (ψ : L.Formula σ), (g ∘ᴸ f).onFormula ψ = g.onFormula (f.onFormula ψ)
  | _, .falsum => rfl
  | _, .equal t₁ t₂ => congrArg₂ Formula.equal (comp_onTerm g f t₁) (comp_onTerm g f t₂)
  | _, .rel _ ts => congrArg (Formula.rel _) (comp_onTerm g f ts)
  | _, .imp ψ₁ ψ₂ => congrArg₂ Formula.imp (comp_onFormula g f ψ₁) (comp_onFormula g f ψ₂)
  | _, .all τ ψ => congrArg (Formula.all τ) (comp_onFormula g f ψ)

/-! ### Relabelling -/

theorem onTerm_relabel (φ : L →ᴸ L') {Γ Γ' : Arity S} (g : ∀ s, Γ.Idx s → Γ'.Idx s) :
    ∀ {σ} (t : L.Term Γ σ), φ.onTerm (t.relabel g) = (φ.onTerm t).relabel g
  | _, .var _ => rfl
  | _, .func _ ts => congrArg (Term.func _) (onTerm_relabel φ g ts)
  | _, .nil => rfl
  | _, .prod t₁ t₂ => congrArg₂ Term.prod (onTerm_relabel φ g t₁) (onTerm_relabel φ g t₂)

theorem onFormula_relabel (φ : L →ᴸ L') :
    ∀ {σ τ : Arity S} (g : ∀ s, σ.Idx s → τ.Idx s) (ψ : L.Formula σ),
      φ.onFormula (ψ.relabel g) = (φ.onFormula ψ).relabel g
  | _, _, _, .falsum => rfl
  | _, _, g, .equal t₁ t₂ =>
    congrArg₂ Formula.equal (φ.onTerm_relabel g t₁) (φ.onTerm_relabel g t₂)
  | _, _, g, .rel _ ts => congrArg (Formula.rel _) (φ.onTerm_relabel g ts)
  | _, _, g, .imp ψ₁ ψ₂ =>
    congrArg₂ Formula.imp (onFormula_relabel φ g ψ₁) (onFormula_relabel φ g ψ₂)
  | _, _, _, .all τ ψ => congrArg (Formula.all τ) (onFormula_relabel φ _ ψ)

end LHom

/-! ### Equivalences of languages -/

variable (L L') in
/-- An equivalence of languages: maps of languages in both directions that are inverse to each
other. -/
structure LEquiv where
  /-- The map from `L` to `L'`. -/
  toLHom : L →ᴸ L'
  /-- The map from `L'` to `L`. -/
  invLHom : L' →ᴸ L
  left_inv : invLHom.comp toLHom = LHom.id L
  right_inv : toLHom.comp invLHom = LHom.id L'

@[inherit_doc] scoped[ManySorted] infixl:10 " ≃ᴸ " => ManySorted.Language.LEquiv

namespace LEquiv

variable (L) in
/-- The identity equivalence of a language. -/
@[simps]
protected def refl : L ≃ᴸ L :=
  ⟨LHom.id L, LHom.id L, rfl, rfl⟩

instance : Inhabited (L ≃ᴸ L) :=
  ⟨LEquiv.refl L⟩

variable {L'' : Language.{u₁, v₁} S}

/-- The inverse of an equivalence of languages. -/
@[simps]
protected def symm (e : L ≃ᴸ L') : L' ≃ᴸ L :=
  ⟨e.invLHom, e.toLHom, e.right_inv, e.left_inv⟩

/-- The composition of equivalences of languages. -/
@[simps]
protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
  ⟨e'.toLHom.comp e.toLHom, e.invLHom.comp e'.invLHom, by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e'.invLHom, e'.left_inv, LHom.id_comp, e.left_inv], by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e.toLHom, e.right_inv, LHom.id_comp, e'.right_inv]⟩

/-- The bijection of tuples of terms given by an equivalence of languages. -/
@[simps]
def onTerm (e : L ≃ᴸ L') {Γ σ : Arity S} : L.Term Γ σ ≃ L'.Term Γ σ where
  toFun := e.toLHom.onTerm
  invFun := e.invLHom.onTerm
  left_inv t := by rw [← LHom.comp_onTerm, e.left_inv, LHom.id_onTerm]
  right_inv t := by rw [← LHom.comp_onTerm, e.right_inv, LHom.id_onTerm]

/-- The bijection of formulas given by an equivalence of languages. -/
@[simps]
def onFormula (e : L ≃ᴸ L') {σ : Arity S} : L.Formula σ ≃ L'.Formula σ where
  toFun := e.toLHom.onFormula
  invFun := e.invLHom.onFormula
  left_inv ψ := by rw [← LHom.comp_onFormula, e.left_inv, LHom.id_onFormula]
  right_inv ψ := by rw [← LHom.comp_onFormula, e.right_inv, LHom.id_onFormula]

end LEquiv

/-! ### Renaming constants -/

variable {α : S → Type u''} {β : S → Type v''}

/-- Rename the name a constant symbol stands for. -/
def ConstantSymbol.map (g : ∀ s, α s → β s) {t : S} :
    ∀ {σ : Arity S}, ConstantSymbol α t σ → ConstantSymbol β t σ
  | _, .mk a => .mk (g t a)

/-- Rename the constants of `constantsOn α`. -/
def LHom.constantsOnMap (g : ∀ s, α s → β s) : constantsOn α →ᴸ constantsOn β :=
  ⟨fun _ _ c => ConstantSymbol.map g c, fun _ R => nomatch R⟩

variable (L α) in
/-- The inclusion of `L` in `L[[α]]`. -/
abbrev lhomWithConstants : L →ᴸ L[[α]] :=
  LHom.sumInl L (constantsOn α)

variable (L) in
/-- Rename the constants of `L[[α]]`. -/
def lhomWithConstantsMap (g : ∀ s, α s → β s) : L[[α]] →ᴸ L[[β]] :=
  (LHom.id L).sumMap (LHom.constantsOnMap g)

/-- Renaming the constants is an expansion from the structure given by `v ∘ g` to the one given by
`v`. -/
theorem isExpansionOn_lhomWithConstantsMap [L.Structure M] (g : ∀ s, α s → β s)
    (v : ∀ s, β s → M s) :
    @LHom.IsExpansionOn _ _ _ M (L.lhomWithConstantsMap g)
      (withConstantsStructure fun s => v s ∘ g s) (withConstantsStructure v) :=
  @LHom.IsExpansionOn.mk _ _ _ M (L.lhomWithConstantsMap g)
    (withConstantsStructure fun s => v s ∘ g s) (withConstantsStructure v)
    (fun f _ => by rcases f with f | ⟨⟨a⟩⟩ <;> rfl)
    (fun R _ => by rcases R with R | R; exacts [Iff.rfl, nomatch R])

@[simp]
theorem LHom.map_constants_comp_sumInl (g : ∀ s, α s → β s) :
    (L.lhomWithConstantsMap g).comp (L.lhomWithConstants α) = L.lhomWithConstants β :=
  rfl

theorem lhomWithConstants_injective : (L.lhomWithConstants α).Injective :=
  LHom.sumInl_injective

/-- Add the constants for `α` to a map of languages. -/
def LHom.addConstants {L' : Language.{u', v'} S} (φ : L →ᴸ L') : L[[α]] →ᴸ L'[[α]] :=
  φ.sumMap (LHom.id _)

variable (L) in
/-- The constant symbol of `L[[α]]` for `a : α s`. -/
protected def con {s : S} (a : α s) : L[[α]].Constants s :=
  Sum.inr (.mk a)

@[simp]
theorem funMap_con [L.Structure M] (v : ∀ s, α s → M s) {s : S} (a : α s) (x : M [^] ⦃⦄) :
    @funMap _ L[[α]] M (withConstantsStructure v) _ _ (L.con a) x = v s a :=
  rfl

end ManySorted.Language
