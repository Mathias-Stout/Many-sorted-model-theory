import MultisortedLogic.LanguageMap

/-
Based on the corresponding Mathlib file Mathlib\ModelTheory\Syntax.lean
which was authored by 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn,
and is released under the Apache 2.0 license.

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/

universe u v w z u' v' w'

namespace MSFirstOrder

namespace MSLanguage

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
variable {M : Sorts → Type w} {α : Sorts → Type u'} {β : Sorts → Type v'} {γ : Sorts → Type*}

open MSFirstOrder MSStructure Fin Fam

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms.
  We cannot use SortedTuple here, as this this trows an error related to nested inductive datatypes.
  Insead, we use dependent maps here, and define appropriate coercions for SortedTuples.
  See also the remark about instDecidableEq_sorted_tuple.
-/

inductive Term (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') : Sorts → Type max z u' u
 | var t : (α t) → L.Term α t
 | func (σ : List (Sorts)) t : ∀ (_ : L.Functions σ t),
    ((i : Fin σ.length) → L.Term α (σ.get i)) → L.Term α t

/- compare this with the simpler definition of terms in the 1-sorted case
inductive Term (α : Type u') : Type max u u'
  | var : α → Term α
  | func : ∀ {l : ℕ} (_f : L.Functions l) (_ts : Fin l → Term α), Term α-/
namespace Term

/-- DecidableEq for SortedTuples as dependent maps
  see also the remark at the definition of Terms. -/
def instDecidableEq_sorted_tuple {σ : List Sorts} {α : Sorts → Type w}
  [hyp : ∀ i : Fin σ.length, DecidableEq (α (σ.get i))] :
  DecidableEq ((i : Fin σ.length) → α (σ.get i)) :=
  inferInstance

--TODO: improve this proof
instance instDecidableEq
  [DecidableEq Sorts]
  [∀ σ : List Sorts, ∀ i: Fin σ.length, DecidableEq (α (σ.get i))]
  [∀ s, DecidableEq (α s)]
  [∀ σ t, DecidableEq (L.Functions σ t)] :
  ∀ t, DecidableEq (L.Term α t) := by
  intro t t₁ t₂
  cases t₁ with
  | var _ a₁ =>
    cases t₂ with
    | var _ a₂ =>
      match decEq a₁ a₂ with
      | isTrue h  => exact isTrue (by rw [h])
      | isFalse h => exact isFalse (by intro eqv; cases eqv; contradiction)
    | func _ =>
      exact isFalse (by intro h; cases h)
  | func σ₁ _ f₁ args₁ =>
    cases t₂ with
    | var _ =>
      exact isFalse (by intro h; cases h)
    | func σ₂ _ f₂ args₂ =>
      match decEq σ₁ σ₂ with
      | isFalse hσ =>
        exact isFalse (by intro h; cases h; contradiction)
      | isTrue hσ =>
        subst hσ
        match decEq f₁ f₂ with
        | isFalse hf =>
          exact isFalse (by intro h; cases h; contradiction)
        | isTrue hf =>
          letI : DecidableEq ((i : Fin σ₁.length) → (L.Term α (σ₁.get i))):=
            instDecidableEq_sorted_tuple (hyp := fun i => instDecidableEq (σ₁[i]))
          letI : ∀ (i : Fin (σ₁.length)), Decidable (args₁ i = args₂ i) := by
            intro i
            apply instDecidableEq
          exact decidable_of_iff (∀ i : Fin (σ₁.length), args₁ i = args₂ i) <| by
            simp[funext_iff, hf]

open Finset

/-- The `Finset` of variables used in a given term (now multi-sorted). -/
@[simp]
def varFinset {t : Sorts} {α : Sorts → Type u'}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : L.Term α t → Finset (Σ t, α t)
  | var t i => {⟨_,i⟩}
  | func _ _ _ ts => univ.biUnion fun i => (ts i).varFinset

/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeft {t : Sorts} [DecidableEq Sorts] [∀ t, DecidableEq (α t)] :
    L.Term (α ⊕ₛ β ) t → Finset (Σ t, α t)
  | var _ (Sum.inl i) => {⟨_,i⟩}
  | var _ (Sum.inr _i) => ∅
  | func _ _ _ ts => univ.biUnion fun i => (ts i).varFinsetLeft

/-- Relabels a term's variables along a particular function -/
@[simp]
def relabel {t : Sorts} (g : α →ₛ β) : L.Term α t → L.Term β t
  | var t a => var t (g t a)
  | func σ t f ts => func σ t f fun i => relabel g (ts i)

variable {t : Sorts}

@[simp]
theorem relabel_id {f : L.Term α t} : relabel (Fam.id α) f = f := by
  induction f with
  | var => rfl
  | func _ _ _ _ ih => simp [ih]

@[simp]
theorem relabel_id_eq_id : (relabel (Fam.id α) : L.Term α t → L.Term α t) = id :=
  funext (fun _ => relabel_id)

@[simp]
theorem relabel_id_eq_id' : (relabel (fun s => @id (α s)) : L.Term α t → L.Term α t) = id :=
  funext (fun _ => relabel_id)

@[simp]
theorem relabel_relabel (f : α →ₛ β) (g : β →ₛ γ) (t : L.Term α t) :
    relabel g (relabel  f t)= relabel (g ∘ₛ f) t:= by
  induction t with
  | var => rfl
  | func _ _ _ _ ih => simp [ih]

@[simp]
theorem relabel_comp_relabel (f : α →ₛ β) (g : famMap β γ) :
    (relabel g ∘ relabel f : L.Term α t → L.Term γ t) = Term.relabel (g ∘ₛ f) :=
  funext (relabel_relabel f g)

/-- Relabels a term's variables along a bijection. -/
@[simps]
def relabelEquiv (g : ∀ s, α s ≃ β s) {t : Sorts} : L.Term α t ≃ L.Term β t :=
  ⟨relabel (fun s => g s), relabel (fun s => (g s).symm), fun _ => by simp, fun _ => by simp⟩

/-- Restricts a term to use only a set of the given variables. -/
@[simp]
def restrictVar
  [DecidableEq Sorts]
  [∀ t, DecidableEq (α t)]
  : ∀ {t : Sorts} (f : L.Term α t)
      (_ : ∀ {s}, {x : (Σ t, α t) // x ∈ varFinset f ∧ x.fst = s} → β s),
      L.Term β t
| _, var t a, g =>
    let x : {x : Σ t, α t // x ∈ (varFinset (var t a))∧ x.fst = t} :=
      { val := ⟨t, a⟩,
        property := by simp [varFinset] }
    var t (@g t x)
| _, func σ out ar ts, g =>
    func σ out ar (fun i =>
      restrictVar (ts i)
        (fun {s} ⟨x, h⟩=>
          (@g s ⟨ x, by
          -- TODO: remove non-terminal simp statement
            simp only [varFinset, List.get_eq_getElem, mem_biUnion, mem_univ, true_and]
            constructor
            ·use i, h.1
            ·exact h.2
          ⟩)))

/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrictVarLeft [DecidableEq Sorts] {γ : Sorts → Type*}
  [∀ t, DecidableEq (α t)]
  : ∀ {t : Sorts} (f : L.Term (α ⊕ₛ γ) t)
      (_f : ∀ {s}, {x : (Σ t, α t) // x ∈ (varFinsetLeft f : Set _) ∧ x.fst = s} → β s),
    L.Term (β ⊕ₛ γ) t
| _, var t (Sum.inl a), g =>
  -- build the subtype value: element is ⟨t, a⟩, membership is mem_singleton_self (⟨t,a⟩),
  -- and fst = t is rfl
  var t (Sum.inl (g ⟨⟨t, a⟩, ⟨mem_singleton_self (⟨t, a⟩ : Σ t, α t), rfl⟩⟩))
| _, var t (Sum.inr a), _f => var t (Sum.inr a)
| _, func F σ t ts, g =>
  func F σ t fun i =>
    (ts i).restrictVarLeft
      (g ∘ Set.inclusion (fun _ hx =>
        -- hx : x ∈ ↑(varFinsetLeft L (ts i)) ∧ x.fst = s
        -- use subset_biUnion_of_mem on hx.1 to get membership in the bigger biUnion,
        -- and keep hx.2 (the fst = s) unchanged
        ⟨ subset_biUnion_of_mem (fun j => varFinsetLeft (ts j)) (mem_univ i) hx.1,
          hx.2 ⟩))

end Term

variable {s₁ s₂ : Sorts} {t : Sorts}
open Term

/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants t) : L.Term α t :=
  func _ t c (default : SortedTuple [] _).toMap

/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions [s₁] t) (g : L.Term α s₁) : L.Term α t :=
  func _ t f (!ₛ[⟨s₁,g⟩]).toMap

/-- Applies a binary function to two terms. -/
def Functions.apply₂ (f : L.Functions [s₁, s₂] t) (g₁ : L.Term α s₁) (g₂ : L.Term α s₂) :
    L.Term α t := func _ t f (!ₛ[⟨s₁,g₁⟩,⟨s₂,g₂⟩]).toMap


/- The representation of a function symbol as a term, on fresh variables indexed by Fin. -/
def Functions.term {σ : List Sorts} {t : Sorts} (f : L.Functions σ t) : L.Term σ.toFam t :=
  func σ t f (fun i => var σ[i] ⟨i,rfl⟩)

namespace Term

/-- Sends a term with constants to a term with extra variables. -/
@[simp]
def constantsToVars {t : Sorts} : L[[γ]].Term α t → L.Term (γ ⊕ₛ α) t
  | var t a => var t (Sum.inr a)
  | func [] t f ts =>
    Sum.casesOn f (fun f => func [] t f fun i => (ts i).constantsToVars) fun c => var t (Sum.inl c)
  | func (s :: σ) t f ts =>
    Sum.casesOn f
    (fun f => func (s :: σ) t f fun i => (ts i).constantsToVars)
    (fun c => isEmptyElim c)


/-- Sends a term with extra variables to a term with constants. -/
@[simp]
def varsToConstants {t : Sorts} : L.Term (γ ⊕ₛ α) t → L[[γ]].Term α t
  | var t (Sum.inr a : (γ ⊕ₛ α) t)  => var t a
  | var _t (Sum.inl a : (γ ⊕ₛ α) _t) => Constants.term (Sum.inr a)
  | func σ t f ts => func σ t (Sum.inl f) fun i => (ts i).varsToConstants

/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
def constantsVarsEquiv {t : Sorts} : L[[γ]].Term α t ≃ L.Term (γ ⊕ₛ α) t :=
  ⟨constantsToVars, varsToConstants, by
    intro g
    induction g with
    | var => rfl
    | func σ t f ts ih =>
      cases σ
      · cases f
        · simp [funext_iff]
        · simp [Constants.term,SortedTuple.default_toMap]
      · obtain - | f := f
        · simp [constantsToVars, varsToConstants, ih]
        · exact isEmptyElim f, by
    intro t
    induction t with
    | var t x => cases x <;> rfl
    | func σ t f a ih =>
      cases σ <;> simp [constantsToVars,varsToConstants,ih] ⟩

example (f g : Fin 0 → Type) : f = g := by exact List.ofFn_inj.mp rfl

/-- A bijection between terms with constants and terms with extra variables. -/
def constantsVarsEquivLeft {t : Sorts} : L[[γ]].Term (α ⊕ₛ β) t ≃ L.Term ((γ ⊕ₛ α) ⊕ₛ β ) t :=
  (constantsVarsEquiv).trans (relabelEquiv (fun _ => Equiv.sumAssoc _ _ _)).symm

@[simp]
theorem constantsVarsEquivLeft_apply (g : L[[γ]].Term (α ⊕ₛ β) t) :
    constantsVarsEquivLeft g =
    (constantsToVars g).relabel (fun _ => (Equiv.sumAssoc _ _ _).invFun) := rfl

@[simp]
theorem constantsVarsEquivLeft_symm_apply (g : L.Term ((γ ⊕ₛ α) ⊕ₛ β) t) :
    (constantsVarsEquivLeft).symm g = varsToConstants (g.relabel (fun _ => Equiv.sumAssoc _ _ _)) :=
  rfl

instance inhabitedOfVar [Inhabited (α t)] : Inhabited (L.Term α t) :=
  ⟨var t default⟩

instance inhabitedOfConstant [Inhabited (L.Constants t)] : Inhabited (L.Term α t) :=
  ⟨(default : L.Constants t).term⟩

/- TODO: state and prove a good analogue of the following onesorted definition
/-- Raises all of the `Fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def liftAt {n : ℕ} (n' m : ℕ) : L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin (n + n'))) :=
  relabel (Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')
-/
variable (l : List Sorts)
/-- Substitutes the variables in a given term with terms. -/
@[simp]
def subst {t : Sorts} : L.Term α t → (α →ₛ (L.Term β)) → L.Term β t
  | var t a, tf => tf t a
  | func σ t f ts, tf => func σ t f fun i => (ts i).subst tf
/-- Substitutes the functions in a given term with expressions. -/
-- Note: with current implementation, an annoying cast is required
@[simp]
def substFunc {t : Sorts} :
  L.Term α t →
  (∀ σ t, L.Functions σ t → L'.Term σ.toFam t) →
  L'.Term α t
  | var t a, _ => var t a
  | func σ t f ts, tf =>
      (tf σ t f).subst fun _s ⟨i, h⟩ =>
        h ▸ ((ts i).substFunc tf)
@[simp]
theorem substFunc_term (g : L.Term α t) : g.substFunc (@Functions.term _ _) = g := by
  induction g
  · rfl
  · simp only [substFunc, Functions.term, subst, ‹∀ _, _›]

end Term

def mkVar {α : Sorts → Type*} (σ : List Sorts) :
    (i : Fin (σ.length)) → Term L (α ⊕ₛ σ.toFam) σ[i] :=
  fun i => var σ[i] (Sum.inr ⟨i,by simp⟩)

/-- `σ&i` is notation for the `n`-th free variable,
  from the corresponding sort determined by a signature σ-/
scoped[MSFirstOrder] infix:arg "&" => MSLanguage.mkVar

namespace LHom

open Term

/-- Maps a term's symbols along a language map. -/
@[simp]
def onTerm {t : Sorts} (φ : L →ᴸ L') : L.Term α t → L'.Term α t
  | var t a => var t a
  | func σ t f ts => func σ t (φ.onFunction f) fun i => onTerm φ (ts i)

@[simp]
theorem id_onTerm : ((LHom.id L).onTerm : L.Term α t → L.Term α t) = id := by
  ext t
  induction t with
  | var => rfl
  | func _ _ _ _ ih => simp_rw [onTerm, ih]; rfl

@[simp]
theorem comp_onTerm {L'' : MSLanguage Sorts} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α t → L''.Term α t) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction t with
  | var => rfl
  | func _ _ _ _ ih => simp_rw [onTerm, ih]; rfl

end LHom

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
def LEquiv.onTerm (φ : L ≃ᴸ L') : L.Term α t ≃ L'.Term α t where
  toFun := φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onTerm, φ.left_inv, LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onTerm, φ.right_inv, LHom.id_onTerm]

variable (L : MSLanguage.{u, v, z} Sorts)


/-- A bounded formula for a many-sorted language `L`, with free variables in `α`.
  Remark: we are using the dependent map representation for SortedTuples here,
  for a similar reason as in the defintion of Terms -/
inductive BoundedFormula (α : Sorts → Type u') : List Sorts → Type (max u v z u')
  | falsum {σ} : BoundedFormula α σ
  | equal {σ t}
    -- note: only terms with the exact same signatures can be set equal to eachother
      (t₁ t₂ : L.Term (α ⊕ₛ σ.toFam) t) :
      BoundedFormula α σ
  | rel {σ σ'}
      (R : L.Relations σ')
      (ts : (i : Fin σ'.length) →  (L.Term (α ⊕ₛ σ.toFam) (σ'.get i))) :
      BoundedFormula α σ
  /-- The logical implication of two bounded formulas-/
  | imp {σ}
      (f₁ f₂ : BoundedFormula α σ) :
      BoundedFormula α σ
  /-- Adds a universal quantifier to a bounded formula-/
  | all {σ s}
      (f : BoundedFormula α (σ ++ [s])) :
      BoundedFormula α σ

abbrev Formula (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') := BoundedFormula L α []

/-- A sentence is a formula with no free variables. -/
abbrev Sentence (L : MSLanguage.{u, v, z} Sorts) :=
  Formula L (fun _ => Empty)

/-- A theory is a set of sentences. -/
abbrev Theory :=
  Set L.Sentence

open Finsupp

variable {L : MSLanguage.{u, v, z} Sorts} {α : Sorts → Type u'} {σ : List Sorts} {s : Sorts}

/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {ξ : List Sorts} (R : L.Relations σ)
    (ts : SortedTuple σ (L.Term (α ⊕ₛ ξ.toFam))) : L.BoundedFormula α ξ :=
  BoundedFormula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations [s]) (t : L.Term (α ⊕ₛ σ.toFam) s) :
    L.BoundedFormula α σ := r.boundedFormula (SortedTuple.fromList' [⟨s,t⟩])

/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations [s₁, s₂]) (t₁ : L.Term (α ⊕ₛ σ.toFam) s₁)
    (t₂ : L.Term (α ⊕ₛ σ.toFam) s₂) :
    L.BoundedFormula α σ := r.boundedFormula (SortedTuple.fromList' [⟨s₁,t₁⟩,⟨s₂,t₂⟩])

/-- The equality of two terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (α ⊕ₛ σ.toFam) s) : L.BoundedFormula α σ :=
  BoundedFormula.equal t₁ t₂

/-- Applies a relation to terms as a formula. -/
def Relations.formula (R : L.Relations σ) (ts : SortedTuple σ (L.Term α)) : L.Formula α:=
  R.boundedFormula (SortedTuple.fromMap (fun i => (ts.toMap i).relabel (fun _ => Sum.inl)))

/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations [s]) (t : L.Term α s) : L.Formula α :=
  Relations.formula r (SortedTuple.fromList' [⟨s,t⟩])

/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations [s₁, s₂]) (t₁ : L.Term α s₁) (t₂ : L.Term α s₂) :
    L.Formula α := Relations.formula r (SortedTuple.fromList' [⟨s₁, t₁⟩, ⟨s₂, t₂⟩])

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α s) : L.Formula α :=
  (t₁.relabel (fun _ => Sum.inl)).bdEqual (t₂.relabel (fun _ => Sum.inl))

namespace BoundedFormula

instance : Inhabited (L.BoundedFormula α σ) :=
  ⟨falsum⟩

instance : Bot (L.BoundedFormula α σ) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
protected def ex {s : Sorts} (φ : L.BoundedFormula α (σ ++ [s])) : L.BoundedFormula α σ :=
  φ.not.all.not

/-- Takes the logical disjunction of two bounded formulas. -/
@[match_pattern]
protected def or (φ ψ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  φ.not.imp ψ

/-- Takes the logical conjunction of two bounded formulas. -/
@[match_pattern]
protected def and (φ ψ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  (φ.not.or ψ.not).not
instance : Top (L.BoundedFormula α σ) :=
  ⟨BoundedFormula.not ⊥⟩

instance : Min (L.BoundedFormula α σ) :=
  ⟨fun f g => (f.imp g.not).not⟩

instance : Max (L.BoundedFormula α σ) :=
  ⟨fun f g => f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BoundedFormula α σ) :=
  φ.imp ψ ⊓ ψ.imp φ

open Finset
open Finsupp

/- TODO: State and prove a multisorted variant of this onesorted definition
/-- The `Finset` of variables used in a given formula. -/
@[simp]
def freeVarFinset [DecidableEq α] : ∀ {n}, L.BoundedFormula α n → Finset α
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts => univ.biUnion fun i => (ts i).varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | _n, all f => f.freeVarFinset
-/

/- TODO: State and prove multisorted variants of these onesorted theorems
/-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
@[simp]
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
  | _m, _n, _h, falsum => falsum
  | _m, _n, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
  | _m, _n, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
  | _m, _n, h, all f => (f.castLE (add_le_add_right h 1)).all

@[simp]
theorem castLE_rfl {n} (h : n ≤ n) (φ : L.BoundedFormula α n) : φ.castLE h = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp [Fin.castLE_of_eq]
  | rel => simp [Fin.castLE_of_eq]
  | imp _ _ ih1 ih2 => simp [Fin.castLE_of_eq, ih1, ih2]
  | all _ ih3 => simp [Fin.castLE_of_eq, ih3]

@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : L.BoundedFormula α k) :
    (φ.castLE km).castLE mn = φ.castLE (km.trans mn) := by
  revert m n
  induction φ with
  | falsum => intros; rfl
  | equal => simp
  | rel =>
    intros
    simp only [castLE, eq_self_iff_true, heq_iff_eq]
    rw [← Function.comp_assoc, Term.relabel_comp_relabel]
    simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => intros; simp only [castLE, ih3]

@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedFormula.castLE mn ∘ BoundedFormula.castLE km :
        L.BoundedFormula α k → L.BoundedFormula α n) =
      BoundedFormula.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)
-/


/- TODO: State and prove a multisorted variant of these onesorted definitions and theorems
/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrictFreeVar [DecidableEq α] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (_f : φ.freeVarFinset → β), L.BoundedFormula β n
  | _n, falsum, _f => falsum
  | _n, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft (f ∘ Set.inclusion subset_union_left))
      (t₂.restrictVarLeft (f ∘ Set.inclusion subset_union_right))
  | _n, rel R ts, f =>
    rel R fun i => (ts i).restrictVarLeft (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => Term.varFinsetLeft (ts i)) (mem_univ i)))
  | _n, imp φ₁ φ₂, f =>
    (φ₁.restrictFreeVar (f ∘ Set.inclusion subset_union_left)).imp
      (φ₂.restrictFreeVar (f ∘ Set.inclusion subset_union_right))
  | _n, all φ, f => (φ.restrictFreeVar f).all


/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs
-/

/-- Maps bounded formulas along a map of terms and a map of relations.
  TODO: This lemma is currently more restrictive than its one-sorted cousin,
  as it assumes that arity of formulas is preserved and sorts are literally the same
  on both sides -/
def mapTermRel (ft : ∀ σ : List Sorts, (L.Term (α ⊕ₛ σ.toFam)) →ₛ (L'.Term (β ⊕ₛ σ.toFam)) )
    (fr : ∀ σ, L.Relations σ → L'.Relations σ) :
    ∀ {σ}, L.BoundedFormula α σ → L'.BoundedFormula β σ
  | _σ, falsum => falsum
  | _σ, equal t₁ t₂ => equal (ft _ _ t₁) (ft _ _ t₂)
  | _σ, rel R ts => rel (fr _ R) fun i => ft _ _ (ts i)
  | _σ, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr).imp (φ₂.mapTermRel ft fr)
  | _σ, all φ => all (φ.mapTermRel ft fr)

/-
/-- Raises all of the `Fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def liftAt : ∀ {n : ℕ} (n' _m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n + n') :=
  fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

@[simp]
theorem mapTermRel_mapTermRel {L'' : MSLanguage}
    (ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (ft' : ∀ n, L'.Term (β ⊕ Fin n) → L''.Term (γ ⊕ (Fin n)))
    (fr' : ∀ n, L'.Relations n → L''.Relations n) {n} (φ : L.BoundedFormula α n) :
    ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) =
      φ.mapTermRel (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

@[simp]
theorem mapTermRel_id_id_id {n} (φ : L.BoundedFormula α n) :
    (φ.mapTermRel (fun _ => id) (fun _ => id) fun _ => id) = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps]
def mapTermRelEquiv (ft : ∀ n, L.Term (α ⊕ (Fin n)) ≃ L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormula α n ≃ L'.BoundedFormula β n :=
  ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → β ⊕ (Fin n)) (k : ℕ) : α ⊕ (Fin k) → β ⊕ (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]
theorem sumElim_comp_relabelAux {m : ℕ} {g : α → β ⊕ (Fin n)} {v : β → M}
    {xs : Fin (n + m) → M} : Sum.elim v xs ∘ relabelAux g m =
    Sum.elim (Sum.elim v (xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n) := by
  ext x
  rcases x with x | x
  · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    rcases g x with l | r <;> simp
  · simp [BoundedFormula.relabelAux]

@[simp]
theorem relabelAux_sumInl (k : ℕ) :
    relabelAux (Sum.inl : α → α ⊕ (Fin n)) k = Sum.map id (natAdd n) := by
  ext x
  cases x <;> · simp [relabelAux]

@[deprecated (since := "2025-02-21")] alias relabelAux_sum_inl := relabelAux_sumInl

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) : L.BoundedFormula β (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

/-- Relabels a bounded formula's free variables along a bijection. -/
def relabelEquiv (g : α ≃ β) {k} : L.BoundedFormula α k ≃ L.BoundedFormula β k :=
  mapTermRelEquiv (fun _n => Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
    fun _n => _root_.Equiv.refl _

@[simp]
theorem relabel_falsum (g : α → β ⊕ (Fin n)) {k} :
    (falsum : L.BoundedFormula α k).relabel g = falsum :=
  rfl

@[simp]
theorem relabel_bot (g : α → β ⊕ (Fin n)) {k} : (⊥ : L.BoundedFormula α k).relabel g = ⊥ :=
  rfl

@[simp]
theorem relabel_imp (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl

@[simp]
theorem relabel_not (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) :
    φ.not.relabel g = (φ.relabel g).not := by simp [BoundedFormula.not]

@[simp]
theorem relabel_all (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabel g = (φ.relabel g).all := by
  rw [relabel, mapTermRel, relabel]
  simp

@[simp]
theorem relabel_ex (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabel g = (φ.relabel g).ex := by simp [BoundedFormula.ex]

@[simp]
theorem relabel_sumInl (φ : L.BoundedFormula α n) :
    (φ.relabel Sum.inl : L.BoundedFormula α (0 + n)) = φ.castLE (ge_of_eq (zero_add n)) := by
  simp only [relabel, relabelAux_sumInl]
  induction φ with
  | falsum => rfl
  | equal => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]
  | rel => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]; rfl
  | imp _ _ ih1 ih2 => simp_all [mapTermRel]
  | all _ ih3 => simp_all [mapTermRel]

@[deprecated (since := "2025-02-21")] alias relabel_sum_inl := relabel_sumInl

/-- Substitutes the variables in a given formula with terms. -/
def subst {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.Term β) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id

/-- A bijection sending formulas with constants to formulas with extra variables. -/
def constantsVarsEquiv : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (γ ⊕ α) n :=
  mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _

/-- Turns the extra variables of a bounded formula into free variables. -/
@[simp]
def toFormula : ∀ {n : ℕ}, L.BoundedFormula α n → L.Formula (α ⊕ (Fin n))
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => t₁.equal t₂
  | _n, rel R ts => R.formula ts
  | _n, imp φ₁ φ₂ => φ₁.toFormula.imp φ₂.toFormula
  | _n, all φ =>
    (φ.toFormula.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))).all

/-- Take the disjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iSup [Finite β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊔ ·) ⊥

/-- Take the conjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iInf [Finite β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊓ ·) ⊤
-/
end BoundedFormula

namespace LHom

open BoundedFormula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
def onBoundedFormula (g : L →ᴸ L') :
    ∀ {ξ : List Sorts}, L.BoundedFormula α ξ → L'.BoundedFormula α ξ
  | _ξ, falsum => falsum
  | _ξ, BoundedFormula.equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | _ξ, rel R ts => (g.onRelation R).boundedFormula (SortedTuple.fromMap (fun i => g.onTerm (ts i)))
  | _ξ, imp f₁ f₂ => (onBoundedFormula g f₁).imp (onBoundedFormula g f₂)
  | _ξ, all f => (onBoundedFormula g f).all

@[simp]
theorem id_onBoundedFormula :
    ((LHom.id L).onBoundedFormula : L.BoundedFormula α σ  → L.BoundedFormula α σ) = id := by
  ext f
  induction f with
  | falsum => rfl
  | equal => rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  | rel => simp only [onBoundedFormula, LHom.id_onTerm,id_onRelation,
    id, Relations.boundedFormula, SortedTuple.toMap_fromMap]
  | imp _ _ ih1 ih2 => rw [onBoundedFormula, ih1, ih2, id, id, id]
  | all _ ih3 => rw [onBoundedFormula, ih3, id, id]

@[simp]
theorem comp_onBoundedFormula {L'' : MSLanguage Sorts} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α σ → L''.BoundedFormula α σ) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula := by
  ext f
  induction f with
  | falsum => rfl
  | equal => simp [Term.bdEqual]
  | rel => simp [onBoundedFormula,Function.comp_apply,onBoundedFormula,Relations.boundedFormula]
  --simp [onBoundedFormula, comp_onRelation, comp_onTerm, Function.comp_apply]
  | imp _ _ ih1 ih2 =>
    simp only [onBoundedFormula, Function.comp_apply, ih1, ih2]
  | all _ ih3 => simp only [ih3, onBoundedFormula, Function.comp_apply]

/-- Maps a formula's symbols along a language map. -/
def onFormula (g : L →ᴸ L') : L.Formula α → L'.Formula α :=
  g.onBoundedFormula

/-- Maps a sentence's symbols along a language map. -/
def onSentence (g : L →ᴸ L') : L.Sentence → L'.Sentence :=
  g.onFormula

/-- Maps a theory's symbols along a language map. -/
def onTheory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
  g.onSentence '' T

@[simp]
theorem mem_onTheory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.Sentence} :
    φ ∈ g.onTheory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.onSentence φ₀ = φ :=
  Set.mem_image _ _ _

end LHom

namespace LEquiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps]
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α σ ≃ L'.BoundedFormula α σ where
  toFun := φ.toLHom.onBoundedFormula
  invFun := φ.invLHom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.left_inv,
      LHom.id_onBoundedFormula]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.right_inv,
      LHom.id_onBoundedFormula]

theorem onBoundedFormula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α σ ≃ L.BoundedFormula α σ) =
      φ.symm.onBoundedFormula :=
  rfl

/-- Maps a formula's symbols along a language equivalence. -/
def onFormula (φ : L ≃ᴸ L') : L.BoundedFormula α σ ≃ L'.BoundedFormula α σ :=
  φ.onBoundedFormula

@[simp]
theorem onFormula_apply (φ : L ≃ᴸ L') :
    (φ.onFormula : L.Formula α → L'.Formula α) = φ.toLHom.onFormula :=
  rfl

@[simp]
theorem onFormula_symm (φ : L ≃ᴸ L') :
    (φ.onFormula.symm : L'.BoundedFormula α σ ≃ L.BoundedFormula α σ) = φ.symm.onFormula :=
  rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps!]
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula

end LEquiv

@[inherit_doc] scoped[MSFirstOrder] infixl:88 " =' " => MSFirstOrder.MSLanguage.Term.bdEqual
-- input \~- or \simeq

@[inherit_doc] scoped[MSFirstOrder] infixr:62 " ⟹ " => MSFirstOrder.MSLanguage.BoundedFormula.imp
-- input \==>

@[inherit_doc] scoped[MSFirstOrder] prefix:110 "∀'" => MSFirstOrder.MSLanguage.BoundedFormula.all
-- input \forall'

@[inherit_doc] scoped[MSFirstOrder] prefix:arg "∼" => MSFirstOrder.MSLanguage.BoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[MSFirstOrder] infixl:61 " ⇔ " => MSFirstOrder.MSLanguage.BoundedFormula.iff
-- input \<=>

@[inherit_doc] scoped[MSFirstOrder] prefix:110 "∃'" => MSFirstOrder.MSLanguage.BoundedFormula.ex
-- input \ex'


namespace Formula
/-
/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α →ₛ β) : L.Formula α → L.Formula β :=
  @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0

/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions n) : L.Formula (Fin (n + 1)) :=
  Term.equal (var 0) (func f fun i => var i.succ)
-/

/-- The negation of a formula. -/
protected nonrec abbrev not (φ : L.Formula α) : L.Formula α :=
  φ.not

/-- The implication between formulas, as a formula. -/
protected abbrev imp : L.Formula α → L.Formula α → L.Formula α:=
  BoundedFormula.imp

/-
variable (β) in
/-- `iAlls f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by universally
quantifying over all variables `Sum.inr _`. -/
noncomputable def iAlls [Finite β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).alls

variable (β) in
/-- `iExs f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _`. -/
noncomputable def iExs [Finite β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).exs

variable (β) in
/-- `iExsUnique f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _` and asserting that the solution should be unique -/
noncomputable def iExsUnique [Finite β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  iExs β <| φ ⊓ iAlls β
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInf fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))
-/
protected nonrec abbrev iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.iff ψ
/-
/-- Take the disjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iSup [Finite α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iSup f

/-- Take the conjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iInf [Finite α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iInf f

/-- A bijection sending formulas to sentences with constants. -/
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm

theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence φ).not :=
  rfl

theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=
  rfl

end Formula

namespace Relations

variable (r : L.Relations 2)

/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.Sentence :=
  ∀'r.boundedFormula₂ (&0) &0

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.Sentence :=
  ∀'∼(r.boundedFormula₂ (&0) &0)

/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)

/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.Sentence :=
  ∀'∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)

/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⊔ r.boundedFormula₂ (&1) &0)

end Relations

section Cardinality

variable (L)

/-- A sentence indicating that a structure has `n` distinct elements. -/
protected def Sentence.cardGe (n : ℕ) : L.Sentence :=
  ((((List.finRange n ×ˢ List.finRange n).filter fun ij : _ × _ => ij.1 ≠ ij.2).map
          fun ij : _ × _ => ∼((&ij.1).bdEqual &ij.2)).foldr
      (· ⊓ ·) ⊤).exs

/-- A theory indicating that a structure is infinite. -/
def infiniteTheory : L.Theory :=
  Set.range (Sentence.cardGe L)

/-- A theory that indicates a structure is nonempty. -/
def nonemptyTheory : L.Theory :=
  {Sentence.cardGe L 1}

/-- A theory indicating that each of a set of constants is distinct. -/
def distinctConstantsTheory (s : Set α) : L[[α]].Theory :=
  (fun ab : α × α => ((L.con ab.1).term.equal (L.con ab.2).term).not) ''
  (s ×ˢ s ∩ (Set.diagonal α)ᶜ)

variable {L}

open Set

theorem distinctConstantsTheory_mono {s t : Set α} (h : s ⊆ t) :
    L.distinctConstantsTheory s ⊆ L.distinctConstantsTheory t := by
  unfold distinctConstantsTheory; gcongr

theorem monotone_distinctConstantsTheory :
    Monotone (L.distinctConstantsTheory : Set α → L[[α]].Theory) := fun _s _t st =>
  L.distinctConstantsTheory_mono st

theorem directed_distinctConstantsTheory :
    Directed (· ⊆ ·) (L.distinctConstantsTheory : Set α → L[[α]].Theory) :=
  Monotone.directed_le monotone_distinctConstantsTheory

theorem distinctConstantsTheory_eq_iUnion (s : Set α) :
    L.distinctConstantsTheory s =
      ⋃ t : Finset s,
        L.distinctConstantsTheory (t.map (Function.Embedding.subtype fun x => x ∈ s)) := by
  classical
    simp only [distinctConstantsTheory]
    rw [← image_iUnion, ← iUnion_inter]
    refine congr(_ '' ($(?_) ∩ _))
    ext ⟨i, j⟩
    simp only [prodMk_mem_set_prod_eq, Finset.coe_map, Function.Embedding.coe_subtype, mem_iUnion,
      mem_image, Finset.mem_coe, Subtype.exists, exists_and_right, exists_eq_right]
    refine ⟨fun h => ⟨{⟨i, h.1⟩, ⟨j, h.2⟩}, ⟨h.1, ?_⟩, ⟨h.2, ?_⟩⟩, ?_⟩
    · simp
    · simp
    · rintro ⟨t, ⟨is, _⟩, ⟨js, _⟩⟩
      exact ⟨is, js⟩

end Cardinality

end Language

end MSFirstOrder
-/
end Formula

end MSLanguage

end MSFirstOrder
