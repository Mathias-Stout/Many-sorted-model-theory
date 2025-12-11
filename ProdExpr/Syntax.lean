import ProdExpr.LanguageMap
import ProdExpr.SortedTuple

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

variable {Sorts : Type z} {σ : ProdExpr Sorts}
  {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
  {M : Sorts → Type w} {α : Sorts → Type u'} {β : Sorts → Type v'} {γ : Sorts → Type*}

open MSFirstOrder MSStructure Fin Fam SortedTuple ProdExpr

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms.
  We cannot use SortedTuple here, as this this trows an error related to nested inductive datatypes.
  Insead, we use dependent maps here, and define appropriate coercions for SortedTuples.
  See also the remark about instDecidableEq_sorted_tuple.
-/
inductive Term (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') :
    ProdExpr Sorts → Type max z u' u where
-- Vars of type `s : S` give terms of type `s : S`.
| var (s : Sorts) : α s → L.Term α (.of s)
-- If we have a term of type `s : ProdExpr S` and a function in the language to `t : S`, then
-- applying the function results in a term of type `t : S`.
| func {σ : ProdExpr Sorts} {t : Sorts} (f : L.Functions σ t) (r : L.Term α σ) : L.Term α (.of t)
-- If we have terms of type `s` and `t` then combining them results in a term of type `s.prod t`.
| prod {σ τ : ProdExpr Sorts} : L.Term α σ → L.Term α τ → L.Term α (σ.prod τ)
| nil : L.Term α .nil

/-- An abbrev for Terms with both named and indexed variables. -/
abbrev BTerm (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') (σ τ : ProdExpr Sorts) :=
   L.Term (α ⊕ₛ σ.indVar) τ

/--
Needed in some cases to show termination for recursion on terms
-/
def Term.size : {σ : ProdExpr Sorts} → L.Term α σ → Nat
    | _, .nil            => 0
    | _, .var _ _        => 1
    | _, .func _ ts  => 1 + ts.size
    | _, .prod t₁ t₂     => 1 + Term.size t₁ + Term.size t₂
/-
inductive Term (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') : Sorts → Type max z u' u
 | var t : (α t) → L.Term α σ
 | func (σ : ProdExpr Sorts) t : ∀ (_ : L.Functions σ t),
    (SortedMap (L.Term α) σ ) → L.Term α σ
-/
/- compare this with the simpler definition of terms in the 1-sorted case
inductive Term (α : Type u') : Type max u u'
  | var : α → Term α
  | func : ∀ {l : ℕ} (_f : L.Functions l) (_ts : Fin l → Term α), Term α-/
namespace Term

/-- DecidableEq for SortedTuples as dependent maps
  see also the remark at the definition of Terms. -/
def instDecidableEq_sorted_tuple {σ : ProdExpr Sorts} {α : Sorts → Type w}
  [hyp : ∀ i : Fin σ.length, DecidableEq (α (σ.get i))] :
  DecidableEq ((i : Fin σ.length) → α (σ.get i)) :=
  inferInstance

/-
--TODO: improve this proof
instance instDecidableEq
  [DecidableEq Sorts]
  [∀ σ : ProdExpr Sorts, DecidableEq (σ.Interpret α)]
  [∀ s, DecidableEq (α s)]
  [∀ σ t, DecidableEq (L.Functions σ t)] :
  ∀ σ, DecidableEq (L.Term α σ) :=
  fun σ t₁ t₂ =>
  match σ, t₁, t₂ with
  | _, nil, nil => .isTrue rfl
  | _, var s₁ x₁, var _ x₂ =>
    if h : x₁ = x₂ then
      (.isTrue (by rw[h]))
    else
      (.isFalse (by simp_all only [var.injEq, not_false_eq_true]))
  | _, func σ₁ s₁ f₁ r₁, func σ₂ _ f₂ r₂ =>
    if h : σ₁ = σ₂ then
    [Mathias: no DecidableEq instance after casting]
      if h' : f₁ = h ▸ f₂ ∧ r₁ = h ▸ r₂ then
        sorry
      else
        sorry
    else
      sorry

  | _, (prod _ _), _ => sorry
  | _, (func _ _), (var _ _) => sorry
  | _, (var _ _), (func _ _) => sorry
-/


open Finset

/-- The `Finset` of variables used in a given term (now multi-sorted). -/
@[simp]
def varFinset {σ : ProdExpr Sorts} {α : Sorts → Type u'}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : L.Term α σ → Finset (Σ t, α t)
  | var t i => {⟨_,i⟩}
  | func _ args => args.varFinset
  | prod t₁ t₂ => t₁.varFinset ∪ t₂.varFinset
  | nil => ∅

lemma varFinset_prod_subset_left {σ₁ σ₂ : ProdExpr Sorts} {α : Sorts → Type u'}
    {t₁ : L.Term α σ₁} {t₂ : L.Term α σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFinset t₁ ⊆ varFinset (prod t₁ t₂) := by
    exact union_subset_left fun ⦃a⦄ a_1 ↦ a_1

lemma varFinset_prod_subset_right {σ₁ σ₂ : ProdExpr Sorts} {α : Sorts → Type u'}
    {t₁ : L.Term α σ₁} {t₂ : L.Term α σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFinset t₂ ⊆ varFinset (prod t₁ t₂) := by
    exact union_subset_right fun ⦃a⦄ a_1 ↦ a_1

/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeft {σ : ProdExpr Sorts} [DecidableEq Sorts] [∀ t, DecidableEq (α t)] :
    L.Term (α ⊕ₛ β) σ → Finset (Σ t, α t)
  | var _ (Sum.inl i) => {⟨_,i⟩}
  | var _ (Sum.inr _i) => ∅
  | func _ args => args.varFinsetLeft
  | prod t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | nil => ∅

/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetRight {σ : ProdExpr Sorts} [DecidableEq Sorts] [∀ t, DecidableEq (β t)] :
    L.Term (α ⊕ₛ β) σ → Finset (Σ t, β t)
  | var _ (Sum.inr i) => {⟨_,i⟩}
  | var _ (Sum.inl _i) => ∅
  | func _ args => args.varFinsetRight
  | prod t₁ t₂ => t₁.varFinsetRight ∪ t₂.varFinsetRight
  | nil => ∅

/-- Relabels a term's variables along a particular function -/
@[simp]
def relabel {σ : ProdExpr Sorts} (g : α →ₛ β) : L.Term α σ → L.Term β σ
  | var t a => var t (g t a)
  | func f₁ args  => func f₁ (relabel g args)
  | prod t₁ t₂ => prod (relabel g t₁) (relabel g t₂)
  | nil => (nil : L.Term β .nil)

/-- Relabel the sum type variables along a map of left summands -/
@[simp]
def relabel_left {σ : ProdExpr Sorts} (g : α →ₛ β) : L.Term (α ⊕ₛ γ) σ → L.Term (β ⊕ₛ γ) σ :=
    relabel (fun s => Sum.map (g s) id)

/-- Relabel the sum type variables along a map of right summands -/
@[simp]
def relabel_right {σ : ProdExpr Sorts} (g : α →ₛ β) : L.Term (γ ⊕ₛ α) σ → L.Term (γ ⊕ₛ β) σ :=
  relabel (fun s => Sum.map id (g s))

variable {t : Sorts} {σ : ProdExpr Sorts}

@[simp]
theorem relabel_id {f : L.Term α σ} : relabel (Fam.id α) f = f := by
  induction f with
  | var => rfl
  | func _ _ ih => simp [ih]
  | prod t₁ t₂ ih₁ ih₂ =>
    simp only [relabel, ih₁, ih₂]
  | nil => rfl

@[simp]
theorem relabel_id_eq_id : (relabel (Fam.id α) :
  L.Term α σ → L.Term α σ) = id :=
  funext (fun _ => relabel_id)

@[simp]
theorem relabel_id_eq_id' : (relabel (fun s => @id (α s)) : L.Term α σ → L.Term α σ) = id :=
  funext (fun _ => relabel_id)

@[simp]
theorem relabel_relabel (f : α →ₛ β) (g : β →ₛ γ) (t : L.Term α σ) :
    relabel g (relabel  f t)= relabel (g ∘ₛ f) t:= by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]
  | prod t₁ t₂ ih₁ ih₂ => simp only [relabel, ih₁, ih₂]
  | nil => rfl

@[simp]
theorem relabel_comp_relabel (f : α →ₛ β) (g : famMap β γ) :
    (relabel g ∘ relabel f : L.Term α σ → L.Term γ σ) = Term.relabel (g ∘ₛ f) :=
  funext (relabel_relabel f g)

/-- Relabels a term's variables along a bijection. -/
@[simps]
def relabelEquiv (g : α ≃ₛ β) : L.Term α σ ≃ L.Term β σ :=
  ⟨relabel (fun s => g s), relabel (fun s => (g.toEquiv s).symm),
  fun _ => by
    simp [Fam.MSEquiv.toEquiv]
    , fun _ => by  simp [Fam.MSEquiv.toEquiv]⟩

/-- Restricts a term to use only a set of the given variables. -/
@[simp]
def restrictVar
  [DecidableEq Sorts]
  [∀ t, DecidableEq (α t)]
  : ∀ {σ : ProdExpr Sorts} (f : L.Term α σ)
      (_ : ∀ {s}, {x : α s // ⟨s, x⟩ ∈ varFinset f } → β s),
      L.Term β σ
| _ , var t a, g =>
    let x : {x : α t // ⟨t, x⟩ ∈ varFinset (var t a) } :=
      { val := a,
        property := by simp [varFinset] }
    var t (@g t x)
| _, func f ts, g =>
    func f (restrictVar ts g)
| _, prod t₁ t₂, g =>
    prod (restrictVar t₁ (fun x => g ⟨x.val, by
          simp_all only [varFinset, mem_union]
          obtain ⟨val, property⟩ := x
          simp_all only [true_or]⟩ ))
        (restrictVar t₂ (fun x => g ⟨x.val, by
          simp_all only [varFinset, mem_union]
          obtain ⟨val, property⟩ := x
          simp_all only [or_true]⟩))
  | _, nil, _ => nil

/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrictVarLeft [DecidableEq Sorts] {γ : Sorts → Type*}
  [∀ t, DecidableEq (α t)]
  : ∀ {σ : ProdExpr Sorts} (f : L.Term (α ⊕ₛ γ) σ)
      (_ : ∀ {s}, {x : α s // ⟨s, x⟩ ∈ varFinsetLeft f } → β s),
    L.Term (β ⊕ₛ γ) σ
| _, var t (Sum.inl a), g =>
  let x : {x : α t // ⟨t, x⟩ ∈ varFinsetLeft (var t (Sum.inl a)) } :=
      { val := a,
        property := by simp [varFinsetLeft] }
  var t (Sum.inl (@g t x))
| _, var t (Sum.inr a), _ => var t (Sum.inr a)
| _, func t ts, g =>
  func t (restrictVarLeft ts g)
| _, prod t₁ t₂, g =>
    prod
        (restrictVarLeft t₁ (fun x => g ⟨x.val, by
          simp_all only [varFinsetLeft, mem_union]
          obtain ⟨val, property⟩ := x
          simp_all only [true_or]⟩ ))
        (restrictVarLeft t₂ (fun x => g ⟨x.val, by
          simp_all only [varFinsetLeft, mem_union]
          obtain ⟨val, property⟩ := x
          simp_all only [or_true]⟩))
| _, nil, _ => nil
end Term

variable {s₁ s₂ : Sorts} {t : Sorts}
open Term

/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants t) : L.Term α (of t) :=
  func c nil

/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions (of s₁) s₂) (t : L.Term α (of s₁)) : L.Term α (of s₂) :=
  func f t

/-- Applies a binary function to two terms. -/
def Functions.apply₂ {s₁ s₂ : Sorts} (f : L.Functions ((ProdExpr.of s₁).prod (of s₂)) t)
   (g₁ : L.Term α (of s₁)) (g₂ : L.Term α (of s₂)) : L.Term α (of t) :=
   func f (prod g₁ g₂)

/--
A product term representing a canonical "tuple of variables" for a signature σ.
-/
def varTerm : ∀ σ : ProdExpr Sorts, Term L (indVar σ) σ
  | .nil =>
      .nil
  | .of s =>
      .var s indVar.var
  | .prod σ τ =>
      let leftTerm  : L.Term (indVar (σ.prod τ)) σ :=
        relabel (fun s v => indVar.left (σ := σ) (τ := τ) (s := s) v)
          (varTerm σ)
      let rightTerm : L.Term (indVar (σ.prod τ)) τ :=
        relabel (fun s v => indVar.right (σ := σ) (τ := τ) (s := s) v)
          (varTerm τ)
      .prod leftTerm rightTerm

instance indVarNilEmpty {s : Sorts} : IsEmpty (indVar nil s) := by
  constructor
  intro a
  cases a

instance indVarofInhabited {s : Sorts} : Inhabited (indVar (of s) s) := by
  constructor
  case default =>
    exact indVar.var

instance indVarofUnique {s : Sorts} : Unique (indVar (of s) s) := by
  constructor
  · intro a
    cases a
    case var => rfl

def get {σ : ProdExpr Sorts} (xs : σ.Interpret α) : (s : Sorts) → (indVar σ s) → α s :=
  match σ with
  | .nil => fun s => fun v => isEmptyElim v
  | .of t => fun s => fun v => by
    cases v
    exact xs
  | .prod σ τ => fun s => fun v =>
    match v with
    | indVar.left w => get xs.1 s w
    | indVar.right w => get xs.2 s w

def getVar {σ : ProdExpr Sorts} (s : Sorts) (v : indVar σ s) : L.Term (α ⊕ₛ (indVar σ)) (of s) :=
  Term.var s (Sum.inr v)

/- The representation of a function symbol as a term, on fresh variables indexed by `indVar σ` -/
def Functions.term {σ : ProdExpr Sorts} {t : Sorts} (f : L.Functions σ t) : L.Term (indVar σ) (of t)
   := func f (varTerm σ)

namespace Term

/-- Sends a term with constants to a term with extra variables. -/
@[simp]
def constantsToVars {σ : ProdExpr Sorts} : L[[γ]].Term α σ → L.Term (γ ⊕ₛ α) σ
  | var t a => var t (Sum.inr a)
  | func (σ := σ) (t := t) f ts =>
    Sum.casesOn f
      (fun f => func f ts.constantsToVars)
      fun c => by
        cases σ
        case nil => exact var t (Sum.inl c)
        case of => exact isEmptyElim c
        case prod => exact isEmptyElim c
  | nil => nil
  | prod t₁ t₂ => prod (t₁.constantsToVars) (t₂.constantsToVars)


/-- Sends a term with extra variables to a term with constants. -/
@[simp]
def varsToConstants {σ : ProdExpr Sorts}
 : L.Term (γ ⊕ₛ α) σ → L[[γ]].Term α σ
  | var t (Sum.inr a : (γ ⊕ₛ α) t)  => var t a
  | var _t (Sum.inl a : (γ ⊕ₛ α) _t) => Constants.term (Sum.inr a)
  | func (t := t) f ts => func (Sum.inl f) ts.varsToConstants
  | nil => nil
  | prod t₁ t₂ => prod (t₁.varsToConstants) (t₂.varsToConstants)

/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
def constantsVarsEquiv {τ : ProdExpr Sorts} : L[[γ]].Term α τ ≃ L.Term (γ ⊕ₛ α) τ :=
  ⟨constantsToVars,
  varsToConstants,
  (by
    intro t
    induction t
    case var s t => simp_all only [constantsToVars, varsToConstants]
    case func σ t f ts ih =>
        cases f
        case inl =>
          simp_all only [constantsToVars, varsToConstants, constantsOn_Functions, constantsOnFunc]
        case inr s val =>
          cases σ
          case nil =>
            cases ts ; case nil => rfl
          case of =>
            cases ts
            case var s => exact isEmptyElim val
            case func => exact isEmptyElim val
          case prod σ τ =>
            cases ts
            exact isEmptyElim val
    case nil => simp_all only [constantsToVars, varsToConstants]
    case prod t₁ t₂ => simp_all only [constantsToVars, varsToConstants]
  ),
  (by
    intro t
    induction t
    case var s t =>
      cases t with
      | inl val =>
        simp_all only [varsToConstants, constantsOn_Functions, constantsOnFunc]
        rfl
      | inr val_1 => simp_all only [varsToConstants, constantsToVars]
    case func σ t f ts ih =>
        simp_all only [varsToConstants, constantsOn_Functions, constantsOnFunc, constantsToVars]
    case nil => simp_all only [constantsToVars, varsToConstants]
    case prod t₁ t₂ => simp_all only [constantsToVars, varsToConstants]
  ) ⟩

variable {σ : ProdExpr Sorts}

/-- A bijection between terms with constants and terms with extra variables. -/
def constantsVarsEquivLeft : L[[γ]].Term (α ⊕ₛ β) σ ≃ L.Term ((γ ⊕ₛ α) ⊕ₛ β ) σ :=
  (constantsVarsEquiv).trans (relabelEquiv (MSEquiv.fromEquivs fun _ => Equiv.sumAssoc _ _ _)).symm

@[simp]
theorem constantsVarsEquivLeft_apply (g : L[[γ]].Term (α ⊕ₛ β) σ) :
    constantsVarsEquivLeft g =
    (constantsToVars g).relabel (fun _ => (Equiv.sumAssoc _ _ _).invFun) := rfl

@[simp]
theorem constantsVarsEquivLeft_symm_apply (g : L.Term ((γ ⊕ₛ α) ⊕ₛ β) σ) :
    (constantsVarsEquivLeft).symm g = varsToConstants (g.relabel (fun _ => Equiv.sumAssoc _ _ _)) :=
  rfl

instance inhabitedOfVar [Inhabited (α t)] : Inhabited (L.Term α (of t)) :=
  ⟨var t default⟩

instance inhabitedOfConstant [Inhabited (L.Constants t)] : Inhabited (L.Term α (of t)) :=
  ⟨(default : L.Constants t).term⟩

open indVar

/-- Pushes all of the `τ`-type indVar-indexed variables on the right side of `σ.prod τ`
    to the rightmost side of `(σ.prod σ').prod τ`.
-/
def liftProdAt {τ ρ : ProdExpr Sorts} (σ' σ : ProdExpr Sorts) :
     L.Term (α ⊕ₛ ((σ.prod τ).indVar)) ρ → L.Term (α ⊕ₛ ((σ.prod σ').prod τ).indVar) ρ :=
  fun t => t.relabel_right liftVar

/-- Pushes the unique indVar in `of s` to the rightmost side of `σ'.prod (of s)`.
-/
def liftOfAt {s : Sorts} {ρ : ProdExpr Sorts} (σ' : ProdExpr Sorts) :
     L.Term (α ⊕ₛ ((of s).indVar)) ρ → L.Term (α ⊕ₛ (σ'.prod (of s)).indVar ) ρ :=
  fun t => t.relabel_right
        (fun _ v =>
          match v with
          | .var => right .var
        )

/-- Casts a term with no indVar indexed variables into one with σ'-indexed variables.
-/
def liftNilAt {ρ : ProdExpr Sorts} (σ' : ProdExpr Sorts) :
     L.Term (α ⊕ₛ ProdExpr.nil.indVar) ρ → L.Term (α ⊕ₛ σ'.indVar ) ρ :=
  fun t => t.relabel_right (fun _ v => by cases v)

section substitution

/-- Substitutes the variables in a given ter with terms. -/
@[simp]
def subst {σ} : L.Term α σ → ((s : Sorts) → α s → (L.Term β (of s))) → L.Term β σ
  | nil , _     => nil
  | var t a, tf => tf t a
  | func f ts, tf => func f (ts.subst tf)
  | prod t₁ t₂, tf => prod (t₁.subst tf) (t₂.subst tf)

/-- Given (t: Term α σ) and (v : σ.indVar s), we want to recover the term in t at position v.
This is the direct analogue of `get` for SortedTuples on the semantic side. -/
def getLeafTerm {σ : ProdExpr Sorts} (t : L.Term α σ) : (s : Sorts) → (σ.indVar s) → L.Term α (of s)
  | s, v =>
  match t with
  | nil => isEmptyElim v
  | var s t =>
      match v with
      | indVar.var => var s t
  | func f r =>
      match v with
      | indVar.var => func f r
  | prod t₁ t₂ =>
    match v with
    | indVar.left w => getLeafTerm t₁ s w
    | indVar.right w => getLeafTerm t₂ s w
/-

def getLeafTerm {σ : ProdExpr Sorts} : L.Term α σ → (s : Sorts) → (σ.indVar s) → L.Term α (of s) :=
  match σ with
  | .nil => fun _  _  v  => isEmptyElim v
  | .of s => fun t => fun _ => fun v => by
    cases v; exact t
  | .prod σ τ => fun t => fun s => fun v =>
    match v with
    | indVar.left w => by
      cases t
      case prod t₁ t₂ => exact getLeafTerm t₁ s w
    | indVar.right w => by
      cases t
      case prod t₁ t₂ => exact getLeafTerm t₂ s w
-/


/-- `getLeafTerm` is monotone nonincreasing in size.
It isn't strictly decreasing at vars as it fixes them,
but is strictly decreasing on func and prod terms. -/
lemma getLeafTerm_size_le
  {σ : ProdExpr Sorts} {t : L.Term α σ} {s : Sorts} {v : σ.indVar s} :
    (t.getLeafTerm s v).size <= t.size := by
    revert s v
    induction t with
    | nil => intro s v; cases v
    | var s' x => intro s v; cases v; simp [getLeafTerm]
    | func f r ih => intro s v; cases v; simp [getLeafTerm]
    | @prod σ₁ σ₂ t₁ t₂ ih₁ ih₂ =>
      intro s v; cases v
      case left w =>
        have h:= ih₁ (v:= w)
        simp[getLeafTerm, size]
        linarith
      case right w =>
        have h:= ih₂ (v:= w)
        simp[getLeafTerm, size]
        linarith

lemma getLeafTerm_size_lt_func
  {σ : ProdExpr Sorts} {ts : L.Term α σ} {s : Sorts} {v : σ.indVar s} {f : L.Functions σ t} :
    (ts.getLeafTerm s v).size < (func f ts).size := by
  simp only [size]
  let h := getLeafTerm_size_le (t := ts) (v := v)
  linarith

lemma getLeafTerm_size_lt_prod_l
  {σ τ : ProdExpr Sorts} {t₁ : L.Term α σ} {t₂ : L.Term α τ} :
    t₁.size < (prod t₁ t₂).size := by
  simp[size]
  linarith

lemma getLeafTerm_size_lt_prod_r
  {σ τ : ProdExpr Sorts} {t₁ : L.Term α σ} {t₂ : L.Term α τ} :
    t₂.size < (prod t₁ t₂).size := by
  simp[size]

/--
Substitutes the functions in a given term with expressions.
-/
@[simp]
def substFunc {σ : ProdExpr Sorts} :
  L.Term α σ →
  (∀ σ t, L.Functions σ t → L'.Term σ.indVar (of t)) →
  L'.Term α σ
  | nil, _  => nil
  | var t a, _ => var t a
  | func (σ := σ) (t := t) f ts, tf =>
      (tf σ t f).subst (fun s => fun v => (ts.getLeafTerm s v).substFunc tf)
  | prod t₁ t₂, tf => prod (t₁.substFunc tf) (t₂.substFunc tf)
termination_by
  t _ => t.size
decreasing_by
  -- The recursive call in the `func` case
  ·  -- goal is: (ts.getLeafTerm s v).size < (func f ts).size
    simp[getLeafTerm_size_lt_func (σ := σ) (ts := ts) (s := s) (v := v) (f := f)]
  -- The recursive call on `t₁` in the `prod` case
  · -- goal is: t₁.size < (prod t₁ t₂).size
    simp[getLeafTerm_size_lt_prod_l (t₁ := t₁) (t₂ := t₂)]
  -- The recursive call on `t₂` in the `prod` case
  · -- goal: t₂.size < (prod t₁ t₂).size
    simp[getLeafTerm_size_lt_prod_r (t₁ := t₁) (t₂ := t₂)]

@[simp]
lemma relabel_subst {σ : ProdExpr Sorts}
  (ρ : ∀ s, α s → β s)
  (t : L.Term α σ)
  (f : ∀ s, β s → L.Term γ (of s)) :
  (relabel ρ t).subst f =
    t.subst (fun s v => f s (ρ s v)) := by
  induction t <;> simp [relabel, subst, *]

/--
Substituting leaf terms into varTerm returns the original term:
-/
@[simp]
lemma indVarTerm_subst_getLeaf
  (σ : ProdExpr Sorts) (ts : L.Term α σ) :
  (varTerm σ).subst (fun s v => ts.getLeafTerm s v) = ts := by
  induction σ with
  | nil =>
      cases ts
      simp [varTerm, subst]
  | of s =>
      cases ts with
      | var s' a =>
          simp [varTerm, subst, getLeafTerm]
      | func f' ts' =>
          simp [varTerm, subst, getLeafTerm]
  | prod σ₁ σ₂ ih₁ ih₂ =>
      cases ts with
      | prod t₁ t₂ =>
          unfold varTerm
          simp [subst, getLeafTerm, ih₁ t₁, ih₂ t₂]

/--
Substituting leaf terms of ts into the generic function term for f returns `func f ts`:
-/
@[simp] lemma Functions.term_subst_getLeaf
  (σ : ProdExpr Sorts) (t : Sorts)
  (f : L.Functions σ t) (ts : L.Term α σ) :
  (Functions.term f).subst (fun s v => ts.getLeafTerm s v) = func f ts := by
  simp[subst, Functions.term]

/--
Helper lemma for substFunc_term: since substFunc's recursive call on `func` terms is actually
on `ts.getLeafTerm s v` rather than `ts`, it's helpful to prove this special case separately.
-/
lemma substFunc_getLeafTerm {s : Sorts} {σ : ProdExpr Sorts} {v : σ.indVar s} {g : L.Term α σ} :
  ((g.getLeafTerm s v).substFunc (@Functions.term _ _)) = g.getLeafTerm s v := by
  revert s v
  induction g with
  | var s x =>
    intro s' v; cases v
    case var => simp[getLeafTerm]
  | func f r ih =>
    intro s v; cases v
    case var => simp[getLeafTerm, substFunc, ih]
  | prod t₁ t₂ ih₁ ih₂ =>
    intro s v; cases v
    case left => simp_all[getLeafTerm]
    case right => simp_all[getLeafTerm]
  | nil => simp

@[simp]
theorem substFunc_term
 (g : L.Term α σ) :
  g.substFunc (@Functions.term _ _) = g := by
  induction g
  case nil =>
    simp_all[substFunc]
  case var =>
    simp_all[substFunc]
  case func f ts h =>
    have h' : (fun s v ↦ (ts.getLeafTerm s v).substFunc (@Functions.term Sorts L))
              = fun s v ↦ (ts.getLeafTerm s v):= by
      ext s v; exact substFunc_getLeafTerm (s:= s) (v:= v)
    unfold substFunc; rw[h']
    simp
  case prod t₁ t₂ ih₁ ih₂ =>
    simp_all[substFunc]

end substitution

end Term

namespace LHom

open Term

variable {σ : ProdExpr Sorts}

/-- Maps a term's symbols along a language map. -/
@[simp]
def onTerm {σ : ProdExpr Sorts} (φ : L →ᴸ L') : L.Term α σ → L'.Term α σ
  | .nil => nil
  | var t a => var t a
  | func f ts => func (φ.onFunction f) (φ.onTerm ts)
  | Term.prod t₁ t₂ => (φ.onTerm t₁).prod (φ.onTerm t₂)

@[simp]
theorem id_onTerm : ((LHom.id L).onTerm : L.Term α σ → L.Term α σ) = id := by
  ext t
  induction t with
  | nil => simp only [onTerm, id_eq]
  | var => rfl
  | func _ _ ih => simp only [onTerm, id_onFunction, id_eq, ih]
  | prod t₁ t₂ ih₁ ih₂ => simp only [onTerm, ih₁, id_eq, ih₂]


@[simp]
theorem comp_onTerm {L'' : MSLanguage Sorts} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α σ → L''.Term α σ) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction t with
  | nil => simp only [onTerm, Function.comp_apply]
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl
  | prod t₁ t₂ ih₁ ih₂ => simp only [onTerm, ih₁, Function.comp_apply, ih₂]

end LHom

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
def LEquiv.onTerm (φ : L ≃ᴸ L') : L.Term α σ ≃ L'.Term α σ where
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
inductive BoundedFormula (α : Sorts → Type u') : ProdExpr Sorts → Type (max u v z u')
  | falsum {σ} : BoundedFormula α σ
  | equal {σ τ}
    -- note: only terms with the exact same signatures can be set equal to eachother
      (t₁ t₂ : L.Term (α ⊕ₛ σ.indVar) τ) :
      BoundedFormula α σ
  | rel {σ σ'}
      (R : L.Relations σ')
      (ts : (L.Term (α ⊕ₛ σ.indVar) σ')) :
      BoundedFormula α σ
  /-- The logical implication of two bounded formulas-/
  | imp {σ}
      (f₁ f₂ : BoundedFormula α σ) :
      BoundedFormula α σ
  /-- Adds a universal quantifier to a bounded formula-/
  | all {σ} (τ)
      (f : BoundedFormula α (σ.prod τ)) :
      BoundedFormula α σ

/-- Size of a bounded formula, useful for proving termination of recursion -/
def BoundedFormula.size : {σ : ProdExpr Sorts} → L.BoundedFormula α σ → Nat
    | _, .falsum            => 1
    | _, .equal _ _        => 1
    | _, .rel _ ts  => 1 + ts.size
    | _, .imp f₁ f₂     => 1 + BoundedFormula.size f₁ + BoundedFormula.size f₂
    | _, all _ f => 1 + BoundedFormula.size f

attribute [simp] BoundedFormula.size

abbrev Formula (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') := BoundedFormula L α nil

/-- A sentence is a formula with no free variables. -/
abbrev Sentence (L : MSLanguage.{u, v, z} Sorts) :=
  Formula L (fun _ => Empty)

/-- A theory is a set of sentences. -/
abbrev Theory :=
  Set L.Sentence

open Finsupp

variable {L : MSLanguage.{u, v, z} Sorts} {α : Sorts → Type u'} {σ ξ : ProdExpr Sorts} {s : Sorts}

/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {ξ : ProdExpr Sorts} (R : L.Relations σ)
    (ts : L.Term (α ⊕ₛ ξ.indVar) σ) : L.BoundedFormula α ξ :=
  BoundedFormula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations (of s)) (t : L.Term (α ⊕ₛ σ.indVar) (of s)) :
    L.BoundedFormula α σ := r.boundedFormula t

/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations ((of s₁).prod (of s₂)))
    (t₁ : L.Term (α ⊕ₛ σ.indVar) (of s₁)) (t₂ : L.Term (α ⊕ₛ σ.indVar) (of s₂)) :
    L.BoundedFormula α σ := r.boundedFormula (t₁.prod t₂)

/-- The equality of two tuples of terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (α ⊕ₛ σ.indVar) ξ) : L.BoundedFormula α σ :=
  BoundedFormula.equal t₁ t₂

/-- Applies a relation to terms as a formula. -/
def Relations.formula (R : L.Relations σ) (ts : L.Term α σ) : L.Formula α :=
  R.boundedFormula (relabel (fun _ => Sum.inl) ts)
/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations (of s)) (t : L.Term α (of s)) : L.Formula α :=
  Relations.formula r t

/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations ((of s₁).prod (of s₂)))
    (t₁ : L.Term α (of s₁)) (t₂ : L.Term α (of s₂)) :
    L.Formula α := Relations.formula r (t₁.prod t₂)

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α σ) : L.Formula α :=
  (relabel (fun _ => Sum.inl) t₁).bdEqual (relabel (fun _ => Sum.inl) t₂)

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
protected def ex (ξ : ProdExpr Sorts) (φ : L.BoundedFormula α (σ.prod ξ)) : L.BoundedFormula α σ :=
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

/-- The `Finset` of variables used in a given formula. -/
@[simp]
def freeVarFinset [DecidableEq Sorts] [∀ s, DecidableEq (α s)] :
    ∀ {n}, L.BoundedFormula α n → Finset (Sigma α)
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts =>  ts.varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | _n, all _ f => f.freeVarFinset

open ProdExpr
open VarMap

/-- Casts `L.BoundedFormula α σ` as `L.BoundedFormula α τ`, given a dependent family of
embeddings `σ.indVar → τ.indVar`.

This could be a VarEmbed if we want it to model the original idea of "Moving some variables right"
-/
@[simp]
def castLE : ∀ {σ τ : ProdExpr Sorts} (_ : VarMap σ τ ), L.BoundedFormula α σ → L.BoundedFormula α τ
  | _, _, _, falsum => falsum
  | _, _, h, equal t₁ t₂ =>
    equal (t₁.relabel_right h) (t₂.relabel_right h)
  | _, _, h, rel R ts => rel R (ts.relabel_right h)
  | _, _, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
  | _, _, h, all _ f => (f.castLE (h.extend_right)).all

@[simp]
theorem castLE_id {σ : ProdExpr Sorts} (φ : L.BoundedFormula α σ) :
  φ.castLE Id = φ := by
  induction φ with
  | falsum =>
      simp [BoundedFormula.castLE]
  | @equal σ τ t₁ t₂ =>
      change equal (relabel_right (Fam.id (α := σ.indVar )) t₁)
        (relabel_right (Fam.id (α := σ.indVar )) t₂) = equal t₁ t₂
      simp_all only [relabel_right, Fam.id, Sum.map_id_id, relabel_id_eq_id', id_eq]
  | @rel σ τ R ts =>
      change rel R (relabel_right (Fam.id (α := σ.indVar)) ts) = rel R ts
      simp_all only [relabel_right, Fam.id, Sum.map_id_id, relabel_id_eq_id', id_eq]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp_all only [castLE]
  | all _ φ ih =>
      rw [BoundedFormula.castLE]
      rw[VarMap.idExtend]
      simp_all

@[simp]
theorem castLE_castLE : ∀ {σ τ η : ProdExpr Sorts} (hστ : VarMap σ τ) (hτη : VarMap τ η)
                         (φ : L.BoundedFormula α σ),
    (φ.castLE hστ).castLE hτη = φ.castLE (hτη ∘ₛ hστ) := by
  intro σ τ η hστ hτη φ
  revert τ η
  induction φ with
  | falsum => intros; rfl
  | equal =>
    intro τ_1 η hστ hτη
    simp_all only [castLE, relabel_right, relabel_relabel, Sum.map_comp_map, CompTriple.comp_eq]
  | rel =>
    intros
    simp_all only [castLE, relabel_right, relabel_relabel, Sum.map_comp_map, CompTriple.comp_eq]
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ φ ih => simp [castLE, ih]

@[simp]
theorem castLE_comp_castLE {σ τ η : ProdExpr Sorts} (hστ : VarMap σ τ) (hτη : VarMap τ η) :
    (castLE hτη ∘ castLE hστ :
        L.BoundedFormula α σ → L.BoundedFormula α η) =
      BoundedFormula.castLE (hτη ∘ₛ hστ) :=
  funext (castLE_castLE hστ hτη)



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
-/

/-- Maps bounded formulas along a map of terms and a map of relations.
  TODO: This lemma is currently more restrictive than its one-sorted cousin,
  as it assumes that arity of formulas is preserved and sorts are literally the same
  on both sides -/
def mapTermRel {g : ProdExpr Sorts → ProdExpr Sorts}
    (ft : ∀ σ ξ : ProdExpr Sorts, L.Term (α ⊕ₛ σ.indVar) ξ →  L'.Term (β ⊕ₛ (g σ).indVar) ξ)
    (fr : ∀ σ, L.Relations σ → L'.Relations σ)
    (h : ∀ σ τ, L'.BoundedFormula β (g (σ.prod τ)) → L'.BoundedFormula β ((g σ).prod τ)) :
    ∀ {σ}, L.BoundedFormula α σ → L'.BoundedFormula β (g σ)
  | _σ, falsum => falsum
  | _σ, equal t₁ t₂ => equal (ft _ _ t₁) (ft _ _ t₂)
  | _σ, rel R ts => rel (fr _ R) (ft _ _ ts)
  | _σ, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr h).imp (φ₂.mapTermRel ft fr h)
  | _σ, all ξ φ => (h _ _ (φ.mapTermRel ft fr h)).all ξ

/-
/-- Raises all of the `Fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def liftAt : ∀ {n : ℕ} (n' _m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n + n') :=
  fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])
-/

@[simp]
theorem mapTermRel_mapTermRel {L'' : MSLanguage Sorts}
    (ft : ∀ (σ τ : ProdExpr Sorts), L.Term (α ⊕ₛ σ.indVar) τ → L'.Term (β ⊕ₛ σ.indVar) τ)
    (fr : ∀ σ, L.Relations σ → L'.Relations σ)
    (ft' : ∀ (σ τ : ProdExpr Sorts), L'.Term (β ⊕ₛ σ.indVar) τ → L''.Term (γ ⊕ₛ σ.indVar) τ)
    (fr' : ∀ σ, L'.Relations σ → L''.Relations σ) {σ} (φ : L.BoundedFormula α σ) :
    ((φ.mapTermRel ft fr fun _ _ => id).mapTermRel ft' fr' fun _ _ => id) =
    φ.mapTermRel (fun _ _ => ft' _ _ ∘ ft _ _) (fun _ => fr' _ ∘ fr _ ) (fun _ _ => id)
      := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ _ ih3 => simp [mapTermRel, ih3]

@[simp]
theorem mapTermRel_id_id_id {σ} (φ : L.BoundedFormula α σ) :
    (φ.mapTermRel (fun _ _ => id) (fun _ => id) fun _ _=> id) = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ _ ih3 => simp [mapTermRel, ih3]

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps]
def mapTermRelEquiv (ft : ∀ (σ τ : ProdExpr Sorts),
    L.Term (α ⊕ₛ σ.indVar) τ ≃ L'.Term (β ⊕ₛ σ.indVar) τ)
    (fr : ∀ σ, L.Relations σ ≃ L'.Relations σ) {σ} : L.BoundedFormula α σ ≃ L'.BoundedFormula β σ :=
  ⟨mapTermRel (fun σ τ => ft σ τ) (fun σ => fr σ) fun _ _ => id,
  mapTermRel (fun σ τ => (ft σ τ).symm) (fun σ => (fr σ).symm) fun _ _ => id,
  fun φ => by simp, fun φ => by simp⟩

end BoundedFormula

def relabelAux (g : α →ₛ β ⊕ₛ σ.indVar) (τ : ProdExpr Sorts) :
              (α ⊕ₛ τ.indVar) →ₛ β ⊕ₛ (σ.prod τ).indVar :=
  fun s =>  Sum.map id (Sum.elim .left .right) ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map (g s) id

/-
Mathlib relabelAux for comparison with above:

def relabelAux {n} {α β} (g : α → β ⊕ (Fin n)) (k : ℕ) : α ⊕ (Fin k) → β ⊕ (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id
-/

@[simp] def Term.relabelAux
    {α β : Sorts → Type _}
    {σ τ : ProdExpr Sorts}
    (g : α →ₛ (β ⊕ₛ σ.indVar))
    (ξ : ProdExpr Sorts) :
    L.Term (α ⊕ₛ τ.indVar) ξ →
    L.Term (β ⊕ₛ (σ.prod τ).indVar) ξ :=
  fun t => t.relabel (MSLanguage.relabelAux g τ)

namespace BoundedFormula

def prodAssocR
    (σ τ η : ProdExpr Sorts) :
    L.BoundedFormula β (σ.prod (τ.prod η )) →
    L.BoundedFormula β ((σ.prod τ ).prod η ) :=
  fun φ =>
    φ.castLE (VarMap.assocR σ τ η)

def relabel
    (τ : ProdExpr Sorts)
    (g : α →ₛ (β ⊕ₛ τ.indVar)) :
    ∀ {σ : ProdExpr Sorts}, L.BoundedFormula α σ → L.BoundedFormula β (τ.prod σ)
  | _, falsum =>
      falsum
  | _, equal t₁ t₂ =>
      equal
        (t₁.relabelAux g )
        (t₂.relabelAux g )
  | _, rel R t =>
      rel R (t.relabelAux g)
  | _, imp φ ψ =>
      (relabel τ g φ).imp (relabel τ g ψ)
  | σ, @all _ _ _ _  ξ φ =>
      /-Relabelling φ places τ variables at the front of the free signature,
        which means that φ' will not be a product with a right ξ-factor. As
        a result we need to apply prodAssocR to φ' before we re-quantify-/
      let φ' : L.BoundedFormula β (τ.prod (σ.prod ξ)) :=
        relabel τ g φ
      let φ'' : L.BoundedFormula β ((τ.prod σ).prod ξ) :=
        prodAssocR τ σ ξ φ'
      φ''.all

def relabel_free_equiv (e : α ≃ₛ β) (σ : ProdExpr Sorts) :
    (α ⊕ₛ σ.indVar) ≃ₛ (β ⊕ₛ σ.indVar) :=
    (MSEquiv.fromEquivs (fun s =>
            (e.toEquiv s).sumCongr (_root_.Equiv.refl (σ.indVar s)))
          )

def relabel_free_equiv_inv (e : α ≃ₛ β) (σ : ProdExpr Sorts) :
    (β ⊕ₛ σ.indVar) ≃ₛ (α ⊕ₛ σ.indVar) :=
    (MSEquiv.fromEquivs (fun s =>
            (e.symm.toEquiv s).sumCongr (_root_.Equiv.refl (σ.indVar s)))
          )

--TODO: resolve Equiv namespace conflicts between MSLanguage and _root_
--because at present we have to write _root_.Equiv to refer to regular Equiv namespace.
def relabelEquiv (e : α ≃ₛ β) {σ : ProdExpr Sorts} :
    L.BoundedFormula α σ ≃ L.BoundedFormula β σ :=
  mapTermRelEquiv
    (ft :=
      fun σ _ =>
        Term.relabelEquiv (α := α ⊕ₛ σ.indVar ) (β := β ⊕ₛ σ.indVar)
          (relabel_free_equiv e σ)
    )
    (fr := fun _σ => _root_.Equiv.refl _)

@[simp]
theorem relabel_falsum {τ : ProdExpr Sorts} {g : α →ₛ β ⊕ₛ τ.indVar} {σ : ProdExpr Sorts} :
    (falsum : L.BoundedFormula α σ).relabel (τ := τ) g = falsum :=
  rfl

@[simp]
theorem relabel_bot {τ : ProdExpr Sorts} {g : α →ₛ β ⊕ₛ τ.indVar} {σ : ProdExpr Sorts} :
    (⊥ : L.BoundedFormula α σ).relabel (τ := τ) g = ⊥ :=
  rfl

@[simp]
theorem relabel_imp {τ : ProdExpr Sorts} {g : α →ₛ β ⊕ₛ τ.indVar}
    {σ : ProdExpr Sorts} (φ ψ : L.BoundedFormula α σ) :
    (φ.imp ψ).relabel (τ := τ) g = (φ.relabel (τ := τ) g).imp (ψ.relabel (τ := τ) g) := rfl

@[simp]
theorem relabel_not {τ : ProdExpr Sorts} {g : α →ₛ β ⊕ₛ τ.indVar}
    {σ : ProdExpr Sorts} (φ : L.BoundedFormula α σ) :
    (φ.not).relabel (τ := τ) g = (φ.relabel (τ := τ) g).not := by
  simp [BoundedFormula.not, relabel_bot, relabel_imp]

/--
This Lemma is only true up to associativity, so we have to apply prodAssocR to generalize it.
-/
@[simp]
theorem relabel_all
    (τ : ProdExpr Sorts) (g : α →ₛ (β ⊕ₛ τ.indVar))
    {σ ξ : ProdExpr Sorts}
    (φ : L.BoundedFormula α (σ.prod ξ)) :
    (φ.all).relabel (τ := τ) g =
      (prodAssocR τ σ ξ (φ.relabel (τ := τ) g)).all  := by
  rfl

@[simp]
theorem relabel_ex
    (τ : ProdExpr Sorts) (g : α →ₛ (β ⊕ₛ τ.indVar))
    {σ ξ : ProdExpr Sorts}
    (φ : L.BoundedFormula α (σ.prod ξ)) :
    (φ.ex (ξ := ξ)).relabel τ g = (prodAssocR τ σ ξ (φ.relabel _ g)).ex := by rfl


/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {σ}, L.BoundedFormula α σ → L.Formula α
  | .nil , φ => φ
  --We change the shape (of s) to nil.prod (of s) to prepare it for universal quantification:
  | .of s , φ => (castLE (L := L) (α:= α ) (VarEquiv.nilLeft (of s)).symm φ).all
  | .prod _ _  , φ => φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {σ}, L.BoundedFormula α σ → L.Formula α
  | .nil , φ => φ
  --We change the shape (of s) to nil.prod (of s) to prepare it for existential quantification:
  | .of s , φ => (castLE (L := L) (α:= α ) (VarEquiv.nilLeft (of s)).symm φ).ex
  | .prod _ _  , φ => φ.ex.exs

/-
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
-/

/-- Substitutes the variables in a given formula with terms. -/
def subst
    {σ : ProdExpr Sorts}
    (φ : L.BoundedFormula α σ)
    (f : ∀ s, α s → L.Term β (of s)) :
    L.BoundedFormula β σ :=
  φ.mapTermRel
    (ft :=
      fun (σ' ξ : ProdExpr Sorts)
          (t : L.Term (α ⊕ₛ σ'.indVar) ξ) =>
        t.subst
          (Fam.sumElim
            (fun s a => (f s a).relabel (fun _ => Sum.inl))
            (fun s v => Term.var s (Sum.inr v)))
    )
    (fr := fun _ R => R)
    (h := fun _ _ ψ => ψ)

/-- A bijection sending formulas with con
stants to formulas with extra variables. -/
def constantsVarsEquiv {σ : ProdExpr Sorts} :
    (L[[γ]]).BoundedFormula α σ ≃ L.BoundedFormula (γ ⊕ₛ α) σ :=
  BoundedFormula.mapTermRelEquiv
    (L := L[[γ]]) (L' := L)
    (α := α) (β := γ ⊕ₛ α)
    (ft := fun σ' _ => Term.constantsVarsEquivLeft (β := σ'.indVar))
    (fr := fun _ => Equiv.sumEmpty _ _)

/-

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
    ∀ {ξ : ProdExpr Sorts}, L.BoundedFormula α ξ → L'.BoundedFormula α ξ
  | _ξ, falsum => falsum
  | _ξ, BoundedFormula.equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | _ξ, rel R ts => (g.onRelation R).boundedFormula (g.onTerm ts)
  | _ξ, imp f₁ f₂ => (onBoundedFormula g f₁).imp (onBoundedFormula g f₂)
  | _ξ, all η f => all η (onBoundedFormula g f)

@[simp]
theorem id_onBoundedFormula :
    ((LHom.id L).onBoundedFormula : L.BoundedFormula α σ  → L.BoundedFormula α σ) = id := by
  ext f
  induction f with
  | falsum => rfl
  | equal => rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  | rel => simp only [onBoundedFormula, LHom.id_onTerm,id_onRelation,
    id, Relations.boundedFormula]
  | imp _ _ ih1 ih2 => rw [onBoundedFormula, ih1, ih2, id, id, id]
  | all _ _ ih3 => rw [onBoundedFormula, ih3, id, id]

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
  | all _ _ ih3 => simp only [ih3, onBoundedFormula, Function.comp_apply]

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

variable (l : List ℕ)

@[inherit_doc] scoped[MSFirstOrder] prefix:arg "∼" => MSFirstOrder.MSLanguage.BoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[MSFirstOrder] infixl:61 " ⇔ " => MSFirstOrder.MSLanguage.BoundedFormula.iff
-- input \<=>

@[inherit_doc] scoped[MSFirstOrder] prefix:110 "∃'" => MSFirstOrder.MSLanguage.BoundedFormula.ex
-- input \ex'

--TODO: move
section test

section experiments

variable {S : Type u}

/-- Checks whether a ProdExpr is nonempty and built from repeated uses of σ.prod (.of s),
  starting from nil -/
inductive IsStack : (σ : ProdExpr S) → Prop
  | nil : IsStack nil
  | snoc σ s (h₁ : IsStack σ) : IsStack (σ.prod (.of s))

abbrev PrependNil : (σ : ProdExpr S) → ProdExpr S
  | .nil => nil
  | .of s => nil.prod (.of s)
  | .prod σ₁ σ₂ => (PrependNil σ₁).prod σ₂

theorem prependNil_length_eq : (σ : ProdExpr S) → σ.length = (PrependNil σ).length
  | .nil => by rw [length_nil]
  | .of s => by simp only [length_of, length_prod, length_nil, zero_add]
  | .prod σ₁ σ₂ => by simp only [length_prod, prependNil_length_eq σ₁]

theorem isStack_of_prependNil_ofStack (σ : ProdExpr S) (h : IsStack σ) : IsStack (PrependNil σ) :=
  match h with
  | .nil => by simp only [PrependNil, IsStack.nil]
  | .snoc σ₁ s h₁ => by simp only [PrependNil, isStack_of_prependNil_ofStack σ₁ h₁,
    IsStack.snoc]

theorem prefix_of_stack (σ : ProdExpr S) (s : S) (h : IsStack (σ.prod (.of s))) : IsStack σ :=
  match h with
  | .snoc σ s h₁ => h₁

/-- Get the element at the i-th position (from the bottom) of the stack, along with directions
  in the form of and indVar object -/
@[reducible]
def getOfStack (σ : ProdExpr S) (h : IsStack σ) : (i : Fin σ.length) → Sigma σ.indVar :=
  match σ with
  | .nil => fun i => i.elim0
  | .of s => fun _ => ⟨s, .var⟩
  | .prod τ (.of s) => Fin.append
    (fun j => ⟨(getOfStack τ (prefix_of_stack τ s h) j).1,
      .left (getOfStack τ (prefix_of_stack τ s h) j).2 ⟩)
    (fun _ => ⟨s, .right .var⟩)

def getIndVarOfStack (σ : ProdExpr S) (h : IsStack σ) (i : Fin σ.length) :
    σ.indVar (getOfStack σ h i).1 :=
  (getOfStack σ h i).2

abbrev FinGet (σ : ProdExpr S) : (i : Fin σ.length) → Sigma σ.indVar :=
  match σ with
  | .nil => elim0
  | .of s => fun _ => ⟨s, .var⟩
  | .prod σ₁ σ₂ => Fin.append
    (fun i => ⟨(FinGet σ₁ i).1, .left (FinGet σ₁ i).2⟩)
    (fun j => ⟨(FinGet σ₂ j).1, .right (FinGet σ₂ j).2⟩)

/-- Whether the ProdExpr only has factors nil. Equivalently, its normalized form is nil -/
inductive IsTrivial : (σ : ProdExpr S) → Prop
  | nil : IsTrivial nil
  | prod σ₁ σ₂ (h₁ : IsTrivial σ₁) (h₂ : IsTrivial σ₂) : IsTrivial (σ₁.prod σ₂)

/-- Whether the ProdExpr only has factors nil. Equivalently, its normalized form is nil -/
inductive neTrivial : (σ : ProdExpr S) → Prop
  | of s : neTrivial (.of s)
  | prodLeft σ₁ σ₂ (h₁ : neTrivial σ₁) : neTrivial (.prod σ₁ σ₂)
  | prodRight σ₁ σ₂ (h₂ : neTrivial σ₂) : neTrivial (.prod σ₁ σ₂)

instance instLengthNeZero (σ : ProdExpr S) (h : neTrivial σ) : NeZero σ.length :=
  match h with
  | .of s => Nat.instNeZeroSucc
  | .prodLeft σ₁ σ₂ h₁ => by
    letI := instLengthNeZero σ₁ h₁
    rw [ProdExpr.length_prod, neZero_iff]
    exact Ne.symm (NeZero.ne' (σ₁.length + σ₂.length))
  | .prodRight σ₁ σ₂ h₂ => by
    letI := instLengthNeZero σ₂ h₂
    rw [ProdExpr.length_prod, neZero_iff]
    exact Ne.symm (NeZero.ne' (σ₁.length + σ₂.length))

end experiments

abbrev cL : MSLanguage (Fin 2) where
  Functions := fun _ _ => Empty
  Relations := fun _ => Empty

abbrev η : ProdExpr (Fin 2) := of 0

instance : NeZero η.length := Nat.instNeZeroSucc
instance : NeZero (nil.prod η).length := Nat.instNeZeroSucc


def mkVar' {α : Sorts → Type*} (σ : ProdExpr Sorts)
    {h : IsStack (PrependNil σ)} (i : Fin σ.length) : Term L (α ⊕ₛ (PrependNil σ).indVar)
    (.of (getOfStack (PrependNil σ) h (Fin.cast (prependNil_length_eq σ) i)).1) :=
  Term.var (getOfStack (PrependNil σ)  _ (Fin.cast (prependNil_length_eq σ) i)).1
  (Sum.inr (getOfStack (PrependNil σ) h (Fin.cast (prependNil_length_eq σ) i)).2)


def mkVar {α : Sorts → Type*} (σ : ProdExpr Sorts) (i : Fin (PrependNil σ).length) :
    Term L (α ⊕ₛ (PrependNil σ).indVar) (.of (FinGet (PrependNil σ) i).1) :=
  Term.var (FinGet (PrependNil σ) i).1 (Sum.inr (FinGet (PrependNil σ) i).2)

/-- `σ&i` is notation for the `n`-th free variable,
  from the corresponding sort determined by a signature σ-/
scoped[MSFirstOrder] infix:arg "&" => MSLanguage.mkVar

/- Example Sentence-/
example : cL.Sentence :=
  (∀' η)
  ((Term.var 0 (Sum.inr (getOfStack (nil.prod η) (by simp[IsStack.snoc,IsStack.nil]) 0).2)) ='
  (Term.var 0 (Sum.inr (.right .var))))

example : cL.Sentence := (∀' η) ((∀' η) (Term.var _ (Sum.inr (.right .var)) ='
  Term.var _ (Sum.inr (.left <| .right .var))))

example : cL.Sentence :=
  have : IsStack (PrependNil η) :=  by simp only [IsStack.snoc,IsStack.nil]
  (∀' (.of 0)) ((mkVar' (h := this) η 0) =' (mkVar' (h := this) η 0))

example : cL.Sentence := (∀' (.of 0)) ((mkVar η 0) =' (mkVar η 0))
abbrev χ := η.prod η

example : cL.Sentence :=
  have : neTrivial (PrependNil χ) := .prodRight _ (.of _) (neTrivial.of _)
  letI := instLengthNeZero (PrependNil χ) this
  /-Note: we cannot use mkVar here, as quantifying over χ requires something of shape nil.prod χ
   rather than something of shape PrependNil χ-/
  (∀' χ) ( (Term.var 0 (Sum.inr (.right <| .left .var))) ='
  Term.var 0 (Sum.inr (.right <| .right .var)))
  --(∀' η) ((∀' η) ((mkVar χ 0) =' (mkVar χ 0)))

end test

namespace Formula

/-- Relabels a formula's variables along a particular function.
    This is a little delicate to write down for technical reasons
    related to nil products.
-/
def relabel (g : α →ₛ β) : L.Formula α → L.Formula β :=
  /-(BoundedFormula.castLE  (VarEquiv.nilLeft nil)) is needed
  because relabel always wants to add extra variables. Without the cast,
  the type after applying relabel is:

  `L.BoundedFormula β (ProdExpr.nil.prod ProdExpr.nil)`

  so an application of `(BoundedFormula.castLE  (VarEquiv.nilLeft nil))`
  reduces this down to

  `L.BoundedFormula β ProdExpr.nil`

  as desired.
  -/
  (BoundedFormula.castLE  (VarEquiv.nilLeft nil)) ∘
  (@BoundedFormula.relabel _ β L α .nil (fun s => Sum.inl ∘ g s) .nil)

/-
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
