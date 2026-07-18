import MultisortedLogic.LanguageMap
import MultisortedLogic.SortedTuple

/-
Based on the corresponding Mathlib file Mathlib\ModelTheory\Syntax.lean
which was authored by 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn,
and is released under the Apache 2.0 license.

For the Flypitch project:
- [J. Han, F. van Doorn, A formal proof of the independence of the continuum hypothesis]
  [flypitch_cpp]
- [J. Han, F. van Doorn, A formalization of forcing and the unprovability of
  the continuum hypothesis][flypitch_itp]
-/

universe u v w z u' v' w'

namespace MSFirstOrder

namespace Language

variable {Sorts : Type z} {L : Language.{u, v, z} Sorts} {L' : Language Sorts}
variable {M : Sorts → Type w} {α : Fam.{u'} Sorts} {γ : Fam Sorts}

open Structure Fin Fam Signature
open Interpret

/-- A term on `α` is either a variable indexed by an element of `α`,
    a function symbol applied to simpler terms, or a product of terms.
-/
inductive Term (L : Language.{u, v, z} Sorts) (α : Fam.{u'} Sorts) :
    Signature Sorts → Type max z u' u where
| var (s : Sorts) : α s → L.Term α (of s)
| func {σ : Signature Sorts} {t : Sorts} (f : L.Functions σ t) (r : L.Term α σ) : L.Term α (.of t)
| prod {σ τ : Signature Sorts} : L.Term α σ → L.Term α τ → L.Term α (σ ⨯ τ)
| nil : L.Term α .nil

/-- A term of a single sort `s`. Shorthand for `L.Term α (of s)`. -/
abbrev Term₁ (L : Language.{u, v, z} Sorts) (α : Fam.{u'} Sorts) : Fam Sorts :=
  ⟨fun s => L.Term α ⦃s⦄⟩

/--
Needed in some cases to show termination for recursion on terms
-/
def Term.size : {σ : Signature Sorts} → L.Term α σ → Nat
    | _, .nil            => 2
    | _, .var _ _        => 1
    | _, .func _ ts      => 2 + ts.size
    | _, .prod t₁ t₂     => 1 + Term.size t₁ + Term.size t₂

namespace Term

/-- Recursive helper for establishing `DecidableEq` on terms: -/
def decEqTerm
  [DecidableEq Sorts]
  [∀ s, DecidableEq (α s)]
  [∀ σ t, DecidableEq (L.Functions σ t)] :
  {σ : Signature Sorts} → (t₁ t₂ : L.Term α σ) → Decidable (t₁ = t₂)
| .nil, .nil, .nil =>
    isTrue rfl
| .of s, .var _ x₁, .var _ x₂ =>
    match decEq x₁ x₂ with
    | isTrue h  => isTrue (by cases h; rfl)
    | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
| .of s, .var _ _, .func _ _ =>
    isFalse (by intro hEq; cases hEq)
| .of s, .func _ _, .var _ _ =>
    isFalse (by intro hEq; cases hEq)
| .of s,
    .func (σ := σ₁) (t := _) f₁ r₁,
    .func (σ := σ₂) (t := _) f₂ r₂ =>
    match decEq σ₁ σ₂ with
    | isFalse hσ =>
        isFalse (by intro hEq; cases hEq; exact hσ rfl)
    | isTrue hσ =>
        by
          cases hσ
          match decEq f₁ f₂ with
          | isFalse hf =>
              exact isFalse (by intro hEq; cases hEq; exact hf rfl)
          | isTrue hf =>
              cases hf
              match decEqTerm (σ := σ₁) r₁ r₂ with
              | isTrue hr  => exact isTrue (by cases hr; rfl)
              | isFalse hr => exact isFalse (by intro hEq; cases hEq; exact hr rfl)
| .prod σ τ, .prod t₁₁ t₁₂, .prod t₂₁ t₂₂ =>
    match decEqTerm (σ := σ) t₁₁ t₂₁ with
    | isFalse h1 =>
        isFalse (by intro hEq; cases hEq; exact h1 rfl)
    | isTrue h1 =>
        match decEqTerm (σ := τ) t₁₂ t₂₂ with
        | isFalse h2 =>
            isFalse (by intro hEq; cases hEq; exact h2 rfl)
        | isTrue h2 =>
            isTrue (by cases h1; cases h2; rfl)

instance instDecidableEq
  [DecidableEq Sorts]
  [∀ s, DecidableEq (α s)]
  [∀ σ t, DecidableEq (L.Functions σ t)] :
  ∀ σ, DecidableEq (L.Term α σ) :=
by
  intro σ t₁ t₂
  exact decEqTerm t₁ t₂

section term_monad
/-We can think of Terms as dependent monad-like structures over their variables, with
  `Term.var` functioning as `pure` and `Term.bind` defined in this section.-/

/-- Binds a term assignment to variables in a term -/
@[simp]
def bind {β : Fam Sorts} {σ} : L.Term α σ → (α →ₛ L.Term₁ β) → L.Term β σ
  | nil , _     => nil
  | var t a, tf => tf t a
  | func f ts, tf => func f (ts.bind tf)
  | prod t₁ t₂, tf => prod (t₁.bind tf) (t₂.bind tf)


/-- Relabels a term's variables along a particular function -/
@[simp]
def mapVars {β : Fam Sorts} {σ : Signature Sorts} (g : α →ₛ β) : L.Term α σ → L.Term β σ :=
  fun t => t.bind ⟨fun s a => .var s (g s a)⟩

lemma mapVars_func {s : Sorts} {β : Fam Sorts} {σ : Signature Sorts} {f : α →ₛ β}
    {g : L.Functions σ s} {ts : L.Term α σ} : mapVars f (func g ts) = func g (ts.mapVars f) := by
  simp_all only [mapVars, bind]

theorem mapVars_injective_of_injective {β : Fam Sorts} {σ : Signature Sorts} {f : α →ₛ β}
    (h : ∀ s, Function.Injective (f s)) :
    Function.Injective (mapVars f : L.Term α σ → L.Term β σ) := by
  intro t₁ t₂ heq
  induction t₁ with
  | nil => cases t₂; simp_all only [mapVars, bind]
  | var s a => cases t₂ with
    | var =>
      have hs : Function.Injective (f s) := h s
      rw [var.injEq]
      simp only [mapVars, bind, FamMap.mk_apply, var.injEq] at heq
      apply hs heq
    | func => simp_all only [mapVars, bind, FamMap.mk_apply, reduceCtorEq]
  | func g ts ih => cases t₂ with
    | var => simp_all only [mapVars, bind, FamMap.mk_apply, reduceCtorEq]
    | func h rs =>
      rw [mapVars_func, mapVars_func] at heq
      simp_all only [mapVars, func.injEq, true_and]
      obtain ⟨hσ, ⟨hg, heq'⟩⟩ := heq
      subst hσ
      simp_all only [heq_eq_eq]
      subst hg
      apply ih
      simp_all only
  | prod r₁ r₂ ih₁ ih₂ =>
    cases t₂ with
    | prod =>
      simp_all only [mapVars, bind, prod.injEq]
      obtain ⟨heq₁, heq₂⟩ := heq
      apply And.intro
      · apply ih₁
        simp_all only
      · apply ih₂
        simp_all only

variable {β : Fam Sorts} {t : Sorts} {σ : Signature Sorts}

def varOf (g : α →ₛ β) : α →ₛ L.Term₁ β :=
  ⟨fun s a => Term.var s (g s a)⟩

/-- Associativity of bind -/
@[simp]
theorem bind_bind (t : Term L α σ)
    (f : α →ₛ L.Term₁ β)
    (g : β →ₛ L.Term₁ γ) :
    (t.bind f).bind g = t.bind ⟨fun s a => (f s a).bind g⟩ := by
  induction t <;> simp_all only [bind, FamMap.mk_apply]

theorem bind_id {f : α →ₛ L.Term₁ α}
  (t : Term L α σ) (h : ∀ s a, f s a = var s a) : t.bind f = t := by
  induction t  <;> simp_all only [bind]

/-- Applying bind on the variable map is the identity (right monad law) -/
@[simp]
theorem bind_var (t : Term L α σ) :
    t.bind ⟨fun s a => var s a⟩ = t := by
  induction t <;> simp_all only [bind, FamMap.mk_apply]

/-- Applying bind to a variable (left monad identity) -/
@[simp]
theorem var_bind (s : Sorts) (a : α s) (f : α →ₛ L.Term₁ β) :
    (var s a).bind f = f s a := rfl

theorem mapVars_id {f : L.Term α σ} : mapVars (Fam.FamMap.idₛ) f = f := by
  simp only [mapVars, FamMap.idₛ_apply', bind_var]

@[simp]
theorem mapVars_id_eq_id : (mapVars (fun s => @id (α s)) : L.Term α σ → L.Term α σ) = id := by
  ext f
  apply bind_id
  intro s a
  simp_all only [FamMap.mk_apply]
  rfl

@[simp]
theorem mapVars_mapVars (f : α →ₛ β) (g : β →ₛ γ) (t : L.Term α σ) :
    mapVars g (mapVars f t) = mapVars (g ∘ₛ f) t := by
  induction t with
  | var => rfl
  | func _ _ ih => simp_all only [mapVars,  bind]
  | prod t₁ t₂ ih₁ ih₂ => simp_all only [mapVars,  bind]
  | nil => rfl

@[simp]
theorem mapVars_comp_mapVars (f : α →ₛ β) (g : β →ₛ γ) :
    (mapVars g ∘ mapVars f : L.Term α σ → L.Term γ σ) = mapVars (g ∘ₛ f) :=
  funext (mapVars_mapVars f g)

/-- Relabels a term's variables along a bijection. -/
@[simps]
def mapVarsEquiv (g : α ≃ₛ β) : L.Term α σ ≃ L.Term β σ :=
  ⟨mapVars g,
   mapVars g.symm,
  fun x => by
    have hcomp : ((g.symm : β →ₛ α) ∘ₛ (g : α →ₛ β)) = FamMap.idₛ := by
      ext s a
      change g.symm s (g s a) = a
      exact MSEquiv.symm_toFun_toFun g s a
    calc
      mapVars g.symm (mapVars g x)
          = mapVars ((g.symm : β →ₛ α) ∘ₛ (g : α →ₛ β)) x := by
              exact mapVars_mapVars (f := (g : α →ₛ β)) (g := (g.symm : β →ₛ α)) (t := x)
      _ = mapVars (FamMap.idₛ (α := α)) x := by
            exact congrArg (fun h => mapVars h x) hcomp
      _ = x := by
            exact mapVars_id (f := x)
    ,
    fun x => by
      have hcomp : ((g : α →ₛ β) ∘ₛ (g.symm : β →ₛ α)) = FamMap.idₛ := by
        ext s a
        change g s (g.symm s a) = a
        exact MSEquiv.toFun_symm_toFun g s a
      calc
        mapVars g (mapVars g.symm x)
            = mapVars ((g : α →ₛ β) ∘ₛ (g.symm : β →ₛ α)) x := by
                exact mapVars_mapVars (f := (g.symm : β →ₛ α)) (g := (g : α →ₛ β)) (t := x)
        _ = mapVars (FamMap.idₛ (α := β)) x := by
              exact congrArg (fun h => mapVars h x) hcomp
        _ = x := by
              exact mapVars_id (f := x)⟩

@[simp]
lemma mapVars_size {β σ} (g : α →ₛ β) (t : L.Term α σ) : (t.mapVars g).size = t.size := by
  induction t <;> simp_all only [FamMap.mk_apply, mapVars, bind, size]

end term_monad

section renaming_and_reindexing

variable {β δ : Fam Sorts} {t : Sorts} {σ ξ τ η : Signature Sorts}


/-- Relabel the sum type variables along a map of left summands -/
def rename {β : Fam Sorts} {σ : Signature Sorts} (g : α →ₛ β) :
    L.Term (α ⊕ₛ γ) σ → L.Term (β ⊕ₛ γ) σ :=
  mapVars (Fam.sumMap g FamMap.idₛ)

def reindex {τ η σ : Signature Sorts} (g : SigMap τ η) :
    L.Term (α ⊕ₛ τ.IdxFam) σ → L.Term (α ⊕ₛ η.IdxFam) σ :=
  mapVars (Fam.sumMap FamMap.idₛ g)

@[simp]
theorem rename_id (t : L.Term (α ⊕ₛ γ) σ) : t.rename (Fam.FamMap.idₛ) = t := by
  apply bind_id
  intro s a
  cases a <;> rfl

@[simp]
theorem rename_rename (t : L.Term (α ⊕ₛ γ) σ) (f : α →ₛ β) (g : β →ₛ δ) :
  (t.rename f).rename g = t.rename (g ∘ₛ f) := by
  unfold rename mapVars
  simp only [FamMap.mk_apply, bind_bind, bind]
  congr
  ext s w
  cases w <;> rfl

@[simp]
theorem reindex_id (t : L.Term (α ⊕ₛ σ.IdxFam) τ) : t.reindex FamMap.idₛ = t := by
  apply bind_id
  intro s a
  cases a <;> rfl

@[simp]
theorem reindex_reindex (t : L.Term (α ⊕ₛ σ.IdxFam) ξ) (f : SigMap σ τ) (g : SigMap τ η) :
  (t.reindex f).reindex g = t.reindex (g ∘ₛ f) := by
  unfold reindex mapVars
  simp only [FamMap.mk_apply, bind_bind, bind]
  congr
  ext s w; cases w
  · simp_all only [sumMap_inl_apply, FamMap.idₛ_apply']
  · rfl

variable {τ : Signature Sorts}

@[simp] theorem reindex_var_inl (s : Sorts) (a : α s) (g : SigMap σ τ) :
  (var s (Sum.inl a) : Term L (α ⊕ₛ σ.IdxFam) (of s)).reindex g
    = var s (Sum.inl a) := by
  rfl

@[simp] theorem reindex_var_inr (s : Sorts) (v : σ.IdxFam s) (g : SigMap σ τ) :
  (var s (Sum.inr v) : Term L (α ⊕ₛ σ.IdxFam) (of s)).reindex g
    = var s (Sum.inr (g s v)) := by
  rfl

@[simp] theorem reindex_func {ρ : Signature Sorts} {t : Sorts}
  (F : L.Functions ρ t) (ts : Term L (α ⊕ₛ σ.IdxFam) ρ) (g : SigMap σ τ) :
  (func F ts).reindex g = func F (ts.reindex g) := by
  simp only [reindex, mapVars, bind]

@[simp] theorem reindex_prod {ρ η : Signature Sorts}
  (t₁ : Term L (α ⊕ₛ σ.IdxFam) ρ) (t₂ : Term L (α ⊕ₛ σ.IdxFam) η) (g : SigMap σ τ) :
  (prod t₁ t₂).reindex g = prod (t₁.reindex g) (t₂.reindex g) := by
  simp only [reindex, mapVars, bind]

@[simp] theorem reindex_nil (g : SigMap σ τ) :
  (nil : Term L (α ⊕ₛ σ.IdxFam) .nil).reindex g = nil := by
  simp only [reindex, mapVars, bind]

@[simp]
theorem rename_var_inl (s : Sorts) (a : α s) (f : α →ₛ β) :
    (var s (Sum.inl a) : Term L (α ⊕ₛ σ.IdxFam) (of s)).rename f = var s (Sum.inl (f s a)) := by
  rfl

@[simp]
theorem rename_var_inr (s : Sorts) (v : σ.IdxFam s) (f : α →ₛ β) :
    (var s (Sum.inr v) : Term L (α ⊕ₛ σ.IdxFam) (of s)).rename f = var s (Sum.inr v) := by
  rfl

@[simp]
theorem rename_func {τ : Signature Sorts} {t : Sorts}
    (g : L.Functions τ t) (ts : Term L (α ⊕ₛ σ.IdxFam) τ) (f : α →ₛ β) :
    (func g ts).rename f = func g (ts.rename f) := by
  simp only [rename, mapVars, bind]

@[simp]
theorem rename_prod {τ η : Signature Sorts}
    (t₁ : Term L (α ⊕ₛ σ.IdxFam) τ) (t₂ : Term L (α ⊕ₛ σ.IdxFam) η) (f : α →ₛ β) :
    (prod t₁ t₂).rename f = prod (t₁.rename f) (t₂.rename f) := by
  simp only [rename, mapVars, bind]

@[simp]
theorem rename_nil (f : α →ₛ β) :
    (nil : L.Term (α ⊕ₛ γ) .nil).rename f = nil := by
    simp only [rename, mapVars, bind]

@[simp]
lemma reindex_rename {β : Fam Sorts} {σ τ ξ : Signature Sorts}
    (g : SigMap σ τ)
    (t : L.Term (α ⊕ₛ σ.IdxFam) ξ)
    (f : α →ₛ β) :
    (t.rename f).reindex g = (t.reindex g).rename f := by
    simp only [reindex, mapVars, rename, FamMap.mk_apply, bind_bind, bind]
    congr
    ext s w
    cases w
    · simp_all only [sumMap_inl_apply, FamMap.idₛ_apply']
    · rfl

/-- Renaming variables by an injective mapping is injective. -/
theorem rename_injective_of_injective {f : α →ₛ β} (h : ∀ s, Function.Injective (f s)) :
    Function.Injective (rename f : L.Term (α ⊕ₛ τ.IdxFam) σ → L.Term (β ⊕ₛ τ.IdxFam) σ) :=
  mapVars_injective_of_injective (fun s => (h s).sumMap Function.injective_id)

end renaming_and_reindexing

end Term

section term_constructors

def Term.varTerm : ∀ σ : Signature Sorts, Term L (IdxFam σ) σ
  | .nil =>
      .nil
  | .of s =>
      .var s Idx.var
  | .prod σ τ =>
      let leftTerm  : L.Term (IdxFam (σ ⨯ τ)) σ :=
        mapVars ⟨fun s v => Idx.left (σ := σ) (τ := τ) (s := s) v⟩
          (varTerm σ)
      let rightTerm : L.Term (IdxFam (σ ⨯ τ)) τ :=
        mapVars ⟨fun s v => Idx.right (σ := σ) (τ := τ) (s := s) v⟩
          (varTerm τ)
      .prod leftTerm rightTerm

/--
Given (t: Term α σ) and (v : σ.IdxFam s), we want to recover the term in t at position v.
  This is the direct analogue of `get` for SortedTuples on the semantic side.
-/
def Term.getLeafTerm {σ : Signature Sorts} (t : L.Term α σ) : σ.IdxFam →ₛ L.Term₁ α :=
  ⟨fun s v =>
    match t with
    | nil => isEmptyElim v
    | var s t =>
        match v with
        | Idx.var => var s t
    | func f r =>
        match v with
        | Idx.var => func f r
    | prod t₁ t₂ =>
      match v with
      | Idx.left w => getLeafTerm t₁ s w
      | Idx.right w => getLeafTerm t₂ s w ⟩

-- Simp lemmas for each case of getLeafTerm
@[simp]
theorem getLeafTerm_nil (s : Sorts) (v : Signature.nil.IdxFam s) :
    (Term.nil : L.Term α .nil).getLeafTerm s v = isEmptyElim v := rfl

@[simp]
theorem getLeafTerm_var (s : Sorts) (x : α s) :
    (Term.var s x : L.Term α ⦃s⦄).getLeafTerm s Idx.var = Term.var s x := rfl

@[simp]
theorem getLeafTerm_func {t} {σ : Signature Sorts} (f : L.Functions σ t) (r : L.Term α σ) :
    (Term.func f r).getLeafTerm t Idx.var = Term.func f r := rfl

@[simp]
theorem getLeafTerm_prod_left {σ τ : Signature Sorts} (t₁ : L.Term α σ) (t₂ : L.Term α τ)
    (s : Sorts) (w : σ.IdxFam s) :
    (Term.prod t₁ t₂).getLeafTerm s (Idx.left w) = t₁.getLeafTerm s w := rfl

@[simp]
theorem getLeafTerm_prod_right {σ τ : Signature Sorts} (t₁ : L.Term α σ) (t₂ : L.Term α τ)
    (s : Sorts) (w : τ.IdxFam s) :
    (Term.prod t₁ t₂).getLeafTerm s (Idx.right w) = t₂.getLeafTerm s w := rfl

lemma Term.ext {σ : Signature Sorts}
    (t₁ t₂ : L.Term α σ) (h : ∀ s v, t₁.getLeafTerm s v = t₂.getLeafTerm s v) : t₁ = t₂ := by
  induction t₁ <;> cases t₂
  case var s x y  =>
    simpa[getLeafTerm_var, Term.var.injEq s] using h s (Idx.var )
  case func s v t f a =>
    · simpa[getLeafTerm_func, Term.var.injEq s] using h s (Idx.var )
  case func.var τ s f t h a =>
    simpa using h s Idx.var
  case func.func σ s f t h σ' t' f' =>
    · set t0 := func f t
      set t1 := func f' t'
      exact h s Idx.var
  case prod.prod t₁ t₂ ih₁ ih₂ t₃ t₄  =>
    congr!
    · apply ih₁; intro s v ; simpa using h s v.left
    · apply ih₂; intro s v ; simpa using h s v.right
  case nil => simp only

/-- Constructed whilst making the Henkin model, sorry if this is a bad function to have . -/
def Term.fromFam (σ : Signature Sorts)
  (ts : σ.Interpret ⟨fun (s : Sorts) => L.Term α (of s)⟩) :  L.Term α σ  :=
  match σ, ts with
  | .nil, _ => Term.nil
  | .of _, t => t
  | .prod σ₁ σ₂, (t₁, t₂) => (fromFam σ₁ t₁).prod (fromFam σ₂ t₂)

@[simp]
lemma Term.fromFam_nil
  {ts : ⦃⦄.Interpret ⟨fun (s : Sorts) => L.Term α (of s)⟩} : Term.fromFam .nil ts = Term.nil := rfl

@[simp]
lemma Term.fromFam_of {s} {t : ⦃s⦄.Interpret ⟨fun (s : Sorts) => L.Term α (of s)⟩} :
  Term.fromFam (.of s) t = t := rfl

@[simp]
lemma Term.fromFam_prod {σ₁ σ₂} (t₁ : σ₁.Interpret ⟨fun (s : Sorts) => L.Term α (of s)⟩)
    (t₂ : σ₂.Interpret ⟨fun (s : Sorts) => L.Term α (of s)⟩) :
    Term.fromFam (σ₁.prod σ₂) (t₁,t₂) = (fromFam σ₁ t₁).prod (fromFam σ₂ t₂) := rfl

variable {s₁ s₂ : Sorts} {t : Sorts}
open Term Signature

/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants t) : L.Term₁ α t :=
  func c nil

/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions ⦃s₁⦄ s₂) (t : L.Term₁ α s₁) : L.Term₁ α s₂ :=
  func f t

/-- Applies a binary function to two terms. -/
def Functions.apply₂ {s₁ s₂ : Sorts} (f : L.Functions (⦃s₁⦄ ⨯ ⦃s₂⦄) t)
   (g₁ : L.Term₁ α s₁) (g₂ : L.Term₁ α s₂) : L.Term₁ α t :=
   func f (prod g₁ g₂)

/- The representation of a function symbol as a term, on fresh variables indexed by `IdxFam σ` -/
def Functions.term {σ : Signature Sorts} {t : Sorts} (f : L.Functions σ t) : L.Term₁ (IdxFam σ) t
   := func f (varTerm σ)

end term_constructors

namespace Term

instance IdxFamNilEmpty {s : Sorts} : IsEmpty (IdxFam .nil s) := by
  constructor
  intro a
  cases a

instance IdxFamofInhabited {s : Sorts} : Inhabited (IdxFam (of s) s) where
  default := Idx.var

instance IdxFamofUnique {s : Sorts} : Unique (IdxFam (of s) s) := by
  constructor
  · intro a
    cases a
    case var => rfl

/-- Sends a term with constants to a term with extra variables. -/
@[simp]
def constantsToVars {σ : Signature Sorts} : L[[γ]].Term α σ → L.Term (γ ⊕ₛ α) σ
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
def varsToConstants {σ : Signature Sorts}
 : L.Term (γ ⊕ₛ α) σ → L[[γ]].Term α σ
  | var t (Sum.inr a : (γ ⊕ₛ α) t)  => var t a
  | var _t (Sum.inl a : (γ ⊕ₛ α) _t) => Constants.term (Sum.inr a)
  | func (t := t) f ts => func (Sum.inl f) ts.varsToConstants
  | nil => nil
  | prod t₁ t₂ => prod (t₁.varsToConstants) (t₂.varsToConstants)

/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
def constantsVarsEquiv {τ : Signature Sorts} : L[[γ]].Term α τ ≃ L.Term (γ ⊕ₛ α) τ :=
  ⟨constantsToVars,
  varsToConstants,
  (by
    intro t
    induction t
    case var s t => simp_all only [constantsToVars, varsToConstants]
    case func σ t f ts ih =>
      match f with
      | Sum.inl f => simp_all only [constantsToVars, varsToConstants]
      | Sum.inr c =>
          cases σ <;> cases ts
          · simp_all only [constantsToVars, varsToConstants]
            rfl
          · exact isEmptyElim c
          · exact isEmptyElim c
          · exact isEmptyElim c
    case nil => simp_all only [constantsToVars, varsToConstants]
    case prod t₁ t₂ => simp_all only [constantsToVars, varsToConstants]
  ),
  (by
    intro t
    induction t
    case var s t =>
      cases t with
      | inl val =>
        simp_all only [varsToConstants]
        rfl
      | inr val_1 => simp_all only [varsToConstants, constantsToVars]
    case func σ t f ts ih =>
        simp_all only [varsToConstants, constantsToVars]
    case nil => simp_all only [constantsToVars, varsToConstants]
    case prod t₁ t₂ => simp_all only [constantsToVars, varsToConstants]
  ) ⟩

variable {σ τ : Signature Sorts} {t : Sorts}

/-- A bijection between terms with constants and terms with extra variables. -/
def constantsVarsEquivLeft {β : Fam Sorts} :
    L[[γ]].Term (α ⊕ₛ β) σ ≃ L.Term ((γ ⊕ₛ α) ⊕ₛ β ) σ :=
  (constantsVarsEquiv).trans (mapVarsEquiv (MSEquiv.fromEquivs fun _ => Equiv.sumAssoc _ _ _)).symm

@[simp]
theorem constantsVarsEquivLeft_apply {β : Fam Sorts} (g : L[[γ]].Term (α ⊕ₛ β) σ) :
    constantsVarsEquivLeft g =
    (constantsToVars g).mapVars ⟨fun _ => (Equiv.sumAssoc _ _ _).invFun⟩  := rfl

@[simp]
theorem constantsVarsEquivLeft_symm_apply {β : Fam Sorts} (g : L.Term ((γ ⊕ₛ α) ⊕ₛ β) σ) :
    (constantsVarsEquivLeft).symm g = varsToConstants (g.mapVars ⟨fun _ => Equiv.sumAssoc _ _ _⟩) :=
  rfl

instance inhabitedOfVar [Inhabited (α t)] : Inhabited (L.Term₁ α t) :=
  ⟨var t default⟩


instance inhabitedOfConstant [Inhabited (L.Constants t)] : Inhabited (L.Term₁ α t) :=
  ⟨Constants.term (L := L) (α := α) (t := t) (default : L.Constants t)⟩


section substitution

variable {β : Fam Sorts} {σ : Signature Sorts}


/-- Substitution of named variables via an assignment from names to terms. -/
def subst {β : Fam Sorts} {σ : Signature Sorts} {τ : Signature Sorts}
  (t : L.Term (α ⊕ₛ σ.IdxFam) τ)
  (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
  L.Term (β ⊕ₛ σ.IdxFam) τ:=
  t.bind (Fam.sumElim f (varOf Fam.inr))

@[simp]
theorem subst_id (t : Term L (α ⊕ₛ σ.IdxFam) τ) :
    t.subst ⟨fun s a => var s (Sum.inl a)⟩ = t := by
  induction t <;> simp_all only [subst, bind]
  rename_i a
  cases a with
  | inl val => rfl
  | inr val_1 => rfl

@[simp]
theorem subst_var_inl (s : Sorts) (a : α s)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (var s (Sum.inl a)).subst f = f s a := by
  simp only [subst, bind]
  rfl
/--
Substituting a bound/context variable `inr v` leaves it unchanged.
-/
@[simp]
theorem subst_var_inr (s : Sorts) (v : σ.IdxFam s)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (var s (Sum.inr v)).subst f = var s (Sum.inr v) := by
  rfl

/--
Substitution pushes through function applications.
-/
@[simp]
theorem subst_func {τ : Signature Sorts} {t : Sorts}
    (g : L.Functions τ t) (ts : Term L (α ⊕ₛ σ.IdxFam) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (func g ts).subst f = func g (ts.subst f) := by
  simp only [subst, bind]

/--
Substitution pushes through product terms.
-/
@[simp]
theorem subst_prod {τ η : Signature Sorts}
    (t₁ : Term L (α ⊕ₛ σ.IdxFam) τ) (t₂ : Term L (α ⊕ₛ σ.IdxFam) η)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (prod t₁ t₂).subst f = prod (t₁.subst f) (t₂.subst f) := by
  simp only [subst, bind]

/--
Opens bound variables in a term by splitting the rightmost block of bound variables.

Transforms a term `L.Term (α ⊕ₛ (η ⨯ τ).IdxFam) σ` into `L.Term ((α ⊕ₛ τ.IdxFam) ⊕ₛ η.IdxFam) σ`
by replacing `(η ⨯ τ).IdxFam` variables with a sum where:
- Variables from `η` (left block) become free variables on the right: `Sum.inr`
- Variables from `τ` (right block) become bound variables on the left: `Sum.inl (Sum.inr ...)`
- Original free variables `α` remain as `Sum.inl (Sum.inl ...)`

This is used to "open" a block of quantified variables, making them available as free variables.
The inverse operation is `instantiate` which substitutes terms back in.

⨯⨯Example use case⨯⨯: Opening the innermost quantifier block in nested quantifications.
-/
def openVars {τ η : Signature Sorts} {σ} :
              L.Term (α ⊕ₛ (η ⨯ τ).IdxFam) σ →
               L.Term ((α ⊕ₛ τ.IdxFam) ⊕ₛ η.IdxFam) σ :=
  let f : (α ⊕ₛ (η ⨯ τ).IdxFam) →ₛ
          ⟨fun s => L.Term ((α ⊕ₛ τ.IdxFam) ⊕ₛ η.IdxFam) (of s)⟩ :=
    Fam.sumElim
        (varOf
          (Fam.inl (α:= α ⊕ₛ τ.IdxFam) ∘ₛ Fam.inl (α:= α))
        )
        ⟨fun s (v : (η ⨯ τ).IdxFam s) =>
          match v with
          | .left w => .var s (Sum.inr w)
          | .right w => .var s (Sum.inl (Sum.inr w))
        ⟩
  fun ts =>
    ts.bind (L := L) f

/--
Substitutes the block of bound variables `η` (the rightmost factor of the Signature)
with the `η`-shaped term `u`.
-/
def instantiate {η : Signature Sorts} {ρ : Signature Sorts}
    (t : L.Term (α ⊕ₛ (σ ⨯ η).IdxFam) ρ)
    (u : L.Term (α ⊕ₛ σ.IdxFam) η) :
      L.Term (α ⊕ₛ σ.IdxFam) ρ :=
  t.bind (β := (α ⊕ₛ σ.IdxFam))
    (Fam.sumElim
      (varOf Fam.inl)
      ⟨fun s (v : (σ ⨯ η).IdxFam s) =>
          match v with
          | Signature.Idx.left w =>
              Term.var s (Sum.inr w)
          | Signature.Idx.right w =>
              u.getLeafTerm s w⟩)

/--
`getLeafTerm` commutes with `bind`: extracting a leaf from a substituted term
is the same as substituting into the extracted leaf.
-/
@[simp]
lemma getLeafTerm_bind {σ : Signature Sorts}
    (t : L.Term α σ) (f : α →ₛ L.Term₁ β)
    (s : Sorts) (w : σ.IdxFam s) :
    (t.bind f).getLeafTerm s w = (t.getLeafTerm s w).bind f := by
  induction t generalizing s with
  | nil => exact isEmptyElim w
  | var s' x =>
    cases w
    simp_all only [bind, getLeafTerm_var]
    cases (f s' x)
    · simp_all only [getLeafTerm_var]
    · simp_all only [getLeafTerm_func]
  | func _ _ ih =>
    cases w
    simp  [bind]
  | prod t₁ t₂ ih₁ ih₂ =>
    cases w with
    | left w => simp_all only [bind, getLeafTerm_prod_left]
    | right w => simp_all only [bind, getLeafTerm_prod_right]

/--
Extracting a leaf from `varTerm σ` yields the corresponding variable.
-/
@[simp]
lemma getLeafTerm_varTerm (σ : Signature Sorts) (s : Sorts) (w : σ.IdxFam s) :
    (varTerm (L := L) σ).getLeafTerm s w = .var s w := by
  induction σ with
  | nil => exact isEmptyElim w
  | of s' => cases w; simp only [varTerm, getLeafTerm_var]
  | prod σ₁ σ₂ ih₁ ih₂ =>
    cases w with
    | left w =>
        simp only [varTerm, mapVars, SigMap.incl_left_apply, SigMap.incl_right_apply,
          getLeafTerm_prod_left, getLeafTerm_bind, ih₁ w, bind, FamMap.mk_apply]
    | right w =>
        simp only [varTerm, mapVars, SigMap.incl_left_apply, SigMap.incl_right_apply,
          getLeafTerm_prod_right, getLeafTerm_bind, ih₂ w, bind, FamMap.mk_apply]
/--
Commuting `reindex` and `getLeafTerm`.
Reindexing a term `u` and then extracting leaf `w` is the same as
extracting the leaf first and then reindexing it.
-/
@[simp]
lemma reindex_getLeafTerm {σ σ' η : Signature Sorts}
    (g : SigMap σ σ')
    (u : L.Term (α ⊕ₛ σ.IdxFam) η)
    (s : Sorts)
    (w : η.IdxFam s) :
    (u.reindex g).getLeafTerm s w = (u.getLeafTerm s w).reindex g := by
  induction u generalizing s with
  | nil =>
      exact isEmptyElim w
  | var s' a =>
      cases w
      simp only [reindex, mapVars, bind, FamMap.mk_apply, getLeafTerm_var, var_bind]
  | func f ts ih =>
      cases w
      simp_all only [reindex_func, getLeafTerm_func]
  | prod t₁ t₂ ih₁ ih₂ =>
      cases w with
      | left w_l =>
          simp_all only [reindex_prod, getLeafTerm_prod_left]
      | right w_r =>
          simp_all only [reindex_prod, getLeafTerm_prod_right]

/-- Commuting `reindex` and `instantiate`. Basically equates:

    - Swapping the variables in block `η` with a term `u`, then
      reindexing the result along `g`.

    - Reindexing the original term along `g` (extended to cover `η`), then
      swapping the block `η` with the reindexed term `u`.
-/
@[simp]
lemma instantiate_reindex_extend_right {σ' η τ}
  (g : SigMap σ σ')
  (u : L.Term (α ⊕ₛ σ.IdxFam) η)
  (t : L.Term (α ⊕ₛ (σ ⨯ η).IdxFam) τ) :
  (t.reindex (SigMap.extend_right g)).instantiate (u.reindex g)
    =
  (t.instantiate u).reindex g := by
  induction t with
  | nil =>
      rfl
  | var t a =>
      cases a with
      | inl a =>
          rfl
      | inr v =>
          cases v with
          | left w =>
              rfl
          | right w =>
              simp only [instantiate, reindex_getLeafTerm, bind]; rfl
  | func f r ih =>
      simp only [Term.reindex, mapVars, Term.instantiate, Term.bind] at *
      rw [ih]
  | prod t₁ t₂ ih₁ ih₂ =>
      simp only [Term.reindex, mapVars, Term.instantiate, Term.bind] at *
      rw [ih₁, ih₂]

/-- `getLeafTerm` is monotone nonincreasing in size. It isn't strictly decreasing
    at vars as it fixes them, but is strictly decreasing on func and prod terms. -/
lemma getLeafTerm_size_le
  {σ : Signature Sorts} {t : L.Term α σ} {s : Sorts} {v : σ.IdxFam s} :
    (t.getLeafTerm s v).size <= t.size := by
    revert s v
    induction t with
    | nil => intro s v; cases v
    | var s' x => intro s v; cases v; simp only [getLeafTerm_var, le_refl]
    | func f r ih => intro s v; cases v; simp only [getLeafTerm_func, le_refl]
    | @prod σ₁ σ₂ t₁ t₂ ih₁ ih₂ =>
      intro s v; cases v
      case left w =>
        have h:= ih₁ (v:= w)
        simp only [getLeafTerm_prod_left, size]
        linarith
      case right w =>
        have h:= ih₂ (v:= w)
        simp only [getLeafTerm_prod_right, size]
        linarith

lemma getLeafTerm_size_lt_func
  {σ : Signature Sorts} {ts : L.Term α σ} {s : Sorts} {v : σ.IdxFam s} {f : L.Functions σ t} :
    (ts.getLeafTerm s v).size < (func f ts).size := by
  simp only[size]
  let h := getLeafTerm_size_le (t := ts) (v := v)
  linarith

lemma getLeafTerm_size_lt_prod_l
  {σ τ : Signature Sorts} {t₁ : L.Term α σ} {t₂ : L.Term α τ} :
    t₁.size < (prod t₁ t₂).size := by
  simp only [size]
  linarith

lemma getLeafTerm_size_lt_prod_r
  {σ τ : Signature Sorts} {t₁ : L.Term α σ} {t₂ : L.Term α τ} :
    t₂.size < (prod t₁ t₂).size := by
  simp only [size, lt_add_iff_pos_left, add_pos_iff, _root_.zero_lt_one, true_or]

/--
Substitutes function symbols in a term with term templates.

Given a term in language `L` and a mapping from `L`-function symbols to `L'`-term templates,
replaces each function application `func f ts` with the template `tf σ t f`, binding the
template's variables to the leaf terms extracted from `ts`.

⨯⨯Parameters:⨯⨯
- Term in language `L` with variables `α`
- Template map `tf : ∀ σ t, L.Functions σ t → L'.Term σ.IdxFam ⦃t⦄` that assigns
  a term template (with variables indexed by `σ.IdxFam`) to each function symbol

⨯⨯Example use case⨯⨯: Translating between languages or replacing function symbols with
their definitions. For instance, replacing a binary function `f(x,y)` with a template
like `g(x) + h(y)`.

The binding preserves the structure: leaf terms from the original arguments are substituted
into the corresponding positions in the template.
-/
@[simp]
def bindFunc {σ : Signature Sorts} :
  L.Term α σ →
  (∀ σ t, L.Functions σ t → L'.Term σ.IdxFam ⦃t⦄) →
  L'.Term α σ
  | nil, _  => nil
  | var t a, _ => var t a
  | func (σ := σ) (t := t) f ts, tf =>
      (tf σ t f).bind ⟨fun s => fun v => (ts.getLeafTerm s v).bindFunc tf⟩
  | prod t₁ t₂, tf => prod (t₁.bindFunc tf) (t₂.bindFunc tf)
termination_by
  t _ => t.size
decreasing_by
  -- The recursive call in the `func` case
  · -- goal is: (ts.getLeafTerm s v).size < (func f ts).size
    simp only [getLeafTerm_size_lt_func (σ := σ) (ts := ts) (s := s) (v := v) (f := f)]
  -- The recursive call on `t₁` in the `prod` case
  · -- goal is: t₁.size < (prod t₁ t₂).size
    simp only [getLeafTerm_size_lt_prod_l (t₁ := t₁) (t₂ := t₂)]
  -- The recursive call on `t₂` in the `prod` case
  · -- goal: t₂.size < (prod t₁ t₂).size
    simp only [getLeafTerm_size_lt_prod_r (t₁ := t₁) (t₂ := t₂)]

@[simp]
lemma mapVars_bind {β : Fam Sorts} {σ : Signature Sorts}
  (ρ : α →ₛ β)
  (t : L.Term α σ)
  (f : β →ₛ L.Term₁ γ) :
  (mapVars ρ t).bind f =
    t.bind (fun s v => f s (ρ s v)) := by
  induction t <;>
  simp_all only [mapVars, bind, FamMap.mk_apply]
  rfl

@[simp]
theorem rename_subst (t : Term L (α ⊕ₛ σ.IdxFam) τ)
    (f : α →ₛ β)
    (g : β →ₛ L.Term₁ (γ ⊕ₛ σ.IdxFam)) :
    (t.rename f).subst g = t.subst (fun s a => g s (f s a)) := by
  induction t <;> simp_all only [subst, rename, mapVars, bind]
  case var a =>
  cases a with
  | inl val =>
  simp_all only [sumElim_eval_l]
  rfl
  | inr val_1 =>
  simp_all only [FamMap.mk_apply, sumMap_inr_apply, FamMap.idₛ_apply', bind, sumElim_eval_r]

@[simp]
theorem subst_rename (t : Term L (α ⊕ₛ σ.IdxFam) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam))
    (g : β →ₛ γ) :
    (t.subst f).rename g = t.subst ⟨fun s a => (f s a).rename g⟩ := by
  induction t with
  | var _ a =>
    cases a with
    | inl val => rfl
    | inr val => rfl
  | func F t' ih =>
      simp only [subst_func, rename_func, ih]
  | prod =>
      simp_all only [subst_prod, rename_prod]
  | nil =>
      rfl

/- 4. Subst then Subst (Composition)
 This is the hardest one, usually requiring the `bind_bind` lemma I mentioned in the previous turn.
It says (t[f])[g] = t[x ↦ f(x)[g]] -/
@[simp]
theorem subst_subst (t : Term L (α ⊕ₛ σ.IdxFam) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam))
    (g : β →ₛ L.Term₁ (γ ⊕ₛ σ.IdxFam)) :
    (t.subst f).subst g = t.subst ⟨fun s a => (f s a).subst g⟩ := by
    induction t with
  | var _ a =>
    cases a with
    | inl val => rfl
    | inr val => rfl
  | func F t' ih =>
      simp only [subst_func, ih]
  | prod =>
      simp_all only [subst_prod]
  | nil =>
      rfl


/--
Substituting leaf terms into varTerm returns the original term:
-/
@[simp]
lemma IdxFamTerm_subst_getLeaf
  (σ : Signature Sorts) (ts : L.Term α σ) :
  (varTerm σ).bind (ts.getLeafTerm) = ts := by
  induction σ with
  | nil =>
      cases ts
      simp only [varTerm, bind]
  | of s =>
      cases ts with
      | var s' a => rfl
      | func f' ts' => rfl
  | prod σ₁ σ₂ ih₁ ih₂ =>
      cases ts with
      | prod t₁ t₂ =>
          unfold varTerm
          simp_all only [bind, mapVars, SigMap.incl_left_apply, bind_bind, SigMap.incl_right_apply,
            prod.injEq]
          apply And.intro
          · apply ih₁
          · apply ih₂

/--
Substituting leaf terms of ts into the generic function term for f returns `func f ts`:
-/
@[simp] lemma Functions.term_subst_getLeaf
  (σ : Signature Sorts) (t : Sorts)
  (f : L.Functions σ t) (ts : L.Term α σ) :
  (Functions.term f).bind ts.getLeafTerm = func f ts := by
  simp only [Functions.term, bind, IdxFamTerm_subst_getLeaf]

/--
Helper lemma for bindFunc_term: since bindFunc's recursive call on `func` terms is actually
on `ts.getLeafTerm s v` rather than `ts`, it's helpful to prove this special case separately.
-/
lemma bindFunc_getLeafTerm {s : Sorts} {σ : Signature Sorts} {v : σ.IdxFam s} {g : L.Term α σ} :
  ((g.getLeafTerm s v).bindFunc (@Functions.term _ _)) = g.getLeafTerm s v := by
  revert s v
  induction g with
  | var s x =>
    intro s' v; cases v
    case var => simp_all only [getLeafTerm_var, bindFunc]
  | func f r ih =>
    intro s v; cases v
    case var =>
      simp_all only [getLeafTerm_func, bindFunc]
      rw[←Functions.term_subst_getLeaf]
      rfl
  | prod t₁ t₂ ih₁ ih₂ =>
    intro s v; cases v
    case left => simp_all only [getLeafTerm_prod_left]
    case right => simp_all only [getLeafTerm_prod_right]
  | nil => simp only [IsEmpty.forall_iff, implies_true]

@[simp]
theorem bindFunc_term
 (g : L.Term α σ) :
  g.bindFunc (@Functions.term _ _) = g := by
  induction g
  case nil =>
    simp_all only [bindFunc]
  case var =>
    simp_all only [bindFunc]
  case func f ts h =>
    have h' : (fun s v ↦ (ts.getLeafTerm s v).bindFunc (@Functions.term Sorts L))
              = fun s v ↦ (ts.getLeafTerm s v):= by
      ext s v; exact bindFunc_getLeafTerm (s:= s) (v:= v)
    unfold bindFunc; rw[h']
    rw[←Functions.term_subst_getLeaf]
    rfl
  case prod t₁ t₂ ih₁ ih₂ =>
    simp_all only [bindFunc]

lemma reindex_subst {β : Fam Sorts} {σ τ ξ : Signature Sorts}
    (g : SigMap σ τ)
    (t : L.Term (α ⊕ₛ σ.IdxFam) ξ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (t.subst f).reindex g =
    (t.reindex g).subst ⟨fun s a => (f s a).reindex g⟩ := by
    unfold reindex subst
    simp_all only [mapVars, bind_bind]
    apply congr
    · rfl
    · ext s a
      cases a with
      | inl val =>
      simp_all only [FamMap.mk_apply]
      rfl
      | inr val_1 =>
        simp_all only [FamMap.mk_apply]
        rfl


syntax "reduce_term_to_bind" : tactic

macro_rules
  | `(tactic| reduce_term_to_bind) =>
      `(tactic|
        simp (config := { zeta := true }) only [
          MSFirstOrder.Language.Term.subst,
          MSFirstOrder.Language.Term.rename,
          MSFirstOrder.Language.Term.reindex,
          MSFirstOrder.Language.Term.openVars,
          MSFirstOrder.Language.Term.instantiate,
          MSFirstOrder.Language.Term.mapVars,
          MSFirstOrder.Language.Term.bind,
          MSFirstOrder.Language.Term.varOf,
          MSFirstOrder.Fam.sumElim
        ];
        repeat simp only [MSFirstOrder.Language.Term.bind_bind]
      )

end substitution

section variable_finsets
/-! ### Variable Finsets

This section defines operations for collecting the free variables used in a term
into finite sets. This is used for scope analysis and variable restriction.
-/

open Finset

/-- The `Finset` of variables used in a given term (now multi-sorted). -/
@[simp]
def varFinset {σ : Signature Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : L.Term α σ → Finset (Σ t, α t)
  | var t i => {⟨_,i⟩}
  | func _ args => args.varFinset
  | prod t₁ t₂ => t₁.varFinset ∪ t₂.varFinset
  | nil => ∅

/-- The Fam of variables occuring in a Term -/
def varFam {σ : Signature Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : L.Term α σ → DepSet α
   := fun t => DepSet.ofSigma (varFinset t)

abbrev varType {σ : Signature Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] (t : L.Term α σ) : Fam Sorts :=
  (varFam t : Fam Sorts)

lemma varFinset_prod_subset_left {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    {t₁ : L.Term α σ₁} {t₂ : L.Term α σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFinset t₁ ⊆ varFinset (prod t₁ t₂) := by
    exact union_subset_left fun ⦃a⦄ a_1 ↦ a_1

lemma varFinset_prod_subset_right {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    {t₁ : L.Term α σ₁} {t₂ : L.Term α σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFinset t₂ ⊆ varFinset (prod t₁ t₂) := by
    exact union_subset_right fun ⦃a⦄ a_1 ↦ a_1

@[simp]
lemma varFam_var {s : Sorts} {α : Fam.{u'} Sorts}
    {a : α s}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFam (Term.var (L:= L) s a) s = {a} := by
  simp only [varFam, DepSet.ofSigma, varFinset, coe_singleton]
  ext b
  constructor
  · intro h
    change (⟨s, b⟩ : Sigma α) ∈ ({(⟨s, a⟩ : Sigma α)} : Set (Sigma α)) at h
    simpa using h
  · intro a_1
    simp_all only [Set.mem_singleton_iff]
    subst a_1
    rfl

@[simp]
lemma varFam_var' {s t : Sorts} {α : Fam.{u'} Sorts}
    {a : α s} (h : t ≠ s)
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFam (Term.var (L:= L) s a) t = ∅ := by
  ext b
  constructor
  · intro hb
    simp_all only [ne_eq,coe_singleton, Set.mem_empty_iff_false, varFinset, varFam, DepSet.ofSigma]
    change ⟨t, b⟩ ∈ ({⟨s, a⟩} : Set (Sigma α)) at hb
    simp_all only [Set.mem_singleton_iff, Sigma.mk.injEq, false_and]
  · intro a_1
    simp_all only [ne_eq, Set.mem_empty_iff_false]

@[simp]
lemma varFam_func {s : Sorts} {α : Fam.{u'} Sorts} {f : L.Functions σ s}
    {t : L.Term α σ}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFam (Term.func f t) = varFam t := by
  rfl

@[simp]
lemma varFam_prod_subset_left {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    {t₁ : L.Term α σ₁} {t₂ : L.Term α σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFam t₁ ⊆ varFam (prod t₁ t₂) := by
    simp only [varFam, DepSet.ofSigma, varFinset, coe_union]
    tauto

@[simp]
lemma varFam_prod_subset_right {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    {t₁ : L.Term α σ₁} {t₂ : L.Term α σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFam t₂ ⊆ varFam (prod t₁ t₂) := by
    simp only [varFam, DepSet.ofSigma, varFinset, coe_union]
    tauto

/-- Inclusion of variable types along a function application. -/
def varTypeIncl_func {σ : Signature Sorts} {s : Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)]
    (f : L.Functions σ s) (t : L.Term α σ) :
    t.varType →ₛ (Term.func f t).varType :=
  DepSet.inclusion (by
    intro s x
    simp_all only [varFam_func])

/-- Inclusion of variable types into the left component of a product term. -/
def varTypeIncl_prod_left {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)]
    (t₁ : L.Term α σ₁) (t₂ : L.Term α σ₂) :
    t₁.varType →ₛ (prod t₁ t₂).varType :=
  DepSet.inclusion (varFam_prod_subset_left (t₁ := t₁) (t₂ := t₂))

/-- Inclusion of variable types into the right component of a product term. -/
def varTypeIncl_prod_right {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)]
    (t₁ : L.Term α σ₁) (t₂ : L.Term α σ₂) :
    t₂.varType →ₛ (prod t₁ t₂).varType :=
  DepSet.inclusion (varFam_prod_subset_right (t₁ := t₁) (t₂ := t₂))

/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeft {β : Fam Sorts} {σ : Signature Sorts}
  [DecidableEq Sorts] [∀ t, DecidableEq (α t)] :
    L.Term (α ⊕ₛ β) σ → Finset (Σ t, α t)
  | var _ (Sum.inl i) => {⟨_,i⟩}
  | var _ (Sum.inr _i) => ∅
  | func _ args => args.varFinsetLeft
  | prod t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | nil => ∅

/-- The Fam of variables from the left side of a sum occurring in a Term -/
@[simp]
def varFamLeft {β : Fam Sorts} {σ : Signature Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : L.Term (α ⊕ₛ β) σ → DepSet α :=
  fun t => DepSet.ofSigma (varFinsetLeft t)

abbrev varTypeLeft {β : Fam Sorts} {σ : Signature Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] (t : L.Term (α ⊕ₛ β) σ) : Fam Sorts :=
  (varFamLeft t : Fam Sorts)

@[simp]
lemma varFamLeft_prod_subset_left {β : Fam Sorts} {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    {t₁ : L.Term (α ⊕ₛ β) σ₁} {t₂ : L.Term (α ⊕ₛ β) σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFamLeft t₁ ⊆ varFamLeft (prod t₁ t₂) := by
  simp only [varFamLeft, DepSet.ofSigma, varFinsetLeft, coe_union]
  tauto

@[simp]
lemma varFamLeft_prod_subset_right {β : Fam Sorts} {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    {t₁ : L.Term (α ⊕ₛ β) σ₁} {t₂ : L.Term (α ⊕ₛ β) σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFamLeft t₂ ⊆ varFamLeft (prod t₁ t₂) := by
  simp only [varFamLeft, DepSet.ofSigma, varFinsetLeft, coe_union]
  tauto

/-- Inclusion of variable types on the left side along a function application. -/
def varTypeLeftIncl_func {β : Fam Sorts} {σ : Signature Sorts} {s : Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)]
    (f : L.Functions σ s) (t : L.Term (α ⊕ₛ β) σ) :
    t.varTypeLeft →ₛ (Term.func f t).varTypeLeft :=
  DepSet.inclusion (by
    simp_all only [varFamLeft, varFinsetLeft, subset_refl]
    )

/-- Inclusion of variable types on the left side into the left component of a product term. -/
def varTypeLeftIncl_prod_left {β : Fam Sorts} {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)]
    (t₁ : L.Term (α ⊕ₛ β) σ₁) (t₂ : L.Term (α ⊕ₛ β) σ₂) :
    t₁.varTypeLeft →ₛ (prod t₁ t₂).varTypeLeft :=
  DepSet.inclusion (varFamLeft_prod_subset_left (t₁ := t₁) (t₂ := t₂))

/-- Inclusion of variable types on the left side into the right component of a product term. -/
def varTypeLeftIncl_prod_right {β : Fam Sorts} {σ₁ σ₂ : Signature Sorts} {α : Fam.{u'} Sorts}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)]
    (t₁ : L.Term (α ⊕ₛ β) σ₁) (t₂ : L.Term (α ⊕ₛ β) σ₂) :
    t₂.varTypeLeft →ₛ (prod t₁ t₂).varTypeLeft :=
  DepSet.inclusion (varFamLeft_prod_subset_right (t₁ := t₁) (t₂ := t₂))

instance varFamFinite {σ : Signature Sorts} {α : Fam.{u'} Sorts}
      {t : L.Term α σ} [DecidableEq Sorts] [∀ t, DecidableEq (α t)] :
      Finite (Sigma (varFam t : Fam Sorts)) := by
    show Finite (Sigma (varFam t).Subtype)
    unfold varFam
    rw[←DepSet.isFinite_iff_finite_sigma]
    simp only [DepSet.ofSigma_finset_isFinite]

instance varFamLeftFinite {β : Fam Sorts} {σ : Signature Sorts} {α : Fam.{u'} Sorts}
      {t : L.Term (α ⊕ₛ β) σ} [DecidableEq Sorts] [∀ t, DecidableEq (α t)] :
      Finite (Sigma (varFamLeft t : Fam Sorts)) := by
    show Finite (Sigma (varFamLeft t).Subtype)
    unfold varFamLeft
    rw[←DepSet.isFinite_iff_finite_sigma]
    simp only [DepSet.ofSigma_finset_isFinite]

end variable_finsets

section variable_restriction
/-! ### Variable Restriction

This section defines operations for restricting terms to use only a specified
subset of their free variables. Used for scope management and variable elimination.
-/

open Finset
variable {β : Fam.{v'} Sorts}


/-- Restricts a term to use only a set of the given variables. -/
def restrictVar
  [DecidableEq Sorts]
  [∀ s, DecidableEq (α s)]
  : ∀ {σ : Signature Sorts} (t : L.Term α σ)
      (_ : t.varType →ₛ β),
      L.Term β σ
| _ , var t a, g =>
    var t (@g t ⟨a, by simp⟩)
| _, func f ts, g =>
    func f (restrictVar ts g)
| _, prod t₁ t₂, g =>
    prod (restrictVar t₁ ⟨fun {s} x => g s ⟨x.val, by
          have hx : x.val ∈ (varFam t₁) s := x.property
          change ⟨s, x.val⟩ ∈ varFinset (t₁.prod t₂)
          change ⟨s, x.val⟩ ∈ varFinset t₁ at hx
          simp only [varFinset]
          exact Finset.mem_union_left _ hx⟩⟩)
        (restrictVar t₂ ⟨fun {s} x => g s ⟨x.val, by
          have hx : x.val ∈ (varFam t₂) s := x.property
          change ⟨s, x.val⟩ ∈ varFinset (t₁.prod t₂)
          change ⟨s, x.val⟩ ∈ varFinset t₂ at hx
          simp only [varFinset]
          exact Finset.mem_union_right _ hx⟩⟩)
  | _, nil, _ => nil

/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrictVarLeft {β : Fam Sorts} [DecidableEq Sorts] {γ : Fam Sorts}
  [∀ t, DecidableEq (α t)]
  : ∀ {σ : Signature Sorts} (f : L.Term (α ⊕ₛ γ) σ)
      (_ : f.varTypeLeft →ₛ β),
    L.Term (β ⊕ₛ γ) σ
| _, var t (Sum.inl a), g =>
  let x : (var t (Sum.inl a)).varTypeLeft t :=
      ⟨a, by
        simp_all only [varFamLeft, varFinsetLeft, coe_singleton]
        rfl⟩
  var t (Sum.inl (g t x))
| _, var t (Sum.inr a), _ => var t (Sum.inr a)
| _, func t ts, g =>
  func t (restrictVarLeft ts g)
| _, prod t₁ t₂, g =>
    prod
        (restrictVarLeft t₁ ⟨fun {t} x => g t ⟨x.val, by
          have hx : x.val ∈ (varFamLeft t₁) t := x.property
          change ⟨t, x.val⟩ ∈ varFinsetLeft (t₁.prod t₂)
          change ⟨t, x.val⟩ ∈ varFinsetLeft t₁ at hx
          simp only [varFinsetLeft]
          exact Finset.mem_union_left _ hx⟩⟩)
        (restrictVarLeft t₂ ⟨fun {t} x => g t ⟨x.val, by
          have hx : x.val ∈ (varFamLeft t₂) t := x.property
          change ⟨t, x.val⟩ ∈ varFinsetLeft (t₁.prod t₂)
          change ⟨t, x.val⟩ ∈ varFinsetLeft t₂ at hx
          simp only [varFinsetLeft]
          exact Finset.mem_union_right _ hx⟩⟩)
| _, nil, _ => nil

end variable_restriction

open Idx
variable {σ ξ τ η : Signature Sorts}

/-- The term-level identity needed for `BoundedFormula.openVars_closeVars` when `closeVars` is
defined via `relabel` + `SigEquiv.comm`.
  Shows that opening vars then closing them is the identity. -/
@[simp]
lemma openVars_close_id
  (t : L.Term (α ⊕ₛ (σ ⨯ τ).IdxFam) ξ) :
  Term.reindex (SigEquiv.comm (σ := τ) (τ := σ)).toFun
      ((Term.reindex (SigMap.incl_right : SigMap σ (τ ⨯ σ)) t.openVars).subst
        (Fam.sumElim
          (varOf Fam.inl)
          (varOf (Fam.inr ∘ₛ ⟨fun s => @Idx.left _ _ _ s⟩))))
    = t := by
  induction t with
  | nil =>
      simp only [reindex, mapVars, subst, openVars, bind]
  | func f ts ih =>
      simp_all only [openVars, bind, reindex_func, subst_func]
  | prod t₁ t₂ ih₁ ih₂ =>
      simp_all only [openVars, bind, reindex_prod, subst_prod]
  | var s a =>
      cases a with
      | inl b => rfl
      | inr v =>
          cases v with
          | left w => rfl
          | right w => rfl

/--
General version: closing variables with `f: X → τ.IdxFam` then opening them is
equivalent to renaming the variables from `X` to `τ.IdxFam` via `f`.
-/
lemma close_openVars
  {σ τ : Signature Sorts} {ξ : Signature Sorts} {X : Fam Sorts}
  (f : X →ₛ τ.IdxFam)
  (t : L.Term ((α ⊕ₛ X) ⊕ₛ σ.IdxFam) ξ) :
  openVars (L := L) (α := α) (η := σ) (τ := τ)
    (reindex (SigEquiv.comm (σ := τ) (τ := σ)).toFun
      ((t.reindex
          (SigMap.incl_right : SigMap σ (τ ⨯ σ))
       ).subst
          (Fam.sumElim
            (varOf Fam.inl)
            ⟨fun s x => var s (Sum.inr (Signature.Idx.left (f s x)))⟩
        )
      )
    )
  = (t.rename (Fam.sumElim ⟨fun _ a => Sum.inl a⟩ ⟨fun s x => Sum.inr (f s x)⟩)) := by
  induction t with
  | nil =>
      simp only [openVars, reindex, mapVars, subst, bind, rename]
  | func g ts ih =>
      simp only [openVars, reindex, mapVars, subst, bind_bind, bind,
        rename_func] at *
      rw [ih]
  | prod t₁ t₂ ih₁ ih₂ =>
      simp only [openVars, reindex, mapVars, subst, bind_bind, bind,
        rename_prod] at *
      rw [ih₁, ih₂]
  | var s a =>
      cases a with
      | inl val =>
        cases val with
        | inl val_1 =>
          rfl
        | inr val_2 =>
          rfl
      | inr val_1 =>
        simp_all only [reindex_var_inr, subst_var_inr, rename_var_inr]
        rfl

/-- Specialized version of `close_openVars` with `X := τ.IdxFam` and `f := id`,
so the overall effect is the identity. -/
@[simp]
lemma close_openVars_id_id
  {σ τ : Signature Sorts} {ξ : Signature Sorts}
  (t : L.Term ((α ⊕ₛ τ.IdxFam) ⊕ₛ σ.IdxFam) ξ) :
  openVars (L := L) (α := α) (η := σ) (τ := τ)
    (reindex (SigEquiv.comm (σ := τ) (τ := σ)).toFun
      ((t.reindex
          (SigMap.incl_right : SigMap σ (τ ⨯ σ))
       ).subst
          (Fam.sumElim
            (varOf Fam.inl)
            ⟨fun s x => var s (Sum.inr x.left)⟩
        )
      )
    )
  = t := by
  have h := @close_openVars _ _ _ σ τ ξ (τ.IdxFam) ⟨fun s (x : τ.IdxFam s) => x⟩ t
  simp only [FamMap.mk_apply] at *
  rw [h]
  have eq_id : (Fam.sumElim ⟨fun _ (a : α _) => Sum.inl a⟩ ⟨fun s (x : τ.IdxFam s) => Sum.inr x⟩ :
          (α ⊕ₛ τ.IdxFam) →ₛ (α ⊕ₛ τ.IdxFam)) = Fam.FamMap.idₛ := by
    ext s x
    cases x with
    | inl a => rfl
    | inr x => rfl
  rw [eq_id]
  exact rename_id t

end Term

namespace LHom

variable {σ : Signature Sorts}

open Term

/-- Maps a term's symbols along a language map. -/
@[simp]
def onTerm {σ : Signature Sorts} (φ : L →ᴸ L') : L.Term α σ → L'.Term α σ
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
theorem comp_onTerm {L'' : Language Sorts} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
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
def LEquiv.onTerm {σ : Signature Sorts} (φ : L ≃ᴸ L') : L.Term α σ ≃ L'.Term α σ where
  toFun := φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onTerm, φ.left_inv, LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onTerm, φ.right_inv, LHom.id_onTerm]

variable (L : Language.{u, v, z} Sorts)


/-- A bounded formula for a many-sorted language `L`, with free variables in `α`. -/
inductive BoundedFormula (α : Fam.{u'} Sorts) : Signature Sorts → Type (max u v z u')
  | falsum {σ} : BoundedFormula α σ
  | equal {σ τ}
    -- note: only terms with the exact same signatures can be set equal to eachother
      (t₁ t₂ : L.Term (α ⊕ₛ σ.IdxFam) τ) :
      BoundedFormula α σ
  | rel {σ σ'}
      (R : L.Relations σ')
      (ts : (L.Term (α ⊕ₛ σ.IdxFam) σ')) :
      BoundedFormula α σ
  /-- The logical implication of two bounded formulas-/
  | imp {σ}
      (f₁ f₂ : BoundedFormula α σ) :
      BoundedFormula α σ
  /-- Adds a universal quantifier to a bounded formula-/
  | all {σ} (τ)
      (f : BoundedFormula α (σ ⨯ τ)) :
      BoundedFormula α σ



/-- Size of a bounded formula, useful for proving termination of recursion. -/
def BoundedFormula.size : {σ : Signature Sorts} → L.BoundedFormula α σ → Nat
    | _, .falsum            => 1
    | _, .equal _ _        => 1
    | _, .rel _ ts  => 1 + ts.size
    | _, .imp f₁ f₂     => 1 + BoundedFormula.size f₁ + BoundedFormula.size f₂
    | _, all _ f => 1 + BoundedFormula.size f

attribute [simp] BoundedFormula.size

abbrev Formula (L : Language.{u, v, z} Sorts) (α : Fam.{u'} Sorts) := BoundedFormula L α nil


/-- A sentence is a formula with no free variables. -/
abbrev Sentence (L : Language.{u, v, z} Sorts) :=
  Formula L Fam.EmptyFam

/-- A theory is a set of sentences. -/
abbrev Theory :=
  Set L.Sentence

open Finsupp

variable {L : Language.{u, v, z} Sorts} {α : Fam.{u'} Sorts} {β : Sorts → Type v'}
  {σ ξ τ η : Signature Sorts} {s s₁ s₂ : Sorts}

/-! ### Relation and Equality Constructors -/

/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {ξ : Signature Sorts} (R : L.Relations σ)
    (ts : L.Term (α ⊕ₛ ξ.IdxFam) σ) : L.BoundedFormula α ξ :=
  BoundedFormula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations (of s)) (t : L.Term (α ⊕ₛ σ.IdxFam) (of s)) :
    L.BoundedFormula α σ := r.boundedFormula t

/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations (⦃s₁⦄ ⨯ ⦃s₂⦄)) (t₁ : L.Term (α ⊕ₛ σ.IdxFam) ⦃s₁⦄)
    (t₂ : L.Term (α ⊕ₛ σ.IdxFam) ⦃s₂⦄) :
    L.BoundedFormula α σ := r.boundedFormula (t₁.prod t₂)

/-- The equality of two tuples of terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (α ⊕ₛ σ.IdxFam) ξ) : L.BoundedFormula α σ :=
  BoundedFormula.equal t₁ t₂

/-- Applies a relation to terms as a formula. -/
def Relations.formula (R : L.Relations σ) (ts : L.Term α σ) : L.Formula α :=
  R.boundedFormula (ts.mapVars Fam.inl)
/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations (of s)) (t : L.Term α (of s)) : L.Formula α :=
  Relations.formula r t

/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations (⦃s₁⦄ ⨯ ⦃s₂⦄)) (t₁ : L.Term₁ α s₁) (t₂ : L.Term₁ α s₂) :
    L.Formula α := Relations.formula r (t₁.prod t₂)

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α σ) : L.Formula α :=
  (mapVars Fam.inl t₁).bdEqual (mapVars Fam.inl t₂)

namespace BoundedFormula

/-! ### Basic Instances -/

instance : Inhabited (L.BoundedFormula α σ) :=
  ⟨falsum⟩

instance : Bot (L.BoundedFormula α σ) :=
  ⟨falsum⟩

/-! ### Logical Connectives and Quantifiers -/

/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
protected def ex (ξ : Signature Sorts) (φ : L.BoundedFormula α (σ ⨯ ξ)) : L.BoundedFormula α σ :=
  φ.not.all.not

/-- Takes the logical disjunction of two bounded formulas. -/
@[match_pattern]
protected def or (φ ψ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  φ.not.imp ψ

/-- Takes the logical conjunction of two bounded formulas. -/
@[match_pattern]
protected def and (φ ψ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  (φ.not.or ψ.not).not

/-! ### Typeclass Instances for Lattice Operations -/

instance : Top (L.BoundedFormula α σ) :=
  ⟨BoundedFormula.not ⊥⟩

instance : Min (L.BoundedFormula α σ) :=
  ⟨fun f g => (f.imp g.not).not⟩

instance : Max (L.BoundedFormula α σ) :=
  ⟨fun f g => f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BoundedFormula α σ) :=
  φ.imp ψ ⊓ ψ.imp φ

/-! ### Free Variables -/

open Finset
open Finsupp

/-- The `Finset` of variables used in a given formula. -/
@[simp]
def freeVarFinset [DecidableEq Sorts] [∀ s, DecidableEq (α s)] :
    ∀ {σ}, L.BoundedFormula α σ → Finset (Σ s, α s)
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts =>  ts.varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | _n, all _ f => f.freeVarFinset

/-- The DepSet of free variables occurring in a BoundedFormula -/
def freeVarFam [DecidableEq Sorts] [∀ s, DecidableEq (α s)] :
    ∀ {σ}, L.BoundedFormula α σ → DepSet α :=
  fun {_} φ => DepSet.ofSigma (freeVarFinset φ)

abbrev freeVarType [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts} (φ : L.BoundedFormula α σ) : Fam Sorts :=
  (freeVarFam φ : Fam Sorts)

instance freeVarFamFinite [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts} {φ : L.BoundedFormula α σ} :
    Finite (Sigma (freeVarFam φ : Fam Sorts)) := by
  show Finite (Sigma (freeVarFam φ).Subtype)
  unfold freeVarFam
  rw[←DepSet.isFinite_iff_finite_sigma]
  simp only [DepSet.ofSigma_finset_isFinite]

section free_var_inclusions

variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)] {σ τ : Signature Sorts}
          (t₁ t₂ ts : L.Term (α ⊕ₛ σ.IdxFam) τ) (R : L.Relations τ)
/-! ### Free Variable Inclusions -/

/-- Inclusion of the left term's variables into the free variables of an equality. -/
def varIncl_eq_l :
    t₁.varTypeLeft →ₛ (BoundedFormula.equal t₁ t₂).freeVarType :=
  DepSet.inclusion (by
    unfold freeVarFam Term.varFamLeft freeVarFinset
    simp
  )

/-- Inclusion of the right term's variables into the free variables of an equality. -/
def varIncl_eq_r :
    t₂.varTypeLeft →ₛ (BoundedFormula.equal t₁ t₂).freeVarType :=
  DepSet.inclusion (by
    unfold freeVarFam Term.varFamLeft freeVarFinset
    simp
    )

/-- Inclusion of a relation's term variables into the free variables of the relation formula. -/
@[simp]
theorem varIncl_rel :
    (BoundedFormula.rel R ts).freeVarType = ts.varTypeLeft := by rfl

/-
/-- Inclusion of the left subformula's free variables into an implication. -/
def freeVarTypeIncl_imp_left [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ₁ φ₂ : L.BoundedFormula α σ) :
    φ₁.freeVarType →ₛ (BoundedFormula.imp φ₁ φ₂).freeVarType :=
  DepSet.inclusion (by
    intro s x hx
    change (⟨s, x⟩ : Sigma α) ∈ freeVarFinset φ₁ at hx
    change (⟨s, x⟩ : Sigma α) ∈ freeVarFinset (BoundedFormula.imp φ₁ φ₂)
    exact Finset.mem_union.mpr (Or.inl hx))

/-- Inclusion of the right subformula's free variables into an implication. -/
def freeVarTypeIncl_imp_right [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ₁ φ₂ : L.BoundedFormula α σ) :
    φ₂.freeVarType →ₛ (BoundedFormula.imp φ₁ φ₂).freeVarType :=
  DepSet.inclusion (by
    intro s x hx
    change (⟨s, x⟩ : Sigma α) ∈ freeVarFinset φ₂ at hx
    change (⟨s, x⟩ : Sigma α) ∈ freeVarFinset (BoundedFormula.imp φ₁ φ₂)
    exact Finset.mem_union.mpr (Or.inr hx))

/-- Inclusion of free variables through a universal quantifier. -/
def freeVarTypeIncl_all [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ τ : Signature Sorts}
    (φ : L.BoundedFormula α (σ ⨯ τ)) :
    φ.freeVarType →ₛ (BoundedFormula.all τ φ).freeVarType :=
  DepSet.inclusion (by
    intro s x hx
    change (⟨s, x⟩ : Sigma α) ∈ freeVarFinset φ at hx
    change (⟨s, x⟩ : Sigma α) ∈ freeVarFinset (BoundedFormula.all τ φ)
    simpa [freeVarFinset] using hx)

/-- Inclusion of free variables through negation. -/
def freeVarTypeIncl_not [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ) :
    φ.freeVarType →ₛ (BoundedFormula.not φ).freeVarType := by
  simpa [BoundedFormula.not] using
    (freeVarTypeIncl_imp_left (φ₁ := φ) (φ₂ := (⊥ : L.BoundedFormula α σ)))

/-- Inclusion of the left subformula's free variables into a disjunction. -/
def freeVarTypeIncl_or_left [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ ψ : L.BoundedFormula α σ) :
    φ.freeVarType →ₛ (BoundedFormula.or φ ψ).freeVarType := by
  simpa [BoundedFormula.or] using
    (freeVarTypeIncl_imp_left (φ₁ := BoundedFormula.not φ) (φ₂ := ψ)
      ∘ₛ freeVarTypeIncl_not (φ := φ))

/-- Inclusion of the right subformula's free variables into a disjunction. -/
def freeVarTypeIncl_or_right [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ ψ : L.BoundedFormula α σ) :
    ψ.freeVarType →ₛ (BoundedFormula.or φ ψ).freeVarType := by
  simpa [BoundedFormula.or] using
    (freeVarTypeIncl_imp_right (φ₁ := BoundedFormula.not φ) (φ₂ := ψ))

/-- Inclusion of the left subformula's free variables into a conjunction. -/
def freeVarTypeIncl_and_left [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ ψ : L.BoundedFormula α σ) :
    φ.freeVarType →ₛ (BoundedFormula.and φ ψ).freeVarType := by
  simpa [BoundedFormula.and] using
    (freeVarTypeIncl_not (φ := BoundedFormula.or (BoundedFormula.not φ) (BoundedFormula.not ψ))
      ∘ₛ freeVarTypeIncl_or_left (φ := BoundedFormula.not φ) (ψ := BoundedFormula.not ψ)
      ∘ₛ freeVarTypeIncl_not (φ := φ))

/-- Inclusion of the right subformula's free variables into a conjunction. -/
def freeVarTypeIncl_and_right [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ ψ : L.BoundedFormula α σ) :
    ψ.freeVarType →ₛ (BoundedFormula.and φ ψ).freeVarType := by
  simpa [BoundedFormula.and] using
    (freeVarTypeIncl_not (φ := BoundedFormula.or (BoundedFormula.not φ) (BoundedFormula.not ψ))
      ∘ₛ freeVarTypeIncl_or_right (φ := BoundedFormula.not φ) (ψ := BoundedFormula.not ψ)
      ∘ₛ freeVarTypeIncl_not (φ := ψ))

/-- Inclusion of the left subformula's free variables into a biimplication. -/
def freeVarTypeIncl_iff_left [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ ψ : L.BoundedFormula α σ) :
    φ.freeVarType →ₛ (BoundedFormula.iff φ ψ).freeVarType := by
  let A : L.BoundedFormula α σ := BoundedFormula.imp φ ψ
  let B : L.BoundedFormula α σ := BoundedFormula.not (BoundedFormula.imp ψ φ)
  simpa [BoundedFormula.iff, A, B] using
    (freeVarTypeIncl_not (φ := BoundedFormula.imp A B)
      ∘ₛ freeVarTypeIncl_imp_left (φ₁ := A) (φ₂ := B)
      ∘ₛ freeVarTypeIncl_imp_left (φ₁ := φ) (φ₂ := ψ))

/-- Inclusion of the right subformula's free variables into a biimplication. -/
def freeVarTypeIncl_iff_right [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ ψ : L.BoundedFormula α σ) :
    ψ.freeVarType →ₛ (BoundedFormula.iff φ ψ).freeVarType := by
  let A : L.BoundedFormula α σ := BoundedFormula.imp φ ψ
  let B : L.BoundedFormula α σ := BoundedFormula.not (BoundedFormula.imp ψ φ)
  simpa [BoundedFormula.iff, A, B] using
    (freeVarTypeIncl_not (φ := BoundedFormula.imp A B)
      ∘ₛ freeVarTypeIncl_imp_left (φ₁ := A) (φ₂ := B)
      ∘ₛ freeVarTypeIncl_imp_right (φ₁ := φ) (φ₂ := ψ))

/-- Inclusion of free variables through an existential quantifier. -/
def freeVarTypeIncl_ex [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ ξ : Signature Sorts}
    (φ : L.BoundedFormula α (σ ⨯ ξ)) :
    φ.freeVarType →ₛ (BoundedFormula.ex ξ φ).freeVarType := by
  simpa [BoundedFormula.ex] using
    (freeVarTypeIncl_not (φ := BoundedFormula.all ξ (BoundedFormula.not φ))
      ∘ₛ freeVarTypeIncl_all (φ := BoundedFormula.not φ)
      ∘ₛ freeVarTypeIncl_not (φ := φ))
-/

end free_var_inclusions

/-! ### Variable Reindexing -/

open Signature
open SigMap

/-- Reindexes `L.BoundedFormula α σ` as `L.BoundedFormula α τ`, given a dependent family of
embeddings `σ.IdxFam → τ.IdxFam`.

This could be a SigEmbed if we want it to model the original idea of "Moving some variables right"
-/
@[simp]
def reindex : ∀ {σ τ : Signature Sorts} (_ : SigMap σ τ ),
     L.BoundedFormula α σ → L.BoundedFormula α τ
  | _, _, _, falsum => falsum
  | _, _, h, equal t₁ t₂ =>
    equal (t₁.reindex h) (t₂.reindex h)
  | _, _, h, rel R ts => rel R (ts.reindex h)
  | _, _, h, imp f₁ f₂ => (f₁.reindex h).imp (f₂.reindex h)
  | _, _, h, all _ f => (f.reindex (h.extend_right)).all


@[simp]
lemma reindex_size {τ : Signature Sorts} (g : SigMap σ τ) (φ : L.BoundedFormula α σ) :
  (φ.reindex g).size = φ.size := by
  induction φ generalizing τ with
  | falsum => simp only [reindex, size]
  | equal t₁ t₂ => simp only [reindex, size]
  | rel r t =>
    unfold reindex Term.reindex size
    rw[Term.mapVars_size]
  | imp φ₁ φ₂ ih₁ ih₂ => simp only [reindex, size, ih₁, ih₂]
  | all τ φ ih => simp_all only [reindex, size]

@[simp]
theorem reindex_id {σ : Signature Sorts} (φ : L.BoundedFormula α σ) :
  φ.reindex SigMap.Id = φ := by
  induction φ with
  | falsum =>
      simp only [reindex]
  | @equal σ τ t₁ t₂ =>
      change equal (t₁.reindex FamMap.idₛ) (t₂.reindex FamMap.idₛ) = equal t₁ t₂
      simp_all only [Term.reindex_id]
  | @rel σ τ R ts =>
      change rel R (ts.reindex FamMap.idₛ) = rel R ts
      simp_all only [Term.reindex_id]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp_all only [reindex]
  | @all σ τ φ ih =>
      rw [BoundedFormula.reindex]
      simp_all only [SigMap.idExtend ]

@[simp]
theorem reindex_reindex : ∀ {σ τ η : Signature Sorts} (hστ : SigMap σ τ) (hτη : SigMap τ η)
                         (φ : L.BoundedFormula α σ),
    (φ.reindex hστ).reindex hτη = φ.reindex (hτη ∘ₛ hστ) := by
  intro σ τ η hστ hτη φ
  revert τ η
  induction φ with
  | falsum => intros; rfl
  | equal =>
    intro τ_1 η hστ hτη; simp_all only [reindex, Term.reindex_reindex]
  | rel =>
    intros; simp_all only [reindex, Term.reindex_reindex]
  | imp _ _ ih1 ih2 => simp only [reindex, ih1, ih2, implies_true]
  | all ι φ ih =>
        simp only [reindex,  ih, all.injEq, heq_eq_eq, true_and]
        congr!
        ext s v
        simp[extend_right]
        cases v <;> simp

@[simp]
theorem reindex_comp_reindex {σ τ η : Signature Sorts} (hστ : SigMap σ τ) (hτη : SigMap τ η) :
    (reindex hτη ∘ reindex hστ :
        L.BoundedFormula α σ → L.BoundedFormula α η) =
      BoundedFormula.reindex (hτη ∘ₛ hστ) :=
  funext (reindex_reindex hστ hτη)

/-! ### Quantifier Operations -/

/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {σ}, L.BoundedFormula α σ → L.Formula α
  | .nil , φ => φ
  --We change the shape (of s) to nil ⨯ ⦃s⦄ to prepare it for universal quantification:
  | .of s , φ => (reindex (L := L) (α:= α ) (SigEquiv.nilLeft (of s)).symm.toFun φ).all
  | .prod _ _  , φ => φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {σ}, L.BoundedFormula α σ → L.Formula α
  | .nil , φ => φ
  --We change the shape (of s) to nil ⨯ ⦃s⦄ to prepare it for existential quantification:
  | .of s , φ => (reindex (L := L) (α:= α ) (SigEquiv.nilLeft (of s)).symm.toFun φ).ex
  | .prod _ _  , φ => φ.ex.exs

/-! ### Free Variable Restriction -/

/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrictFreeVar {β : Fam Sorts} [DecidableEq Sorts] [∀ s, DecidableEq (α s)] :
    ∀ {σ : Signature Sorts} (φ : L.BoundedFormula α σ)
    (_f : φ.freeVarFam →ₛ β), L.BoundedFormula β σ
  | _, falsum, _ => falsum
  | _, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft ⟨fun {t} x => f t ⟨x.val, Finset.mem_union.mpr (Or.inl x.property)⟩⟩)
          (t₂.restrictVarLeft ⟨fun {t} x => f t ⟨x.val, Finset.mem_union.mpr (Or.inr x.property)⟩⟩)
  | _, rel R ts, f => rel R (ts.restrictVarLeft ⟨fun {t} x => f t x⟩)
  | _, imp φ₁ φ₂, f => by
    exact
      (φ₁.restrictFreeVar ⟨fun {t} => fun x => f t  ⟨x.1, Finset.mem_union.mpr (Or.inl x.2)⟩⟩).imp
      (φ₂.restrictFreeVar ⟨fun {t} => fun x => f t  ⟨x.1, Finset.mem_union.mpr (Or.inr x.2)⟩⟩)
  | _, all _ φ, f => (φ.restrictFreeVar f).all

/-! ### Mapping Operations -/

/-- Maps bounded formulas along a map of terms and a map of relations.
  TODO: This lemma is currently more restrictive than its one-sorted cousin,
  as it assumes that arity of formulas is preserved and sorts are literally the same
  on both sides -/
def mapTermRel {β : Fam Sorts} {g : Signature Sorts → Signature Sorts}
    (ft : ∀ σ ξ : Signature Sorts, L.Term (α ⊕ₛ σ.IdxFam) ξ →  L'.Term (β ⊕ₛ (g σ).IdxFam) ξ)
    (fr : ∀ σ, L.Relations σ → L'.Relations σ)
    (h : ∀ σ τ, L'.BoundedFormula β (g (σ ⨯ τ)) → L'.BoundedFormula β ((g σ) ⨯ τ)) :
    ∀ {σ}, L.BoundedFormula α σ → L'.BoundedFormula β (g σ)
  | _σ, falsum => falsum
  | _σ, equal t₁ t₂ => equal (ft _ _ t₁) (ft _ _ t₂)
  | _σ, rel R ts => rel (fr _ R) (ft _ _ ts)
  | _σ, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr h).imp (φ₂.mapTermRel ft fr h)
  | _σ, all ξ φ => (h _ _ (φ.mapTermRel ft fr h)).all ξ

@[simp]
theorem mapTermRel_mapTermRel {β : Fam Sorts} {L'' : Language Sorts}
    (ft : ∀ (σ τ : Signature Sorts), L.Term (α ⊕ₛ σ.IdxFam) τ → L'.Term (β ⊕ₛ σ.IdxFam) τ)
    (fr : ∀ σ, L.Relations σ → L'.Relations σ)
    (ft' : ∀ (σ τ : Signature Sorts), L'.Term (β ⊕ₛ σ.IdxFam) τ → L''.Term (γ ⊕ₛ σ.IdxFam) τ)
    (fr' : ∀ σ, L'.Relations σ → L''.Relations σ) {σ} (φ : L.BoundedFormula α σ) :
    ((φ.mapTermRel ft fr fun _ _ => id).mapTermRel ft' fr' fun _ _ => id) =
    φ.mapTermRel (fun _ _ => ft' _ _ ∘ ft _ _) (fun _ => fr' _ ∘ fr _ ) (fun _ _ => id)
      := by
  induction φ with
  | falsum => rfl
  | equal => simp only [mapTermRel, Function.comp_apply]
  | rel => simp only [mapTermRel, Function.comp_apply]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, ih1, ih2]
  | all _ _ ih3 => simp only [mapTermRel, id_eq, ih3]

@[simp]
theorem mapTermRel_id_id_id {σ} (φ : L.BoundedFormula α σ) :
    (φ.mapTermRel (fun _ _ => id) (fun _ => id) fun _ _=> id) = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp only [mapTermRel, id_eq]
  | rel => simp only [mapTermRel, id_eq]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, ih1, ih2]
  | all _ _ ih3 => simp only [mapTermRel, ih3, id_eq]

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps!]
def mapTermRelEquiv
    {β : Fam Sorts}
    (ft : ∀ (σ τ : Signature Sorts),
      L.Term (α ⊕ₛ σ.IdxFam) τ ≃ L'.Term (β ⊕ₛ σ.IdxFam) τ)
    (fr : ∀ σ, L.Relations σ ≃ L'.Relations σ) {σ} :
    L.BoundedFormula α σ ≃ L'.BoundedFormula β σ :=
  ⟨
    mapTermRel (fun σ τ => ft σ τ) (fun σ => fr σ) fun _ _ => id,
    mapTermRel (fun σ τ => (ft σ τ).symm) (fun σ => (fr σ).symm) fun _ _ => id,
    fun φ => by simp only [mapTermRel_mapTermRel, _root_.Equiv.symm_comp_self, mapTermRel_id_id_id],
    fun φ => by simp only [mapTermRel_mapTermRel, _root_.Equiv.self_comp_symm, mapTermRel_id_id_id]
  ⟩


/-! ### Variable Renaming -/

variable {β : Fam Sorts}

/--
Renames the named free variables in a bounded formula.
-/
def rename (f : α →ₛ β) :
    L.BoundedFormula α σ → L.BoundedFormula β σ :=
  mapTermRel
    -- Apply Term.rename (formerly relabel_left) to terms
    (fun _ _ t => t.rename f)
    -- Relations stay the same
    (fun _ R => R)
    -- Quantifiers are the same as before
    (fun _ _ φ => φ)

@[simp]
lemma rename_rel {η : Signature Sorts}
    {g : α →ₛ β}
    {r : L.Relations σ}
    {t : L.Term (α ⊕ₛ η.IdxFam) σ} :
    (rel r t).rename g = rel r (Term.rename g t) := by
    rfl

@[simp]
lemma rename_equal {η : Signature Sorts}
    {g : α →ₛ β}
    {t₁ t₂ : L.Term (α ⊕ₛ η.IdxFam) σ} :
    (equal t₁ t₂).rename g = equal (t₁.rename g) (t₂.rename g) := by
    rfl

@[simp]
lemma rename_falsum
    {g : α →ₛ β}
    :
    (falsum : L.BoundedFormula α σ).rename g = falsum := by
    simp only [rename, mapTermRel]

@[simp]
lemma rename_imp {g : α →ₛ β} (φ ψ : L.BoundedFormula α σ) :
  (φ.imp ψ).rename g = (φ.rename g).imp (ψ.rename g) := by
  simp only [rename, mapTermRel]

@[simp]
lemma rename_all {σ τ : Signature Sorts} {g : α →ₛ β} (φ : L.BoundedFormula α (σ ⨯ τ)) :
  φ.all.rename g = (φ.rename g).all := by
  unfold rename
  simp[mapTermRel]

/-- Renaming with Id is the identity map. -/
@[simp]
theorem rename_id (φ : BoundedFormula L α σ) :
    φ.rename (Fam.FamMap.idₛ) = φ := by
  induction φ
  · simp only [rename_falsum]
  · simp only [rename_equal, Term.rename_id]
  · simp only [rename_rel, Term.rename_id]
  · simp_all only [rename_imp]
  · simp_all only [rename, Term.rename_id, mapTermRel]

/-- Iterating rename. -/
@[simp]
theorem rename_rename (φ : BoundedFormula L α σ) (f : α →ₛ β) (g : β →ₛ γ) :
    (φ.rename f).rename g = φ.rename (g ∘ₛ f) := by
  induction φ <;> simp_all only [rename, mapTermRel, Term.rename_rename]

@[simp]
lemma reindex_rename {τ : Signature Sorts}
    (g : SigMap σ τ)
    (φ : L.BoundedFormula α σ)
    (f : α →ₛ β) :
    (φ.rename f).reindex g = (φ.reindex g).rename f := by
  induction φ generalizing τ with
  | falsum =>
      simp only [rename, mapTermRel, reindex]
  | equal t₁ t₂ =>
      simp only [rename, mapTermRel, reindex, Term.reindex_rename]
  | rel R ts =>
      simp only [rename, mapTermRel, reindex, Term.reindex_rename]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [rename, mapTermRel, reindex, imp.injEq]
      apply And.intro
      · apply @ih₁
      · apply @ih₂
  | all η φ ih =>
      simpa only [rename, mapTermRel, reindex, all.injEq, heq_eq_eq, true_and] using
  congrArg (fun x => (BoundedFormula.all η x)) (ih (g.extend_right))

/-- An injective variable renaming operation acts injectively on boundedformulas. -/
theorem rename_injective_of_injective {f : α →ₛ β}
   (h : ∀ s, Function.Injective (f s)) :
    Function.Injective (rename f : L.BoundedFormula α σ → L.BoundedFormula β σ) := by
  intro φ ψ heq
  induction φ with
  | falsum =>
    cases ψ <;> simp_all
  | equal t₁ t₂ =>
    rw [rename_equal] at heq
    cases ψ with
    | falsum | rel | imp | all => simp_all
    | equal =>
      rw [rename_equal] at heq
      simp only [equal.injEq] at heq
      obtain ⟨h_sort, h₁, h₂⟩ := heq
      subst h_sort
      simp only [heq_eq_eq] at h₁ h₂
      congr 1
      · exact Term.rename_injective_of_injective h h₁
      · exact Term.rename_injective_of_injective h h₂
  | rel R ts =>
    cases ψ with
    | falsum | equal | imp | all => simp_all
    | rel =>
      rw [rename_rel, rename_rel] at heq
      simp only [rel.injEq] at heq ⊢
      obtain ⟨hsort, hrel, hts⟩ := heq
      subst hsort hrel
      simp_all only [heq_eq_eq, true_and]
      apply Term.rename_injective_of_injective h at hts
      exact hts
  | imp φ₁ φ₂ ih₁ ih₂ =>
    cases ψ with
    | falsum | equal | rel | all => simp_all
    | imp ψ₁ ψ₂ =>
      rw [rename_imp, rename_imp] at heq
      simp_all only [imp.injEq]
      obtain ⟨heq₁, heq₂⟩ := heq
      apply And.intro
      · apply ih₁
        simp_all only
      · apply ih₂
        simp_all only
  | all τ φ' ih =>
    cases ψ with
    | falsum | equal | rel | imp => simp_all
    | all η ψ =>
      rw [rename_all, rename_all] at heq
      simp_all only [all.injEq]
      simp_all only [true_and]
      obtain ⟨left, right⟩ := heq
      subst left
      simp_all only [heq_eq_eq]
      apply ih
      simp_all only


/-! ### Substitution -/

/--
Substitutes the free variables in a given formula with terms.

Note: `f` provides terms that may contain bound variables from `σ`.
This gives an avenue to passing named variables across to indexed
variables in a bounded formula, namely by having `f` map some `α s`
names to terms of the form `Term.var (Sum.inl v)` where `v : σ.IdxFam s`.
-/
def subst {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    L.BoundedFormula β σ :=
  match φ with
  | falsum => falsum
  | equal t₁ t₂ =>
      equal (t₁.subst f) (t₂.subst f)
  | rel R ts =>
      rel R (ts.subst f)
  | imp φ₁ φ₂ =>
      (φ₁.subst f).imp (φ₂.subst f)
  | all τ φ =>
      let f' : α →ₛ L.Term₁ (β ⊕ₛ (σ ⨯ τ).IdxFam) :=
        ⟨fun s a => (f s a).reindex SigMap.incl_left⟩
      (φ.subst f').all

/-! ### Substitution Lemmas -/

open Term

/-- Substitutes the variables with terms given an assignment only on those variables
    occurring in the formula. -/
def substFreeVars [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (f : φ.freeVarFam →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    L.BoundedFormula β σ :=
    (φ.restrictFreeVar FamMap.idₛ).subst f

@[simp]
theorem subst_falsum (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (falsum : BoundedFormula L α σ).subst f = falsum := rfl

@[simp]
theorem subst_equal {τ : Signature Sorts} (t₁ t₂ : L.Term (α ⊕ₛ σ.IdxFam) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (equal t₁ t₂).subst f = equal (t₁.subst f) (t₂.subst f) := rfl

@[simp]
theorem subst_rel {τ : Signature Sorts} (R : L.Relations τ) (ts : L.Term (α ⊕ₛ σ.IdxFam) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (rel R ts).subst f = rel R (ts.subst f) := rfl

@[simp]
theorem subst_imp (φ₁ φ₂ : BoundedFormula L α σ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (φ₁.imp φ₂).subst f = (φ₁.subst f).imp (φ₂.subst f) := rfl

@[simp]
theorem subst_not (φ : BoundedFormula L α σ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (φ.not).subst f = (φ.subst f).not := rfl

/--
Push substitution through the universal quantifier.
Note: The substitution function `f` must be reindexed to account for the new bound variables in `τ`.
-/
@[simp]
theorem subst_all (τ : Signature Sorts) (φ : BoundedFormula L α (σ ⨯ τ))
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (φ.all).subst f = (φ.subst ⟨fun s a => (f s a).reindex SigMap.incl_left⟩).all := rfl

-- Derived Connectives (And, Or, Ex, Iff)

@[simp]
theorem subst_or (φ ψ : BoundedFormula L α σ) (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (φ.or ψ).subst f = (φ.subst f).or (ψ.subst f) := by
  simp only [BoundedFormula.or, subst_imp, subst_not]

@[simp]
theorem subst_and (φ ψ : BoundedFormula L α σ) (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (φ.and ψ).subst f = (φ.subst f).and (ψ.subst f) := by
  simp only [BoundedFormula.and, subst_not, subst_or]

@[simp]
theorem subst_iff (φ ψ : BoundedFormula L α σ) (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (φ.iff ψ).subst f = (φ.subst f).iff (ψ.subst f) := by
  simp only [BoundedFormula.iff]
  rfl

@[simp]
theorem subst_ex (τ : Signature Sorts) (φ : BoundedFormula L α (σ ⨯ τ))
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (φ.ex).subst f = (φ.subst ⟨fun s a => (f s a).reindex SigMap.incl_left⟩).ex := by
  -- `ex` is defined as `(all not).not`
  simp only [BoundedFormula.ex, subst_not, subst_all]

/-! ### Reindex Interaction Lemmas -/

@[simp]
theorem reindex_not (φ : BoundedFormula L α σ) (g : SigMap σ τ) :
    (φ.not).reindex g = (φ.reindex g).not := by
  simp only [reindex, BoundedFormula.not, imp.injEq, true_and]
  rfl

@[simp]
theorem reindex_or (φ ψ : BoundedFormula L α σ) (g : SigMap σ τ) :
    (φ.or ψ).reindex g = (φ.reindex g).or (ψ.reindex g) := by
  simp only [reindex, BoundedFormula.or, imp.injEq, and_true]
  rfl
@[simp]
theorem reindex_and (φ ψ : BoundedFormula L α σ) (g : SigMap σ τ) :
    (φ.and ψ).reindex g = (φ.reindex g).and (ψ.reindex g) := by
  simp only [reindex, BoundedFormula.and]
  rfl

@[simp]
theorem reindex_iff (φ ψ : BoundedFormula L α σ) (g : SigMap σ τ) :
    (φ.iff ψ).reindex g = (φ.reindex g).iff (ψ.reindex g) := by
  simp only [BoundedFormula.iff]
  rfl

@[simp]
theorem reindex_ex (ξ : Signature Sorts) (φ : BoundedFormula L α (σ ⨯ ξ)) (g : SigMap σ τ) :
    (φ.ex).reindex g = (φ.reindex (g.extend_right)).ex := by
  simp only [reindex, BoundedFormula.ex]
  rfl

/-! ### Relabeling -/

/--
Redefines the old `relabel` with new API:
1. Widens `σ` to `τ ⨯ σ` in `φ` with `reindex` and the mapping `σ → τ ⨯ σ`
2. Substitutes the original free variable names `α` into `β ⊕ τ`.
-/
def relabel {β : Fam Sorts} {τ : Signature Sorts}
    (g : α →ₛ β ⊕ₛ τ.IdxFam)
    (φ : L.BoundedFormula α σ) :
    L.BoundedFormula β (τ ⨯ σ) :=
  ((φ.reindex
      SigMap.incl_right --pushes the `σ`-variables of `φ` rightward
    ).rename g -- relabels the `α`-variables by `g` to be `β ⊕ₛ τ.IdxFam` ones.
   ).subst
      (Fam.sumElim
        (varOf Fam.inl) --leaves the `β`-variables alone
        ⟨fun s v => Term.var s (Sum.inr (.left v))⟩ --pushes the `τ`-vars to the indexed product
      )


--TODO: resolve Equiv namespace conflicts between Language and _root_
--because at present we have to write _root_.Equiv to refer to regular Equiv namespace.
def relabelEquiv (e : α ≃ₛ β) {σ : Signature Sorts} :
    L.BoundedFormula α σ ≃ L.BoundedFormula β σ :=
  mapTermRelEquiv
    (fun σ _ =>
      Term.mapVarsEquiv (α := α ⊕ₛ σ.IdxFam) (β := β ⊕ₛ σ.IdxFam)
        (MSEquiv.sumCongr e MSEquiv.refl))
    (fun _ => _root_.Equiv.refl (L.Relations _))

  /-
  (ft :=
      fun σ _ =>
        Term.mapVarsEquiv (α := α ⊕ₛ σ.IdxFam) (β := β ⊕ₛ σ.IdxFam)
          (MSEquiv.sumCongr e MSEquiv.refl)
  )
  (fr := fun _σ => _root_.Equiv.refl _)
  -/
@[simp]
theorem relabel_falsum {β : Fam Sorts} {τ : Signature Sorts}
    {g : α →ₛ β ⊕ₛ τ.IdxFam} {σ : Signature Sorts} :
    (falsum : L.BoundedFormula α σ).relabel (τ := τ) g = falsum :=
  rfl

@[simp]
theorem relabel_bot {β : Fam Sorts} {τ : Signature Sorts}
    {g : α →ₛ β ⊕ₛ τ.IdxFam} {σ : Signature Sorts} :
    (⊥ : L.BoundedFormula α σ).relabel (τ := τ) g = ⊥ :=
  rfl

@[simp]
theorem relabel_imp {β : Fam Sorts} {τ : Signature Sorts}
    {g : α →ₛ β ⊕ₛ τ.IdxFam} {σ : Signature Sorts} (φ ψ : L.BoundedFormula α σ) :
    (φ.imp ψ).relabel (τ := τ) g =
      (φ.relabel (τ := τ) g).imp (ψ.relabel (τ := τ) g) :=
  rfl

@[simp]
theorem relabel_not {β : Fam Sorts} {τ : Signature Sorts}
    {g : α →ₛ β ⊕ₛ τ.IdxFam} {σ : Signature Sorts} (φ : L.BoundedFormula α σ) :
    (φ.not).relabel (τ := τ) g =
      (φ.relabel (τ := τ) g).not := by
  simp only [BoundedFormula.not, relabel_imp, relabel_bot]

/--
Commutation of reindexing and substitution.
Reindexing a formula by `g` and then substituting is the same as
substituting first (with reindexed terms) and then reindexing the result.
-/
@[simp]
lemma reindex_subst {β : Fam Sorts} {σ τ : Signature Sorts}
    (g : SigMap σ τ)
    (φ : L.BoundedFormula α σ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.IdxFam)) :
    (φ.subst f).reindex g =
    (φ.reindex g).subst ⟨fun s a => (f s a).reindex g⟩ := by
  induction φ generalizing τ with
  | falsum => simp only [subst, reindex, subst_falsum]
  | equal t₁ t₂ =>
      simp only [subst, reindex, Term.reindex_subst]
  | rel R ts =>
      simp only [subst, reindex, Term.reindex_subst]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [subst, reindex, ih₁, ih₂, subst_imp]
  | all η φ ih =>
      simp only [subst, reindex]
      rw [ih (g.extend_right)]
      congr
      funext s a
      simp_all only [extend_right, FamMap.mk_apply, Term.reindex_reindex]
      rfl


/--
This lemma is only true up to associativity, so we have to apply prodAssocR to generalize it.
-/
@[simp]
theorem relabel_all {β : Fam Sorts}
    (τ : Signature Sorts) (g : α →ₛ (β ⊕ₛ τ.IdxFam))
    {σ ξ : Signature Sorts}
    (φ : L.BoundedFormula α (σ ⨯ ξ)) :
    (φ.all).relabel g =
      ((φ.relabel g).reindex (SigMap.assocR τ σ ξ )).all
:= by
  unfold BoundedFormula.relabel
  simp only [reindex, extend_right, incl_right_apply, rename_all, subst_all, reindex_subst,
    reindex_rename, reindex_reindex, all.injEq, heq_eq_eq, true_and]
  congr 2
  · congr
    ext s v
    cases v
    case left => rfl
    case right => rfl
  · ext s v
    simp only [assocR]
    cases v
    case inl => rfl
    case inr => rfl

syntax "reduce_formula" : tactic

macro_rules
  | `(tactic| reduce_formula) =>
      `(tactic|
        simp (config := { zeta := true }) only [
          MSFirstOrder.Language.BoundedFormula.rename,
          MSFirstOrder.Language.BoundedFormula.relabel,
          MSFirstOrder.Language.BoundedFormula.subst,
          MSFirstOrder.Language.BoundedFormula.reindex,
          MSFirstOrder.Language.BoundedFormula.mapTermRel_id_id_id
        ];
        repeat simp only [MSFirstOrder.Language.BoundedFormula.mapTermRel_mapTermRel]
      )

/-! ### Block Swapping for Variable Rearrangement -/

/--
Swaps the middle and right blocks in a three-way product: `(σ·τ)·η ≃ (σ·η)·τ`.

This equivalence rearranges bound variables by swapping the positions of `τ` and `η`
while keeping `σ` fixed in the leftmost position. Implemented as a composition of
associativity and commutativity transformations:
1. Reassociate: `((σ·τ)·η) ≃ (σ·(τ·η))`
2. Swap right pair: `(σ·(τ·η)) ≃ (σ·(η·τ))`
3. Reassociate back: `(σ·(η·τ)) ≃ ((σ·η)·τ)`

⨯⨯Use case⨯⨯: Variable rearrangement during quantifier manipulation, particularly when
reordering nested quantifiers or when preparing formulas for normal forms.
-/
def block_swap {σ τ η : Signature Sorts} :
  SigEquiv ((σ ⨯ τ) ⨯ η) ((σ ⨯ η) ⨯ τ) :=
          SigEquiv.trans
            (SigEquiv.trans
              (SigEquiv.assocL σ τ η) -- ((σ ⨯ τ) ⨯ η) ≃ (σ ⨯ (τ ⨯ η))
              (SigEquiv.prod_congr SigEquiv.Id SigEquiv.comm) -- (σ ⨯ (τ ⨯ η)) ≃  (σ ⨯ (η ⨯ τ))
            )
            (SigEquiv.assocR σ η τ)

@[simp] lemma block_swap_left_left {σ τ η : Signature Sorts} {s : Sorts}
    (v : σ.IdxFam s) :
    (block_swap : Fam.MSEquiv ((σ ⨯ τ) ⨯ η).IdxFam ((σ ⨯ η) ⨯ τ).IdxFam)   s (.left (.left v)) =
    (.left (.left v)) := by
  rfl

@[simp] lemma block_swap_left_right {σ τ η : Signature Sorts} {s : Sorts}
    (v : τ.IdxFam s) :
    block_swap (σ := σ) (τ := τ) (η := η) s (.left (.right v)) = (.right v) := by
  rfl

@[simp] lemma block_swap_right {σ τ η : Signature Sorts} {s : Sorts}
    (v : η.IdxFam s) :
    block_swap (σ := σ) (τ := τ) (η := η) s (.right v) = (.left (.right v)) := by
  rfl

@[simp] lemma block_swap_symm_left_left {σ τ η : Signature Sorts} {s : Sorts}
    (v : σ.IdxFam s) :
    (block_swap (σ := σ) (τ := τ) (η := η)).symm s (.left (.left v)) = (.left (.left v)) := by
  rfl

@[simp] lemma block_swap_symm_right {σ τ η : Signature Sorts} {s : Sorts}
    (v : τ.IdxFam s) :
    (block_swap (σ := σ) (τ := τ) (η := η)).symm s (.right v) = (.left (.right v)) := by
  rfl

@[simp] lemma block_swap_symm_left_right {σ τ η : Signature Sorts} {s : Sorts}
    (v : η.IdxFam s) :
    (block_swap (σ := σ) (τ := τ) (η := η)).symm s (.left (.right v)) = (.right v) := by
  rfl

@[simp] lemma block_swap_block_swap {σ τ η : Signature Sorts} {s : Sorts}
    (x : ((σ ⨯ τ) ⨯ η).IdxFam s) :
    block_swap (σ := σ) (τ := η) (η := τ) s (block_swap (σ := σ) (τ := τ) (η := η) s x) = x := by
  cases x with
  | left x =>
      cases x with
      | left v  => simp only [block_swap_left_left]
      | right v => simp only [block_swap_left_right, block_swap_right]
  | right v =>
      simp only [block_swap_right, block_swap_left_right]

/-! ### Opening and Closing Variables -/

/--
Opens bound variables in a formula by splitting the rightmost block of quantified variables.

Transforms a bounded formula `L.BoundedFormula α (σ ⨯ τ)` into
`L.BoundedFormula (α ⊕ₛ τ.IdxFam) σ` by converting the `τ` block of bound variables into free
variables. This is the formula-level equivalent of `Term.openVars`.

⨯⨯Transformation:⨯⨯
- Free variables `α` remain free
- Bound variables from `τ` (rightmost block) become free variables: `α ⊕ₛ τ.IdxFam`
- Bound variables from `σ` (leftmost block) remain bound

⨯⨯Use case⨯⨯: Opening quantifiers for substitution. For example, to substitute into
`∀ x ∀ y. φ(x,y)`,
first open the `y` quantifier to get `∀ x. φ(x, y_free)`, then substitute for `y_free`.

This operation is inverted by `closeVars` or `instantiate`.
-/
def openVars {σ τ : Signature Sorts} :
    L.BoundedFormula α (σ ⨯ τ) → L.BoundedFormula (α ⊕ₛ τ.IdxFam) σ
  | .falsum => .falsum
  | .imp φ₁ φ₂ => .imp (openVars φ₁) (openVars φ₂)
  | .equal t₁ t₂ => .equal t₁.openVars t₂.openVars
  | .rel R ts => .rel R ts.openVars
  | .all η φ =>
      let φ' := (φ.reindex block_swap.toFun).openVars
      φ'.all η
termination_by
  φ => φ.size

/-- Inverse for openVars along a map from a right free variable factor back to IdxFams. -/
def closeVars {σ τ : Signature Sorts} {X : Fam Sorts}
  (f : X →ₛ τ.IdxFam) :
  L.BoundedFormula (α ⊕ₛ X) σ → L.BoundedFormula α (σ ⨯ τ)
| φ =>
    let g : (α ⊕ₛ X) →ₛ (α ⊕ₛ τ.IdxFam) :=
      Fam.sumElim Fam.inl (Fam.inr ∘ₛ f)
    (φ.relabel g).reindex SigEquiv.comm.toFun

@[simp]
lemma closeVars_falsum {σ τ : Signature Sorts} {X : Fam Sorts} (f : X →ₛ τ.IdxFam) :
  (falsum : L.BoundedFormula (α ⊕ₛ X) σ).closeVars f = falsum := by
  simp only [closeVars, relabel_falsum, reindex]

@[simp]
lemma closeVars_imp {σ τ : Signature Sorts} {X : Fam Sorts} (f : X →ₛ τ.IdxFam)
    {φ₁ φ₂ : L.BoundedFormula (α ⊕ₛ X) σ} :
  (φ₁.imp φ₂).closeVars f = (φ₁.closeVars f).imp (φ₂.closeVars f) := by
  simp only [closeVars, relabel_imp, reindex]

@[simp]
lemma closeVars_all {σ τ η : Signature Sorts} {X : Fam Sorts} (f : X →ₛ τ.IdxFam)
    {φ : L.BoundedFormula (α ⊕ₛ X) (σ ⨯ η)} :
  (φ.all).closeVars f = ((φ.closeVars f).reindex block_swap.toFun).all η := by
  unfold closeVars
  simp only [relabel_all, reindex, extend_right, reindex_reindex, all.injEq, heq_eq_eq,
    true_and]
  set ψ := (relabel (Fam.sumElim { toFun := fun x a ↦ Sum.inl a }
    {toFun := fun s x ↦ Sum.inr (f s x) }) φ)
    with hψ
  congr 1
  ext s a
  match a with
  | .left v => simp_all only [FamMap.comp_apply', FamMap.mk_apply, ψ]; rfl
  | .right v =>
    match v with
    | .left w => simp_all only [FamMap.comp_apply', FamMap.mk_apply, ψ]; rfl
    | .right w => simp_all only [FamMap.comp_apply', FamMap.mk_apply, ψ]; rfl

theorem inductionOn_size {τ : Signature Sorts}
    {C : ∀ {α : Fam.{u'} Sorts} {σ τ : Signature Sorts},
        L.BoundedFormula α (σ ⨯ τ) → Prop}
    {α_inner : Fam.{u'} Sorts} {σ_inner : Signature Sorts}
    (φ : L.BoundedFormula α_inner (σ_inner ⨯ τ))
    (h :
      ∀ {α τ} {σ : Signature Sorts} (φ : L.BoundedFormula α (σ ⨯ τ)),
        (∀ {α'} {σ' τ' : Signature Sorts} (ψ : L.BoundedFormula α' (σ' ⨯ τ')),
          ψ.size < φ.size → C ψ) → C φ) :
    C φ :=
  h φ (fun {α' σ' τ'} ψ _ => inductionOn_size ψ h)
termination_by φ.size


lemma openVars_closeVars {σ τ : Signature Sorts} (φ : L.BoundedFormula α (σ ⨯ τ)) :
  φ.openVars.closeVars (FamMap.idₛ : τ.IdxFam →ₛ τ.IdxFam) = φ := by
  -- generalizing α is crucial here because the recursive step changes the type of α
  apply inductionOn_size φ
  intro α σ τ φ ih
  cases φ with
  | falsum =>
      simp_all only [closeVars, openVars, size, Nat.lt_one_iff]
      rfl
  | imp φ₁ φ₂ =>
    have h₁ := ih φ₁ (by simp only [size]; linarith)
    have h₂ := ih φ₂ (by
      simp only [size, lt_add_iff_pos_left, add_pos_iff, _root_.zero_lt_one, true_or])
    simp only [openVars, closeVars_imp, h₁, h₂]
  | equal t₁ t₂ =>
    simp only [closeVars, relabel, rename, Fam.FamMap.idₛ, openVars, reindex, mapTermRel,
      subst_equal, rename_subst,  equal.injEq, heq_eq_eq, true_and]
    simp only [Term.reindex, Term.subst, Term.openVars, Term.bind_bind, mapVars]
    constructor <;>
      { apply Term.bind_id _
        intro s a;
        --simp_all only [size, Nat.lt_one_iff, FamMap.idₛ_apply'];
        cases a with
        | inl val => simp_all only [FamMap.mk_apply, bind_bind, Term.bind]; rfl
        | inr val =>
            simp_all only [size, Nat.lt_one_iff, FamMap.mk_apply, bind_bind, Term.bind]
            cases val <;> rfl
      }
  | rel R ts =>
    simp only [closeVars, relabel, Fam.FamMap.idₛ,  openVars, reindex, rename_rel, subst_rel,
      rename_subst, rel.injEq, heq_eq_eq, true_and]
    reduce_term_to_bind
    apply Term.bind_id
    intro s a
    simp_all only [size, FamMap.comp_apply', FamMap.mk_apply,  bind_bind, Term.bind]
    cases a
    · rfl
    · rename_i val
      cases val <;> rfl
  | all η φ =>
    rw [openVars]
    simp only [closeVars_all, all.injEq, heq_eq_eq, true_and]
    have ih' := ih (reindex block_swap.toFun φ) (by simp only [reindex_size, size,
      lt_add_iff_pos_left, _root_.zero_lt_one])
    simp only [ih', reindex_reindex]
    set g := (block_swap.toFun ∘ₛ block_swap.toFun) with hg
    have hg':  g = FamMap.idₛ := by
      ext s v;  simp only [hg, FamMap.comp_apply', FamMap.idₛ_apply']
      change block_swap s (block_swap s v) = v
      simp
    rw[hg']
    simp_all only [size, reindex_size, lt_add_iff_pos_left, _root_.zero_lt_one, reindex_id, g]

/--
General version: `closeVars` followed by `openVars` is syntactically just renaming the free
variables `α ⊕ₛ X` into `α ⊕ₛ τ.IdxFam` by sending `X` along `f`.

This is the main rewriting lemma used to prove `realize_closeVars` cleanly.
-/
lemma closeVars_openVars {σ τ : Signature Sorts} {X : Fam Sorts}
    (f : X →ₛ τ.IdxFam)
    (φ : L.BoundedFormula (α ⊕ₛ X) σ) :
    (φ.closeVars (α := α) (σ := σ) (τ := τ) f).openVars
      =
    φ.rename (Fam.sumMap FamMap.idₛ f) := by
  induction φ with
  | falsum =>
      simp only [closeVars_falsum, openVars, rename, mapTermRel]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [closeVars_imp, openVars]
      rw [ih₁, ih₂]
      simp only [rename, mapTermRel]
  | @equal σ₀ ξ t₁ t₂ =>
      unfold closeVars openVars
      reduce_formula
      simp only [mapTermRel, subst_equal, reindex, equal.injEq, heq_eq_eq,
        true_and]
      reduce_term_to_bind
      constructor <;>
      { congr 2
        ext x y
        cases y
        · case inl w =>
          cases w
          · simp_all only [Term.bind, FamMap.mk_apply, FamMap.comp_apply']
            rfl
          · simp_all only [FamMap.mk_apply, Term.bind, sumMap_inl_apply, FamMap.idₛ_apply',
              Sum.elim_inr, FamMap.comp_apply', Sum.elim_inl, bind_bind, sumMap_inr_apply]
            rfl
        · case inr =>
            simp_all only [FamMap.mk_apply, Term.bind, sumMap_inr_apply, incl_right_apply,
              FamMap.idₛ_apply', Sum.elim_inr, FamMap.comp_apply']
            rfl
      }
  | @rel σ' τ' R ts =>
      simp only [closeVars, relabel, rename, reindex, mapTermRel, subst_rel, rename_subst, openVars,
        rel.injEq, heq_eq_eq, true_and]
      reduce_term_to_bind
      congr 2
      ext x y : 2
      cases y
      case inl w =>
        cases w
        case inl v =>
          simp_all only [Term.bind, FamMap.mk_apply, FamMap.comp_apply', bind_bind]
          rfl
        case inr _ =>
          simp_all only [Term.bind, FamMap.mk_apply, FamMap.comp_apply', bind_bind,
            ]
          rfl
      case inr w =>
        cases w
        <;> simp_all only [Term.bind, FamMap.mk_apply, FamMap.comp_apply']
        <;> rfl
  | all η ψ ih =>
    simp only [closeVars, relabel_all, reindex, reindex_reindex] at *
    simp only [rename, openVars, reindex_reindex, mapTermRel, all.injEq, heq_eq_eq, true_and] at *
    rw[← ih]
    congr
    ext s x; cases x
    case left v => simp_all only [extend_right]; rfl
    case right v => cases v <;> simp_all only [extend_right] <;> rfl

@[simp]
lemma closeVars_openVars_id {σ τ : Signature Sorts}
    (φ : L.BoundedFormula (α ⊕ₛ τ.IdxFam) σ) :
    (φ.closeVars (α := α) (σ := σ) (τ := τ) (FamMap.idₛ : τ.IdxFam →ₛ τ.IdxFam)).openVars
      =
    φ := by
  rw [closeVars_openVars]
  simp

/-! ### From Boundedformulas to Formulas -/

def toFormula {σ : Signature Sorts} (φ : L.BoundedFormula α σ) : L.Formula (α ⊕ₛ σ.IdxFam) :=
  (φ.reindex SigMap.nil_left_inv).openVars

def fromFormula {σ : Signature Sorts} (φ : L.Formula (α ⊕ₛ σ.IdxFam)) : L.BoundedFormula α σ :=
  (φ.closeVars FamMap.idₛ).reindex SigMap.nil_left

@[simp]
lemma fromFormula_toFormula {σ : Signature Sorts} (φ : L.BoundedFormula α σ) :
    φ.toFormula.fromFormula = φ := by
  rw [toFormula, fromFormula, openVars_closeVars, reindex_reindex]
  apply reindex_id

@[simp]
lemma toFormula_fromFormula {σ : Signature Sorts} (φ : L.Formula (α ⊕ₛ σ.IdxFam)) :
    (fromFormula φ).toFormula = φ := by
  rw [toFormula, fromFormula, reindex_reindex]
  have :  FamMap.comp (base := Sorts) (α := (⦃⦄ ⨯ σ).IdxFam) nil_left_inv  nil_left = FamMap.idₛ :=
    by ext s x; rw [FamMap.comp_apply', nil_left_left_inv, FamMap.idₛ_apply']
  rw [this, reindex_id, closeVars_openVars_id]



/-! ### Instantiation and Witnesses -/

/--
Substitute a term `u` of shape `τ` into the `τ` variables of `φ`:
-/
def instantiate {σ τ : Signature Sorts} :
    L.BoundedFormula α (σ ⨯ τ)
    → L.Term (α ⊕ₛ σ.IdxFam) τ →
       L.BoundedFormula α σ :=
    fun φ t =>
      φ.openVars.subst (Fam.sumElim (varOf Fam.inl) (fun s a => t.getLeafTerm s a))

/--
An unqualified version of instantiate that completely eliminates all bound variables to
return a Formula.
-/
def fully_instantiate {τ : Signature Sorts} :
    L.BoundedFormula α τ
    → L.Term (α ⊕ₛ nil.IdxFam) τ →
       L.Formula α :=
    fun φ t =>
     (φ.reindex SigMap.nil_left_inv).instantiate t

def has_witness (T : L.Theory) (φ : L.BoundedFormula Fam.EmptyFam (of s)) : Prop :=
      ∃ c : L.Constants s,
        φ.fully_instantiate c.term ∈ T ↔ φ.exs ∈ T

/-! ### Constants and Variables Equivalence -/

section constants_vars_equiv

variable {γ : Fam.{u'} Sorts}

/-- A bijection sending formulas with constants to formulas with extra variables. -/
def constantsVarsEquiv {σ : Signature Sorts} {γ : Fam Sorts} :
    (L[[γ]]).BoundedFormula α σ ≃ L.BoundedFormula (γ ⊕ₛ α) σ :=
  BoundedFormula.mapTermRelEquiv
    (L := L[[γ]]) (L' := L)
    (α := α) (β := γ ⊕ₛ α)
    (ft := fun σ' _ => Term.constantsVarsEquivLeft (β := σ'.IdxFam))
    (fr := fun _ => Equiv.sumEmpty _ _)

end constants_vars_equiv

/-! ### Finite Meets and Joins -/


/--
Indexed AND `⋀ [φ₁, φ₂, ...]` from a list
-/
def bigAnd (l : List (L.BoundedFormula α σ)) : L.BoundedFormula α σ :=
  l.foldr (· ⊓ ·) ⊤

/--
Indexed OR `⋁ [φ₁, φ₂, ...]` from a list
-/
def bigOr (l : List (L.BoundedFormula α σ)) : L.BoundedFormula α σ :=
  l.foldr (· ⊔ ·) ⊥

-- Notation
prefix:110 "⋀ " => bigAnd
prefix:110 "⋁ " => bigOr

/-- Take the disjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iSup {X} [Finite X] (f : X → L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  let _ := Fintype.ofFinite X
  ⋁ ((Finset.univ : Finset X).toList.map f)

/-- Take the conjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iInf {X} [Finite X] (f : X → L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  let _ := Fintype.ofFinite X
  ⋀ ((Finset.univ : Finset X).toList.map f)

theorem bigAnd_nil : ⋀ ([] : List (L.BoundedFormula α σ)) = ⊤ := rfl

theorem bigOr_nil : ⋁ ([] : List (L.BoundedFormula α σ)) = ⊥ := rfl



/-! ### Localization of Formulas -/

section localize_formula

variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)]

/-- A localization of a bounded formula is a signature `τ` together with an equivalence
between the formula's free-variable family and `τ.IdxFam`. This packages the data needed
to replace named free variables with signature-indexed ones. -/
structure LocalForm {σ : Signature Sorts} (φ : L.BoundedFormula α σ) where
  τ : Signature Sorts
  e : φ.freeVarFam ≃ₛ τ.IdxFam

namespace LocalForm

variable {σ : Signature Sorts} {φ : L.BoundedFormula α σ} (lf : φ.LocalForm)

/-- The localized bounded formula: free variables replaced by `τ.IdxFam`. -/
def toFormula : L.BoundedFormula lf.τ.IdxFam σ :=
  φ.restrictFreeVar lf.e

/-- The derived closed bounded formula: free variables become bound in signature `τ`.
    Only available when `σ = nil` (i.e. for `Formula`). -/
def toBoundedFormula {φ : L.Formula α} (lf : φ.LocalForm) : L.BoundedFormula Fam.EmptyFam lf.τ :=
  let φ_restricted : L.BoundedFormula φ.freeVarFam Signature.nil :=
    φ.restrictFreeVar FamMap.idₛ
  let φ_renamed : L.BoundedFormula lf.τ.IdxFam Signature.nil :=
    φ_restricted.rename lf.e.toFun
  let φ_sum : L.BoundedFormula (Fam.EmptyFam ⊕ₛ lf.τ.IdxFam) Signature.nil :=
    φ_renamed.rename ⟨fun _ => Sum.inr⟩
  (φ_sum.closeVars (FamMap.idₛ : lf.τ.IdxFam →ₛ lf.τ.IdxFam)).reindex (SigEquiv.nilLeft lf.τ).toFun

end LocalForm

/-- Canonical localization via `famToSignature`. -/
noncomputable def localize (φ : L.BoundedFormula α σ) : φ.LocalForm :=
  ⟨(Signature.famToSignature φ.freeVarFam.Subtype).1,
   (Signature.famToSignature φ.freeVarFam.Subtype).2⟩

/-- Manual localization from a user-supplied equivalence. -/
def localizeBy (φ : L.BoundedFormula α σ) (τ : Signature Sorts)
    (e : φ.freeVarFam ≃ₛ τ.IdxFam) : φ.LocalForm :=
  ⟨τ, e⟩

end localize_formula

end BoundedFormula

namespace Formula

variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)]

/-- A localization of a formula. Specializes `BoundedFormula.LocalForm` at `σ = nil`. -/
abbrev LocalForm (φ : L.Formula α) := BoundedFormula.LocalForm φ

/-- Canonical localization of a formula via `famToSignature`. -/
noncomputable abbrev localize (φ : L.Formula α) := BoundedFormula.localize φ

/-- Manual localization of a formula from a user-supplied equivalence. -/
abbrev localizeBy (φ : L.Formula α) := BoundedFormula.localizeBy φ

end Formula

/-! ## Language Homomorphisms and Equivalences -/

namespace LHom

open BoundedFormula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
def onBoundedFormula (g : L →ᴸ L') :
    ∀ {ξ : Signature Sorts}, L.BoundedFormula α ξ → L'.BoundedFormula α ξ
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
theorem comp_onBoundedFormula {L'' : Language Sorts} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α σ → L''.BoundedFormula α σ) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula := by
  ext f
  induction f with
  | falsum => rfl
  | equal => simp only [onBoundedFormula, Term.bdEqual, comp_onTerm, Function.comp_apply]
  | rel => simp only [onBoundedFormula, Relations.boundedFormula, comp_onRelation, comp_onTerm,
    Function.comp_apply]
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

@[inherit_doc] scoped[MSFirstOrder] infixl:88 " =' " => MSFirstOrder.Language.Term.bdEqual
-- input \~- or \simeq

@[inherit_doc] scoped[MSFirstOrder] infixr:62 " ⟹ " => MSFirstOrder.Language.BoundedFormula.imp
-- input \==>

--@[inherit_doc] scoped[MSFirstOrder] prefix:110 "∀'" => MSFirstOrder.Language.BoundedFormula.all
-- input \forall'

/-! ## Notation -/

variable (l : List ℕ)

@[inherit_doc] scoped[MSFirstOrder] prefix:arg "∼" => MSFirstOrder.Language.BoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[MSFirstOrder] infixl:61 " ⇔ " => MSFirstOrder.Language.BoundedFormula.iff
-- input \<=>

--@[inherit_doc] scoped[MSFirstOrder] prefix:110 "∃'" => MSFirstOrder.Language.BoundedFormula.ex
-- input \ex'

/-! ## Formula Operations -/

namespace Formula

/-- Relabels a formula's variables along a particular function.
    Much simpler to define via `BoundedFormula.rename` rather than
    the previous one with `relabel`.
-/
def rename {β : Fam Sorts} (g : α →ₛ β) : L.Formula α → L.Formula β :=
  BoundedFormula.rename g

/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions σ s) : L.Formula (σ ⨯ ⦃s⦄).IdxFam :=
  Term.equal (.var s (.right .var)) (.func f ((Term.varTerm σ).mapVars ⟨@Idx.left _ _ _ ⟩))


/-- The negation of a formula. -/
protected nonrec abbrev not (φ : L.Formula α) : L.Formula α :=
  φ.not

/-- The implication between formulas, as a formula. -/
protected abbrev imp : L.Formula α → L.Formula α → L.Formula α :=
  BoundedFormula.imp

open Signature Term FamMap

/-! ### Indexed Quantification over Free Variables -/
--TODO: Extend this so you can quantify away all the vars from a formula without the need to
--postulate that it's finite.
section free_var_quantification

variable (β : Fam Sorts) in
/-- `iAlls φ` turns `L.Formula (α ⊕ₛ β)` into `L.Formula α`
by universally quantifying all `Sum.inr _` variables. -/
noncomputable def iAlls [Finite (Sigma β)]
    (φ : L.Formula (α ⊕ₛ β)) : L.Formula α :=
by
  rcases famToSignature β with ⟨σ, e⟩
  exact
    (φ.relabel
        (Fam.sumMap (δ := σ.IdxFam) idₛ e)).alls

variable (β : Fam Sorts) in
/-- `iExs f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _`. -/
noncomputable def iExs [Finite (Sigma β)]
    (φ : L.Formula (α ⊕ₛ β)) : L.Formula α :=
by
  rcases famToSignature β with ⟨σ, e⟩
  exact
    (φ.relabel
        ⟨fun s a => Sum.map id (e s) a⟩).exs

variable (β : Fam Sorts) in
/-- `iExsUnique f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _` and asserting that the solution should be unique -/
noncomputable def iExsUnique [Finite (Sigma β)] (φ : L.Formula (α ⊕ₛ β)) : L.Formula α :=
by
  classical
  -- interpret the β-variables of φ as the right β-block in ((α ⊕ β) ⊕ β)
  let shiftβ : (α ⊕ₛ β) →ₛ ((α ⊕ₛ β) ⊕ₛ β) :=
    Fam.sumElim (Fam.inl ∘ₛ Fam.inl) Fam.inr
  -- conjunction asserting “witness β = challenger β” (pointwise over the finite Sigma β)
  let eqWitness : L.Formula ((α ⊕ₛ β) ⊕ₛ β) :=
    BoundedFormula.iInf (L := L) (X := Sigma β)
      (fun ⟨s, x⟩ =>
        Term.equal (L := L) (α := ((α ⊕ₛ β) ⊕ₛ β))
          (Term.var s (Sum.inl (Sum.inr x)))  -- witness β  (the left of (α ⊕ β))
          (Term.var s (Sum.inr x))            -- challenger β
      )
  -- uniqueness condition: ∀ challenger β, (φ[challenger] → challenger = witness)
  let uniq : L.Formula (α ⊕ₛ β) :=
    Formula.iAlls (L := L) (α := (α ⊕ₛ β)) (β := β)
      ((BoundedFormula.rename (L := L) (σ := Signature.nil) shiftβ φ).imp eqWitness)
  -- ∃ witness β, (φ ∧ uniq)
  exact Formula.iExs (L := L) (α := α) (β := β) (φ ⊓ uniq)

end free_var_quantification

/-! ### Additional Formula Operations -/

protected nonrec abbrev iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.iff ψ

/-- Take the disjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iSup {β} {X : Type _} [Finite X] (f : X → L.Formula β) : L.Formula β :=
  BoundedFormula.iSup f

/-- Take the conjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iInf {β} {X : Type _} [Finite X] (f : X → L.Formula β) : L.Formula β :=
  BoundedFormula.iInf f

/-! ### Formula-Sentence Equivalence -/

/-- A bijection sending formulas to sentences with constants. -/
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans
    (BoundedFormula.relabelEquiv
      (MSEquiv.fromEquivs
        (fun _ => Equiv.sumEmpty _ _))
    )
  ).symm

theorem equivSentence_bot : equivSentence (⊥ : L.Formula α) = ⊥ := rfl

theorem equivSentence_symm_bot : equivSentence.symm (⊥ : L[[α]].Sentence) = ⊥ :=
  equivSentence.injective equivSentence_bot.symm

theorem equivSentence_top : equivSentence (⊤ : L.Formula α) = ⊤ := rfl

theorem equivSentence_symm_top : equivSentence.symm (⊤ : L[[α]].Sentence) = ⊤ :=
  equivSentence.injective equivSentence_top.symm

theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence φ).not :=
  by
    simp only [equivSentence, BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv,
      BoundedFormula.relabelEquiv, Equiv.coe_refl, Equiv.refl_symm, BoundedFormula.not,
      Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk, BoundedFormula.mapTermRel,
      BoundedFormula.mapTermRel_mapTermRel, CompTriple.comp_eq, BoundedFormula.imp.injEq, true_and]
    rfl

theorem equivSentence_imp (φ ψ : L.Formula α) :
    equivSentence (φ ⟹ ψ) = equivSentence φ ⟹ equivSentence ψ := by
    simp only [equivSentence, BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv,
      BoundedFormula.relabelEquiv, Equiv.coe_refl, Equiv.refl_symm, Equiv.symm_trans_apply,
      Equiv.coe_fn_symm_mk, BoundedFormula.mapTermRel, BoundedFormula.mapTermRel_mapTermRel,
      CompTriple.comp_eq]

theorem equivSentence_symm_imp (φ ψ : L[[α]].Sentence) :
    equivSentence.symm (φ ⟹ ψ) = equivSentence.symm φ ⟹ equivSentence.symm ψ := by
  apply equivSentence.injective
  simp only [_root_.Equiv.apply_symm_apply, equivSentence_imp]

theorem equivSentence_symm_not (φ : L[[α]].Sentence) :
    equivSentence.symm φ.not = (equivSentence.symm φ).not := by
  apply equivSentence.injective
  simp only [_root_.Equiv.apply_symm_apply, equivSentence_not]

theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=  by
    simp only [equivSentence, BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv,
      BoundedFormula.relabelEquiv, Equiv.coe_refl, Equiv.refl_symm, Equiv.symm_trans_apply,
      Equiv.coe_fn_symm_mk, BoundedFormula.mapTermRel_mapTermRel, CompTriple.comp_eq]
    rfl

theorem equivSentence_symm_inf (φ ψ : L[[α]].Sentence) :
    equivSentence.symm (φ ⊓ ψ) = equivSentence.symm φ ⊓ equivSentence.symm ψ := by
  apply equivSentence.injective
  simp only [_root_.Equiv.apply_symm_apply, equivSentence_inf]

theorem equivSentence_sup (φ ψ : L.Formula α) :
    equivSentence (φ ⊔ ψ) = equivSentence φ ⊔  equivSentence ψ :=  by
    simp only [equivSentence, BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv,
      BoundedFormula.relabelEquiv, Equiv.coe_refl, Equiv.refl_symm, Equiv.symm_trans_apply,
      Equiv.coe_fn_symm_mk, BoundedFormula.mapTermRel_mapTermRel, CompTriple.comp_eq]
    rfl

theorem equivSentence_symm_sup (φ ψ : L[[α]].Sentence) :
    equivSentence.symm (φ ⊔ ψ) = equivSentence.symm φ ⊔ equivSentence.symm ψ := by
  apply equivSentence.injective
  simp only [_root_.Equiv.apply_symm_apply, equivSentence_sup]

theorem equivSentence_bigAnd (l : List (L.Formula α)) :
    equivSentence (BoundedFormula.bigAnd l) = ⋀ (l.map equivSentence) := by
  induction l
  case nil => simp only [BoundedFormula.bigAnd_nil, equivSentence_top, List.map_nil]
  case cons φ l ih =>
    simp only [BoundedFormula.bigAnd, List.foldr_cons, List.map_cons]
    rw [equivSentence_inf, ← BoundedFormula.bigAnd, ← BoundedFormula.bigAnd, ih]

theorem equivSentence_symm_bigAnd (l : List (L[[α]].Sentence)) :
    equivSentence.symm (⋀ l) = BoundedFormula.bigAnd (l.map equivSentence.symm) := by
  apply equivSentence.injective
  simp only [_root_.Equiv.apply_symm_apply, equivSentence_bigAnd, List.map_map,
    _root_.Equiv.self_comp_symm, List.map_id_fun, id_eq]

theorem equivSentence_bigOr (l : List (L.Formula α)) :
    equivSentence (⋁ l) = ⋁ (l.map equivSentence) := by
  induction l
  case nil =>
    simp only [BoundedFormula.bigOr_nil, List.map_nil, equivSentence_bot]
  case cons φ l ih =>
    simp only [BoundedFormula.bigOr, List.foldr_cons, List.map_cons]
    rw [equivSentence_sup, ← BoundedFormula.bigOr, ← BoundedFormula.bigOr, ih]

theorem equivSentence_symm_bigOr (l : List (L[[α]].Sentence)) :
    equivSentence.symm (⋁ l) = ⋁ (l.map equivSentence.symm) := by
  apply equivSentence.injective
  simp only [_root_.Equiv.apply_symm_apply, equivSentence_bigOr, List.map_map,
    _root_.Equiv.self_comp_symm, List.map_id_fun, id_eq]




/-! ### Using formulas as relations -/
/- Use an `L.Formula σ.Idx` the way one would use a `L.Relations σ` to build a new formula-/
--TODO: construct relevant lemmas on the semantic side
/-- Substitute terms into a `Formula`, turning it into a `Boundedformula`
  This is the analogue of `Relations.boundedFormula` -/
def boundedFormula {ξ : Signature Sorts} (φ : L.Formula σ.IdxFam)
    (ts : L.Term (α ⊕ₛ ξ.IdxFam) σ) : L.BoundedFormula α ξ :=
  let ψ  := φ.reindex (default : SigMap ⦃⦄ ξ) -- Prepare a fresh tuple of bound variables ξ
  ψ.subst ts.getLeafTerm -- Plug the given tuple of terms into ψ

/-- Applies a formula in one free variable as a unary operation -/
def boundedFormula₁ {ξ : Signature Sorts} {s : Sorts} (φ : L.Formula (of s).IdxFam)
    (t : L.Term (α ⊕ₛ ξ.IdxFam) ⦃s⦄) :  L.BoundedFormula α ξ :=
  φ.boundedFormula t

def boundedFormula₂ {ξ : Signature Sorts} {s t : Sorts}
    (φ : L.Formula ((⦃s⦄ ⨯ ⦃t⦄).IdxFam))
    (t₁ : L.Term (α ⊕ₛ ξ.IdxFam) (of s)) (t₂ : L.Term (α ⊕ₛ ξ.IdxFam) (of t)) :
    L.BoundedFormula α ξ := φ.boundedFormula (t₁.prod t₂)

def formula (φ : L.Formula σ.IdxFam) (ts : L.Term α σ) : L.Formula α :=
  φ.boundedFormula (ts.mapVars Fam.inl)

def formula₁ {s : Sorts} (φ : L.Formula (of s).IdxFam) (t : L.Term α (of s)) : L.Formula α :=
  φ.formula t

def formula₂ {s t : Sorts} (φ : L.Formula (⦃s⦄ ⨯ ⦃t⦄).IdxFam)
    (t₁ : L.Term α (of s)) (t₂ : L.Term α (of t)) : L.Formula α :=
  φ.formula (t₁.prod t₂)


end Formula

variable {T : L.Theory}

/-! ## Cardinality -/

section Cardinality

/-! ### Helper Definitions -/

def mkVar'' {σ : Signature Sorts} (i : Fin σ.length) :
    (Σ s : Sorts, L.Term (α ⊕ₛ σ.IdxFam) (of s)) := by
  let sv := σ.getIdxFam i
  exact ⟨sv.fst, .var sv.fst (Sum.inr sv.snd)⟩

open Signature
variable (L)

/-- Helper: `fromListAux acc (replicate n s)` preserves `OneSort s` when `acc` is already
`OneSort s`. -/
private lemma oneSort_fromListAux_replicate {S} (s : S) :
    ∀ (acc : Signature S), OneSort s acc → ∀ n : ℕ,
      OneSort s (Signature.fromListAux acc (List.replicate n s)) := by
  intro acc hacc n
  induction n generalizing acc with
  | zero =>
      simpa only [List.replicate_zero, fromListAux] using hacc
  | succ n ih =>
      -- replicate (n+1) s = s :: replicate n s
      simp only [List.replicate_succ, fromListAux]
      -- unfold the accumulator update in fromListAux
      cases acc with
      | nil =>
          -- acc' := of s
          simpa only using (ih (acc := of s) (hacc := OneSort.of))
      | of t =>
          -- This case can only happen if `t` is definitionally `s`
          -- (since `hacc : OneSort s (.of t)`).
          cases hacc
          -- now acc = of s
          have hacc' : OneSort s ((of s) ⨯ ⦃s⦄) :=
            OneSort.prod OneSort.of OneSort.of
          simpa only using (ih (acc := (of s) ⨯ ⦃s⦄) (hacc := hacc'))
      | prod σ τ =>
          have hacc' : OneSort s ((σ ⨯ τ) ⨯ ⦃s⦄) :=
            OneSort.prod hacc OneSort.of
          simpa only using (ih (acc := (σ ⨯ τ) ⨯ ⦃s⦄) (hacc := hacc'))

/-- Helper: `fromList (replicate n s)` is `OneSort s`. -/
private lemma oneSort_fromList_replicate {S} (s : S) (n : ℕ) :
    OneSort s (Signature.fromList (List.replicate n s)) := by
  simpa only [fromList] using
  (oneSort_fromListAux_replicate (s := s) (acc := (Signature.nil : Signature S)) OneSort.nil n)
/-- `repeat n s` is the `Signature` consisting of `n` copies of `.of s`, multiplied on the right. -/
def _root_.MSFirstOrder.Signature.repeat (n : ℕ) (s : Sorts) : Signature Sorts :=
  match n with
  | .zero => .nil
  | .succ n => (Signature.repeat n s) ⨯ ⦃s⦄

@[simp]
lemma _root_.MSFirstOrder.Signature.repeat_length (n : ℕ) (s : Sorts) :
  (Signature.repeat n s).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Signature.repeat, length_prod, ih, length_of]

@[simp] lemma _root_.MSFirstOrder.Signature.repeat_zero (s : Sorts) :
    Signature.repeat (Sorts := Sorts) 0 s = .nil := by
  simp only [Signature.repeat]

/-- Successor rule for `repeat`: appending one more copy of `s` corresponds to multiplying by
`.of s` on the right. -/
@[simp] lemma _root_.MSFirstOrder.Signature.repeat_succ (n : ℕ) (s : Sorts) :
    Signature.repeat (Sorts := Sorts) (n + 1) s =
      ((Signature.repeat (Sorts := Sorts) n s) ⨯ ⦃s⦄) := by
  simp only [Signature.repeat]

/-- `repeat n s` is a one-sorted `Signature` (all entries are `s`). -/
theorem _root_.MSFirstOrder.Signature.oneSort_repeat (s : Sorts) (n : ℕ) :
    OneSort s (Signature.repeat (Sorts := Sorts) n s) := by
  induction n with
  | zero =>
    simp_all only [Signature.repeat_zero]
    apply OneSort.nil
  | succ n ih =>
      rw [Signature.repeat]
      apply OneSort.prod ih
      apply OneSort.of


/-! ### Cardinality Sentences and Theories -/

/-
### Distinctness over repeated blocks
-/

open Term Signature

/-- In context `σ ⨯ ⦃s⦄`, asserts that the rightmost variable of sort `s`
    is distinct from every variable in the left `σ` block (assumed to be one-sorted). -/
protected def BoundedFormula.distinct_from
    (s : Sorts) : (σ : Signature Sorts) → (hσ : OneSort s σ) →
    L.BoundedFormula α (σ ⨯ ⦃s⦄)
    |  .nil,  h =>  ⊤
    |  .of t,  h => by
        let vr : (⦃t⦄ ⨯ ⦃s⦄).IdxFam s := Idx.var.right
        let vl :  (⦃t⦄ ⨯ ⦃s⦄).IdxFam t := Idx.var.left
        let h_os := OneSort.sort_is_s (OneSort.prod h (OneSort.of)) (t:= t) vl
        rw[h_os]; rw[h_os] at vl; rw[h_os] at vr
        exact (var s (Sum.inr vl) =' var s (Sum.inr  vr)).not
    |  (.prod σ τ), h =>
      let hσ := OneSort.prodl h
      let hτ := OneSort.prodr h
      -- embed (σ ⨯ ⦃s⦄) into ((σ ⨯ τ) ⨯ ⦃s⦄)
      let gσ :
          SigMap (σ ⨯ ⦃s⦄) ((σ ⨯ τ) ⨯ ⦃s⦄) :=
        (SigMap.incl_left (σ := σ) (τ := τ)).extend_right (η := ⦃s⦄)
      -- embed (τ ⨯ ⦃s⦄) into ((σ ⨯ τ) ⨯ ⦃s⦄)
      let gτ :
          SigMap (τ ⨯ ⦃s⦄) ((σ ⨯ τ) ⨯ ⦃s⦄) :=
        (SigMap.incl_right (σ := τ) (τ := σ)).extend_right (η := ⦃s⦄)
      ((BoundedFormula.distinct_from s σ hσ).reindex gσ) ⊓
      ((BoundedFormula.distinct_from s τ hτ).reindex gτ)

/-- `distinct s n` asserts that the `n` bound variables of sort `s` in `Signature.repeat n s`
    are pairwise distinct. Defined inductively on `n`.

    The successor case is: old distinctness (reindexed into the left block) and
    the new last variable is distinct from all earlier ones. -/
protected def BoundedFormula.distinct (s : Sorts) :
    ∀ n : ℕ, L.BoundedFormula α (Signature.repeat n s)
  | 0 => ⊤
  | n + 1 =>
    ((BoundedFormula.distinct s n).reindex (SigMap.incl_left)) ⊓
    (BoundedFormula.distinct_from L s (Signature.repeat n s) (Signature.oneSort_repeat s n))

/-- A sentence indicating that a structure has at least `n` distinct elements of sort `s`. -/
protected def Sentence.cardGe (s : Sorts) (n : ℕ) : L.Sentence :=
  (BoundedFormula.distinct L s n).exs

/-- A theory indicating that a structure is infinite at a sort. -/
def infiniteTheory (s : Sorts) : L.Theory :=
  Set.range (Sentence.cardGe L s)

/-- A theory that indicates a structure is nonempty. -/
def nonemptyTheory (s : Sorts) : L.Theory :=
  {Sentence.cardGe L s 1}

/-- A theory indicating that each of a set of constants (all of one fixed sort) is distinct. -/
def distinctConstantsAtSortTheory (t : Sorts) (s : Set (α t)) : L[[α]].Theory :=
  (fun ab : α t × α t =>
      (Term.equal
        (Constants.term (Sum.inr ab.1) : L[[α]].Term Fam.EmptyFam (.of t))
        (Constants.term (Sum.inr ab.2))).not) ''
    (s ×ˢ s ∩ (Set.diagonal (α t))ᶜ)

/-- A theory indicating that each of a `DepSet` of constants is distinct. -/
def distinctConstantsTheory (S : DepSet α) : L[[α]].Theory :=
  ⋃ t  : Sorts, L.distinctConstantsAtSortTheory t (S t)

/-! ### Properties of distinctConstantsAtSortTheory -/

variable {L}

open Set

theorem distinctConstantsAtSortTheory_mono {t : Sorts} {s₁ s₂ : Set (α t)} (h : s₁ ⊆ s₂) :
    L.distinctConstantsAtSortTheory t s₁ ⊆ L.distinctConstantsAtSortTheory t s₂ := by
  unfold distinctConstantsAtSortTheory; gcongr

theorem monotone_distinctConstantsAtSortTheory (t : Sorts) :
    Monotone (L.distinctConstantsAtSortTheory (t := t) : Set (α t) → L[[α]].Theory) :=
  fun _s _t st => L.distinctConstantsAtSortTheory_mono (t := t) st

theorem directed_distinctConstantsAtSortTheory (t : Sorts) :
    Directed (· ⊆ ·) (L.distinctConstantsAtSortTheory (t := t) : Set (α t) → L[[α]].Theory) :=
  Monotone.directed_le (monotone_distinctConstantsAtSortTheory (L := L) (α := α) t)

theorem distinctConstantsAtSortTheory_eq_iUnion {t : Sorts} (s : Set (α t)) :
    L.distinctConstantsAtSortTheory t s =
      ⋃ u : Finset s,
        L.distinctConstantsAtSortTheory t (u.map (Function.Embedding.subtype fun x => x ∈ s)) := by
  classical
  simp only [distinctConstantsAtSortTheory]
  rw [← image_iUnion, ← iUnion_inter]
  refine congr(_ '' ($(?_) ∩ _))
  ext ⟨i, j⟩
  simp only [prodMk_mem_set_prod_eq, Finset.coe_map, Function.Embedding.coe_subtype, mem_iUnion,
    mem_image, Finset.mem_coe, Subtype.exists, exists_and_right, exists_eq_right]
  refine ⟨fun h => ⟨{⟨i, h.1⟩, ⟨j, h.2⟩}, ⟨h.1, ?_⟩, ⟨h.2, ?_⟩⟩, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_or]
  · simp only [Finset.mem_insert, Subtype.mk.injEq, Finset.mem_singleton, or_true]
  · rintro ⟨u, ⟨is, _⟩, ⟨js, _⟩⟩
    exact ⟨is, js⟩

/-! ### Properties of distinctConstantsTheory -/

theorem distinctConstantsTheory_mono {S₁ S₂ : DepSet α} (h : S₁ ⊆ S₂) :
    L.distinctConstantsTheory S₁ ⊆ L.distinctConstantsTheory S₂ := by
  intro φ hφ
  rcases Set.mem_iUnion.mp hφ with ⟨t, ht⟩
  refine Set.mem_iUnion.mpr ⟨t, ?_⟩
  exact L.distinctConstantsAtSortTheory_mono (t := t) ((DepSet.le_def.mp h) t) ht

theorem monotone_distinctConstantsTheory :
    Monotone (L.distinctConstantsTheory : DepSet α → L[[α]].Theory) :=
  fun _S _T hST => L.distinctConstantsTheory_mono hST

theorem directed_distinctConstantsTheory :
    Directed (· ⊆ ·) (L.distinctConstantsTheory : DepSet α → L[[α]].Theory) :=
  Monotone.directed_le (monotone_distinctConstantsTheory (L := L) (α := α))

theorem distinctConstantsTheory_eq_iUnion (S : DepSet α) :
    L.distinctConstantsTheory S =
      ⋃ u : Finset S,
        L.distinctConstantsTheory
          (DepSet.ofSigma (α := α)
            (((u.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) :
              Set (Sigma α))) := by
  classical
  apply Set.Subset.antisymm
  · intro φ hφ
    rcases Set.mem_iUnion.mp hφ with ⟨t, ht⟩
    rw [L.distinctConstantsAtSortTheory_eq_iUnion (t := t) (s := S t)] at ht
    rcases Set.mem_iUnion.mp ht with ⟨u, hu⟩
    let v : Finset S :=
      u.image (fun x => ⟨⟨t, x.1⟩, by simp only [DepSet.mem_sigma, Subtype.coe_prop]⟩)
    refine Set.mem_iUnion.mpr ⟨v, ?_⟩
    refine Set.mem_iUnion.mpr ⟨t, ?_⟩
    let T : DepSet α :=
      DepSet.ofSigma (α := α)
        ((((v.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) : Set (Sigma α)))
    have hTt :
        T t = ((u.map (Function.Embedding.subtype fun x => x ∈ S t)) : Set (α t)) := by
      ext x
      change
        ((⟨t, x⟩ : Sigma α) ∈
            (((v.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) :
              Set (Sigma α))) ↔
          x ∈ ((u.map (Function.Embedding.subtype fun x => x ∈ S t)) : Set (α t))
      simp [v, DepSet.mem_sigma]
    rw [hTt]
    exact hu
  · intro φ hφ
    rcases Set.mem_iUnion.mp hφ with ⟨u, hu⟩
    let T : DepSet α :=
      DepSet.ofSigma (α := α)
        ((((u.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) : Set (Sigma α)))
    have hTS : T ⊆ S := by
      intro x hx
      change x ∈
          ((((u.map (Function.Embedding.subtype fun x => x ∈ S)) : Finset (Sigma α)) :
            Set (Sigma α))) at hx
      simp only [Finset.mem_coe, Finset.mem_map, Function.Embedding.coe_subtype] at hx
      rcases hx with ⟨y, hyu, hEq⟩
      simpa [hEq] using y.2
    exact L.distinctConstantsTheory_mono hTS hu

end Cardinality



/-! ## Experimental Definitions
-/

section Experimental

abbrev FinGet {S} (σ : Signature S) : (i : Fin σ.length) → Sigma σ.IdxFam :=
  match σ with
  | .nil => elim0
  | .of s => fun _ => ⟨s, .var⟩
  | .prod σ₁ σ₂ => Fin.append
    (fun i => ⟨(FinGet σ₁ i).1, .left (FinGet σ₁ i).2⟩)
    (fun j => ⟨(FinGet σ₂ j).1, .right (FinGet σ₂ j).2⟩)

end Experimental


end Language

end MSFirstOrder
