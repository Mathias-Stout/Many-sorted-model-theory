import ProdExpr.Signature
import ProdExpr.Fam


/-!
# Working with "sorted tuples"

This file defines some common operations on and proves some basic theorems about
`σ.Interpret α`, where `σ` is of type `ProdExpr S` and `α` is a dependent type over S
-/

universe u v w z

variable {S : Type u}
namespace MSFirstOrder

namespace SortedTuple

open ProdExpr

variable {α : S → Type v} {β : S → Type w}

instance nilUnique : Unique (Interpret β ProdExpr.nil) :=
  inferInstanceAs (Unique PUnit)

@[simp]
lemma reduce_nil (a : Interpret α ProdExpr.nil) : a = default := rfl

abbrev mk_default (α : S → Type v) : Interpret α ProdExpr.nil := default

instance indVarNilEmpty {s : S} : IsEmpty (indVar nil s) := by
  constructor
  intro a
  cases a

instance indVarofInhabited {s : S} : Inhabited (indVar (of s) s) := by
  constructor
  case default =>
    exact indVar.var

instance indVarofUnique {s : S} : Unique (indVar (of s) s) := by
  constructor
  · intro a
    cases a
    case var => rfl

/-- Takes an `indVar σ` as an index for a Sorted Tuple xs and returns
    the value at that position. -/
def get {σ : ProdExpr S} (xs : σ.Interpret α) : (indVar σ) →ₛ α  :=
  match σ with
  | .nil => fun s => fun v => isEmptyElim v
  | .of t => fun s => fun v => by
    cases v
    exact xs
  | .prod σ τ => fun s => fun v =>
    match v with
    | indVar.left w => get xs.1 s w
    | indVar.right w => get xs.2 s w

open indVar

theorem get_of (s : S) (xs : (of s).Interpret α) : get xs _ var = xs := rfl

def fromGet {σ : ProdExpr S} (v : (indVar σ) →ₛ α) : σ.Interpret α :=
  match σ with
  | .nil =>  default
  | .of t => v t var
  | .prod _ _  =>  ⟨fromGet (fun s => fun w => v s (left w)),
                  fromGet (fun s => fun w => v s (right w))⟩

/-- Restrict a dependent indVar map to only vars from the left factor -/
def leftMap {σ τ : ProdExpr S} (v : (indVar (σ.prod τ)) →ₛ α) : (indVar σ) →ₛ α :=
   (fun s => fun w => v s (left w))

/-- Restrict a dependent indVar map to only vars from the right factor -/
def rightMap {σ τ : ProdExpr S} (v : (indVar (σ.prod τ)) →ₛ α) : (indVar τ) →ₛ α :=
   (fun s => fun w => v s (right w))

@[simp]
theorem get_fromGet {σ : ProdExpr S} (xs : σ.Interpret α) : fromGet (get xs) = xs := by
  induction σ
  case nil => simp
  case of t => rfl
  case prod σ τ => simp_all only [fromGet, get, Prod.mk.eta]

@[simp]
theorem fromGet_get {σ : ProdExpr S} (v : (indVar σ) →ₛ α) : get (fromGet v) = v :=by
  ext s x
  induction σ
  case nil => exact isEmptyElim x
  case of t =>
    have h : α t = (of t).Interpret α := by rfl
    change get (h ▸ (v t var)) s x = v s x
    cases x
    case var =>
    simp_all only
    rfl
  case prod σ τ =>
    rw[fromGet, get]
    simp_all only
    split
    next v_1 w => simp_all only
    next v_1 w => simp_all only

/-- Forget the tree shape and just view it as a list of elements with their sorts. -/
def toList {σ : ProdExpr S} (t : σ.Interpret α) : List (Sigma α) :=
  match σ with
  | ProdExpr.nil  => []
  | of s          => [⟨s, t⟩]
  | prod _ _      => toList t.fst ++ toList t.snd

/--
Turn a Sorted Tuple into a Finset of ⟨s, a : α s⟩ pairs
-/
def toFinset {σ : ProdExpr S} (t : σ.Interpret α)
    [DecidableEq S] [∀ t, DecidableEq (α t)] : Finset (Sigma α) :=
  match σ with
  | nil            => ∅
  | of s         => {⟨s, t⟩}
  | prod _ _      => toFinset t.fst ∪ toFinset t.snd

@[simp] lemma toList_nil :
   toList (mk_default α) = [] := rfl

@[simp] lemma toList_of (s : S) (a : α s) :
    toList (σ := of s) a = [⟨s, a⟩] := rfl

@[simp] lemma toList_prod {σ τ : ProdExpr S} (xs : σ.Interpret α) (ys : τ.Interpret α) :
    toList (σ := σ.prod τ) ⟨xs,  ys⟩ = toList xs ++ toList ys := rfl

@[simp] lemma toList_prod' {σ τ : ProdExpr S} (xs : (σ.prod τ).Interpret α) :
    toList (σ := σ.prod τ) xs = toList xs.1 ++ toList xs.2 := rfl

lemma toList_length {σ : ProdExpr S} {xs ys : σ.Interpret α} :
  (toList xs).length = (toList ys).length := by
  induction σ
  case of => simp
  case nil => simp
  case prod σ τ ih₁ ih₂ => simp[ih₁ (xs := xs.1) (ys := ys.1), ih₂ (xs := xs.2) (ys := ys.2)]

variable {α : S → Type v} {β : S → Type w} {γ : S → Type z}
variable {σ ξ η : ProdExpr S} {s : S} {x : α s}
variable {l : List (Sigma α)} {xs : σ.Interpret α}

open List

@[simp]
theorem length_eq (xs : σ.Interpret α) : (toList xs).length = σ.length := by
  induction σ
  case nil => rfl
  case of =>
    simp[ProdExpr.length]
  case prod =>
    simp_all[ProdExpr.length]

theorem length_eq_List (xs : σ.Interpret α) : (toList xs).length = σ.toList.length := by
  induction σ
  case nil =>
    simp[ProdExpr.toList]
  case of =>
    simp[ProdExpr.toList]
  case prod _ _ ih₁ ih₂ =>
    simp_all[ProdExpr.toList, ih₁ (xs := xs.1), ih₂ (xs := xs.2)]

section maps

/-- Map a dependent function over a SortedTuple, similar to List.map. -/
def map (f : α →ₛ β) {σ : ProdExpr S} (xs : σ.Interpret α) : σ.Interpret β :=
  match f , σ , xs with
  | _ , .nil  , _      =>  default
  | f , .of s , xs      =>  f s xs
  | f , .prod _ _ , xs => ⟨map f xs.1 , map f xs.2⟩

/--A sorted tuple is comparable to a "dependent functor",
  so we borrow this notation for "Functor.map". -/
infixr:100 " <$>ₛ " => SortedTuple.map

@[simp]
theorem map_id (xs : σ.Interpret α) : (fun _ => id) <$>ₛ xs = xs := by
  induction σ
  case nil => simp[map]
  case of => simp [map, id_eq]
  case prod τ η ih₁ ih₂ => simp only [map, ih₁, ih₂, Prod.mk.eta]

@[simp]
theorem map_id' (xs : σ.Interpret α) : (fun _ t => t) <$>ₛ xs = xs := by
  have : (fun _ t => t : α →ₛ α) = fun _ => id := rfl
  simp [this]

theorem comp_map (φ : α →ₛ β) (ψ : β →ₛ γ)
    (xs : σ.Interpret α) : ((ψ ∘ₛ φ) <$>ₛ  xs) = ψ <$>ₛ (φ <$>ₛ  xs) := by
  induction σ
  case nil => simp only [map]
  case of => simp [map]
  case prod τ η ih₁ ih₂ => simp only [map, ih₁, ih₂]

theorem get_map (xs : σ.Interpret α) (f : α →ₛ β) : SortedTuple.get (f <$>ₛ xs) =
    fun s => f s ∘ (get xs s) := by
  induction σ with
  | nil => funext s x; exact isEmptyElim x
  | of s =>
    funext s₁ a
    cases a
    rw [Function.comp_apply, get_of]
    rfl
  | prod σ₁ σ₂ ih₁ ih₂ =>
    funext s a
    obtain ⟨x₁, x₂⟩ := xs
    rw [map]
    cases a with
    | left v => simp only [ih₁, Function.comp_apply, get]
    | right w => simp only [ih₂, Function.comp_apply, get]

theorem map_prod {σ₁ σ₂ : ProdExpr S} {f : α →ₛ β} (x₁ : σ₁.Interpret α) (x₂ : σ₂.Interpret α) :
    (f <$>ₛ (x₁, x₂) : (σ₁.prod σ₂).Interpret β) =
    ((f <$>ₛ x₁, f <$>ₛ x₂) : (σ₁.prod σ₂).Interpret β) := rfl

end maps

section instances

@[simp]
theorem default_toList {S : Type u} {α : S → Type*} :
  toList (default : nil.Interpret α ) = [] := rfl

@[simp]
theorem map_default {S : Type u} {α β : S → Type*} {f : α →ₛ β} :
  f <$>ₛ (default : nil.Interpret α) = default := rfl


def decidableEq
    [∀ s, DecidableEq (α s)] :
    ∀ {σ : ProdExpr S}, DecidableEq (σ.Interpret α)
| .nil =>
    by intro a b; cases a; cases b; exact isTrue rfl
| .of s =>
    by
    aesop
| .prod σ τ =>
    by
    simp only [Interpret]
    intro a b
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1 , b2⟩
    have h1 : Decidable (a1 = b1) :=
      SortedTuple.decidableEq (σ := σ) a1 b1
    have h2 : Decidable (a2 = b2) :=
      SortedTuple.decidableEq (σ := τ) a2 b2
    have h3:= (inferInstance : Decidable (a1 = b1 ∧ a2 = b2))
    aesop

instance instDecidableEq
    [∀ s, DecidableEq (α s)] :
    DecidableEq (σ.Interpret α) :=
  SortedTuple.decidableEq (σ := σ)

open ProdExpr

/-- “Flat” argument tuples: one entry per position in the arity `σ`. -/
def SortedMap (α : S → Type v) (σ : ProdExpr S) :=
  (i : Fin σ.length) → α (σ.get i)

/-- Coercion instance from SortedTuple to a dependent object over Sorts -/
instance instCoeFam : Coe (σ.Interpret α) (σ.indVar →ₛ α) where
  coe := get

end instances
end SortedTuple

section interpret_equivalences
/-This section elaborates on how SortedTuple.get interacts with maps of indVars, which
will be needed in semantics.-/

open SortedTuple
namespace ProdExpr

/-- The map of interpretations induced by a VarMap on signatures. -/
def Interpret.reindex
    {X : S → Type v} {σ τ : ProdExpr S} (f : VarMap σ τ) :
    Interpret X τ → Interpret X σ :=
  fun xs =>
    SortedTuple.fromGet
      (fun s w => SortedTuple.get xs s (f s w))

@[simp]
lemma get_reindex
     {X : S → Type _} {σ τ : ProdExpr S}
    (xs : Interpret X τ) (f : VarMap σ τ) :
  SortedTuple.get (xs.reindex f) = fun s w => SortedTuple.get xs s (f s w) := by
  ext s w
  simp [Interpret.reindex]

/-- The equivalence on interpretations induced by a `VarEquiv` on signatures. -/
def Interpret.reindexEquiv
    {X : S → Type v} {σ τ : ProdExpr S} (e : VarEquiv σ τ) :
    Interpret X σ ≃ Interpret X τ :=
{ toFun    := fun xs => xs.reindex e.invFun
  , invFun := fun ys => ys.reindex e.toFun
  , left_inv := by
      intro xs
      simp [Interpret.reindex]
  , right_inv := by
      intro ys
      simp [Interpret.reindex] }

end ProdExpr
end interpret_equivalences

end MSFirstOrder
