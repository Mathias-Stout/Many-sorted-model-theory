import MultisortedLogic.Signature
import MultisortedLogic.DepSet

/-!
# The supporting datatype of "sorted tuples"

This file defines the Interpret datatype, equivalences to different representations and
a mapping over them. A Interpret is meant to represent a dependent vector: the type of
the entries is controlled by a list `σ` over some type `S` and an assignment `α → Type*`.
Equivalently, it is an object of type `List (Sigma α)`, with given first projection.
This abstract datatype helps convert between these different avatars while the project evolves.
The representation of Interprets in the final iteration might differ drastically, or an entirely
different datatype or formalism might be preferred after further testing.


## Main Definitions

- Given a type `S`, a map `α : Fam S` and a list `σ : Signature S`,
  a `α[^]σ` is a `List (Sigma α)` with first projection equal to `σ`
- `Sortedtuple.ofList'` converts a `List (Sigma α)` to a Interpret, notation `!ₛ[ ... ]`
- `Interpret.toMap` converts a `α[^]σ ` to a dependent map
  `(i : Fin σ.length) → α (σ.get i)`
- `Interpret.toFMap` converts a `α[^]σ ` to a map fibered over `S`: an object of type
  `(s : S) → { (i : Fin σ.length) // σ.get i = s } →  α s`
- `Interpret.append` appends two Interprets, similar to appending lists
- `Interpret.map` maps a dependent function over a Interpret,
  similar to List.map. Notation `<$>ₛ`


## Main theorems

- Equivalence between sorted tuples and dependent maps
  in `Interpret.toMap_fromMap` and `Interpret.fromMap_toMap`
- Equivalence between sorted tuples and maps fibered over a base `S`
  in `Interpret.toFMap_fromFMap` and `Interpret.fromFmap_toFmap`
- various helper theorems on appending,
  casting over equality of the parametrizing list `σ`, and mapping over Interprets
-/

universe u v w z

variable {S : Type u}
namespace MSFirstOrder
open Fam
namespace Signature
namespace Interpret

open Signature

variable {α β : Fam S} {s : S}

/-! ## Basic Instances and Properties -/

instance nilUnique : Unique (Interpret β ⦃⦄) :=
  inferInstanceAs (Unique PUnit)

instance emptyNil : IsEmpty ((⦃⦄.Idx) s) :=
  by
  constructor
  intro a ; cases a

lemma reduce_nil (a : Interpret α ⦃⦄) : a = default := rfl

abbrev mk_default (α : Fam.{v} S) : Interpret α ⦃⦄ := default

instance IdxNilEmpty : IsEmpty (Idx ⦃⦄ s) := by
  constructor
  intro a
  cases a

instance IdxNilEmpty' : IsEmpty (⦃⦄.IdxFam s) := by
  constructor
  intro a
  cases a

instance IdxofInhabited : Inhabited (Idx ⦃s⦄ s) :=
  ⟨Idx.var⟩

instance IdxofUnique : Unique (Idx ⦃s⦄ s) := by
  constructor
  · intro a
    cases a
    case var => rfl

/-! ## Core Operations -/

/-! ### Element Access -/

/-- Takes an `IdxFam σ` as an index for a Sorted Tuple xs and returns
    the value at that position.
-/
def get {σ : Signature S} (xs : α [^] σ) : (σ.IdxFam) →ₛ α  :=
  match σ with
  | .nil => ⟨fun s => fun v => isEmptyElim v⟩
  | .of t => ⟨fun s => fun v => by
    cases v
    exact xs⟩
  | .prod σ τ => ⟨fun s => fun v =>
    match v with
    | Idx.left w => get xs.1 s w
    | Idx.right w => get xs.2 s w⟩

/-
lemma ext {σ : Signature S} (xs ys : α[^]σ) (h: ∀ (s: S) (v: σ.Idx s), xs.get s v = ys.get s v) :
    xs = ys := by
  induction σ
  simp_all only [implies_true]
  case of s =>
    simpa using h s Idx.var
  case prod σ τ ihσ ihτ =>
    rcases xs with ⟨x, x'⟩
    rcases ys with ⟨y, y'⟩
    simp
    exact
      ⟨by apply ihσ x y
          intro s v ; simpa using h s v.left,
       by apply ihτ x' y'
          intro s v ; simpa using h s v.right,
      ⟩


-/
open Idx

@[simp]
theorem get_of (s : S) (xs : ⦃s⦄.Interpret α) : xs.get _ var = xs := rfl

@[simp]
theorem get_left {s : S} {σ τ : Signature S} {v : σ.Idx s} (xs : (σ.prod τ).Interpret α)
  : get xs _ (left v) = get xs.1 _ v  := rfl

@[simp]
theorem get_right {s : S} {σ τ : Signature S} {v : σ.Idx s} (xs : (τ.prod σ).Interpret α)
  : get xs _ (right v) = get xs.2 _ v  := rfl

def fromGet {σ : Signature S} (v : IdxFam σ →ₛ α) : α[^]σ :=
  match σ with
  | .nil =>  (default : PUnit)
  | .of t => v t var
  | .prod _ _  =>  ⟨fromGet (⟨fun s => fun w => v s (left w)⟩),
                  fromGet (⟨fun s => fun w => v s (right w)⟩)⟩

@[simp]
theorem get_fromGet {σ : Signature S} (xs : α [^] σ) : fromGet (get xs) = xs := by
  induction σ
  case nil => simp only
  case of t => rfl
  case prod σ τ =>
    obtain ⟨fst, snd⟩ := xs
    ext : 1
    · simp_all only
      apply σ
    · simp_all only
      apply τ

@[simp]
theorem fromGet_get {σ : Signature S} (v : (IdxFam σ) →ₛ α) : get (fromGet v) = v :=by
  ext s x
  induction σ
  case nil => exact isEmptyElim x
  case of t =>
    have h : α t = α[^]⦃t⦄ := by rfl
    change get (h ▸ (v t var)) s x = v s x
    cases x
    case var =>
    simp_all only
    rfl
  case prod σ τ =>
    rw[fromGet, get]
    simp_all only [Fam.FamMap.mk_apply]
    split
    next v_1 w => simp_all only
    next v_1 w => simp_all only


/-- Decomposition lemma for `fromGet` on product signatures.
    Useful for simplifying contexts in ultraproduct proofs.
    Not marked @[simp] to avoid interfering with `comap` proofs. -/
theorem fromGet_prod {σ τ : Signature S} (v : IdxFam (σ ⨯ τ) →ₛ α) :
    fromGet v = ⟨fromGet ⟨fun s w => v s (Idx.left w)⟩,
                 fromGet ⟨fun s w => v s (Idx.right w)⟩⟩ := rfl

/-! ## Conversion Functions -/

/-! ### List Conversion -/

/-- Forget the tree shape and just view it as a list of elements with their sorts. -/
def toList {σ : Signature S} (t : α [^] σ) : List (Sigma α) :=
  match σ with
  | ⦃⦄  => []
  | of s          => [⟨s, t⟩]
  | prod _ _      => toList t.fst ++ toList t.snd

/-! ### Finset Conversion -/

/--
Turn a Sorted Tuple into a Finset of ⟨s, a : α s⟩ pairs
-/
def toFinset {σ : Signature S} (t : α [^] σ)
    [DecidableEq S] [∀ t, DecidableEq (α t)] : Finset (Sigma α) :=
  match σ with
  | nil            => ∅
  | of s         => {⟨s, t⟩}
  | prod _ _      => toFinset t.fst ∪ toFinset t.snd

@[simp] lemma toList_nil :
   toList (mk_default α) = [] := rfl

@[simp] lemma toList_of (s : S) (a : α s) :
    toList (σ := ⦃s⦄) a = [⟨s, a⟩] := rfl

@[simp] lemma toList_prod {σ τ : Signature S} (xs : α [^] σ) (ys : τ.Interpret α) :
    toList (σ := σ.prod τ) ⟨xs,  ys⟩ = toList xs ++ toList ys := rfl

@[simp] lemma toList_prod' {σ τ : Signature S} (xs : (σ.prod τ).Interpret α) :
    toList (σ := σ.prod τ) xs = toList xs.1 ++ toList xs.2 := rfl

/-! ### Length Properties -/

lemma toList_length {σ : Signature S} {xs ys : α [^] σ} :
  (toList xs).length = (toList ys).length := by
  induction σ
  case of => simp only [toList_of, List.length_cons, List.length_nil, zero_add]
  case nil => simp only
  case prod σ τ ih₁ ih₂ => simp only [toList_prod', List.length_append,
    ih₁ (xs := xs.1) (ys := ys.1), ih₂ (xs := xs.2) (ys := ys.2)]

variable {α : Fam.{v} S} {β : Fam S} {γ : Fam S}
variable {σ ξ η : Signature S} {s : S} {x : α s}
variable {l : List (Sigma α)} {xs : α [^] σ}

open List

@[simp]
theorem length_eq (xs : α [^] σ) : (toList xs).length = σ.length := by
  induction σ
  case nil => rfl
  case of =>
    simp only [toList_of, length_cons, List.length_nil, zero_add, length]
  case prod =>
    simp_all only [toList_prod', length_append, length]

theorem length_eq_List (xs : α [^] σ) : (toList xs).length = σ.toList.length := by
  induction σ
  case nil =>
    simp only [length_eq, length_nil, Signature.toList, List.length_nil]
  case of =>
    simp only [toList_of, length_cons, List.length_nil, zero_add, Signature.toList]
  case prod _ _ ih₁ ih₂ =>
    simp_all only [length_eq, toList_prod', length_append, ih₁ (xs := xs.1), ih₂ (xs := xs.2),
      Signature.toList]

/-! ## Mapping Operations -/

section maps

/-- Map a dependent function over a Interpret, similar to List.map. -/
def map (f : α →ₛ β) {σ : Signature S} (xs : α [^] σ) : β [^] σ:=
  match f , σ , xs with
  | _ , .nil  , _      =>  default
  | f , .of s , xs      =>  f s xs
  | f , .prod _ _ , xs => ⟨map f xs.1 , map f xs.2⟩

/-- Map using a FamMapClass instance - this version can better infer the target family. -/
def mapClass {F : Type*} {base : Type*} {M N : Fam base} [Fam.FamMapClass F M N]
    (φ : F) {σ : Signature base} (xs : M [^] σ) : N [^] σ :=
  map (Fam.FamMapClass.toFamMap φ) xs

/--A sorted tuple is comparable to a "dependent functor",
  so we borrow this notation for "Functor.map". -/
infixr:100 " <$>ₛ " => Interpret.mapClass

lemma mapClass_map_prod {F} [FamMapClass F α β] (f : F) (xs : α [^] σ) (ys : α [^] ξ) :
  Interpret.mapClass f (σ := σ ⨯ ξ) (xs, ys) = (f <$>ₛ xs, f <$>ₛ ys) := rfl

@[simp]
theorem mapClass_eq_map {F} [FamMapClass F α β] (f : F) (xs : α [^] σ) :
    f <$>ₛ xs = map (f : α →ₛ β) xs := rfl

@[simp]
theorem map_id (xs : α [^] σ) : FamMap.idₛ (α:= α) <$>ₛ xs = xs := by
  induction σ
  case nil => simp only [mapClass, map, PUnit.default_eq_unit]
  case of => rfl
  case prod τ η ih₁ ih₂ =>
      simp_all only [mapClass, map, Prod.mk.eta]

@[simp]
theorem map_id_map (xs : α [^] σ) : map (FamMap.idₛ (α := α)) xs = xs := by
  change FamMap.idₛ (α := α) <$>ₛ xs = xs
  exact map_id xs

@[simp]
theorem map_id' (xs : α [^] σ) : (⟨fun _ t => t⟩ : FamMap _ _ ) <$>ₛ xs = xs := by
  have : (⟨fun _ t => t⟩ : α →ₛ α) = ⟨fun _ => id⟩ := rfl
  change FamMap.idₛ (α:= α) <$>ₛ xs = xs
  simp only [map_id]

theorem comp_map (φ : α →ₛ β) (ψ : β →ₛ γ)
    (xs : α [^] σ) : ((ψ ∘ₛ φ) <$>ₛ  xs) = ψ <$>ₛ (φ <$>ₛ  xs) := by
  induction σ
  case nil => simp [mapClass, map]
  case of => rfl
  case prod τ η ih₁ ih₂ =>
    simp_all only [mapClass, map]

theorem comp_mapClass {F} [FamMapClass F α β] {G} [FamMapClass G β γ]
    (φ : F) (ψ : G) (xs : α [^] σ) :
    (((ψ : β →ₛ γ) ∘ₛ (φ : α →ₛ β)) <$>ₛ xs) = ψ <$>ₛ (φ <$>ₛ xs) := by
  rw [comp_map]
  rfl

@[simp]
theorem map_mapClass {F} [FamMapClass F α β] {G} [FamMapClass G β γ]
    (φ : F) (ψ : G) (xs : α [^] σ) :
    ψ <$>ₛ (φ <$>ₛ xs) = (((ψ : β →ₛ γ) ∘ₛ (φ : α →ₛ β)) <$>ₛ xs) := by
  simpa using (comp_mapClass (φ := φ) (ψ := ψ) (xs := xs)).symm

@[simp]
theorem map_map {F} [FamMapClass F α β] {G} [FamMapClass G β γ] (φ : F) (ψ : G) (xs : α [^] σ) :
    ψ <$>ₛ (φ <$>ₛ xs) = map ((ψ : β →ₛ γ) ∘ₛ (φ : α →ₛ β)) xs := by
  rw [map_mapClass]
  rfl

@[simp]
theorem get_map {F} [FamMapClass F α β] (xs : α [^] σ) (f : F) : Interpret.get (f <$>ₛ xs) =
    f ∘ₛ (get xs) := by
  induction σ with
  | nil => ext s x; exact isEmptyElim x
  | of s =>
    ext s₁ a; cases a
    simp_all only [get_of]; rfl
  | prod σ₁ σ₂ ih₁ ih₂ =>
    ext s a; obtain ⟨x₁, x₂⟩ := xs
    simp_all only [mapClass, map]
    cases a with
    | left v => simp_all only [get_left]; rfl
    | right w => simp_all only [get_right]; rfl

@[simp]
theorem get_map_apply {F} [FamMapClass F α β] (xs : α [^] σ) (f : F) (s : S) (v : σ.Idx s) :
    (f <$>ₛ xs).get s v = f s (xs.get s v) := by
  calc
    (f <$>ₛ xs).get s v = (Interpret.get (f <$>ₛ xs)) s v := rfl
    _ = (f ∘ₛ xs.get) s v := by
      exact congrArg (fun g => g s v) (get_map (σ := σ) (xs := xs) (f := f))
    _ = f s (xs.get s v) := rfl

@[simp]
theorem map_prod {F} [FamMapClass F α β] {σ₁ σ₂ : Signature S} (f : F) (x₁ : σ₁.Interpret α)
    (x₂ : α [^] σ₂) : (f <$>ₛ (x₁, x₂) : (σ₁.prod σ₂).Interpret β) =
    ((f <$>ₛ x₁, f <$>ₛ x₂) : (σ₁.prod σ₂).Interpret β) := by
  simp [mapClass, map]

end maps

/-! ## Type Class Instances -/

section instances

@[simp]
theorem default_toList {S : Type u} {α : Fam S} :
  toList (default : nil.Interpret α ) = [] := rfl

@[simp]
theorem map_default {S : Type u} {α : Fam S} {β : Fam S} {F} [FamMapClass F α β] (f : F) :
  f <$>ₛ (default : nil.Interpret α) = default := by
    simp [mapClass, map]

/-- Decidability instance for Interpret equality.
    Uses structural recursion on the Signature shape. -/
def decidableEq
    [∀ s, DecidableEq (α s)] :
    ∀ {σ : Signature S}, DecidableEq (α[^]σ)
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
      Interpret.decidableEq (σ := σ) a1 b1
    have h2 : Decidable (a2 = b2) :=
      Interpret.decidableEq (σ := τ) a2 b2
    have h3:= (inferInstance : Decidable (a1 = b1 ∧ a2 = b2))
    aesop

instance instDecidableEq
    [∀ s, DecidableEq (α s)] :
    DecidableEq (α[^]σ) :=
  Interpret.decidableEq (σ := σ)

instance {σ : Signature S} [∀ a, Nonempty (α a)] : Nonempty (α [^] σ) := by
  induction σ with
  | nil => infer_instance
  | of => infer_instance
  | prod => infer_instance

open Signature
open Fam

/-- "Flat" argument tuples: one entry per position in the arity `σ`. -/
def SortedMap (α : Fam.{v} S) (σ : Signature S) :=
  (i : Fin σ.length) → α (σ.getIdxFam i).1

/-- Coercion instance from Interpret to a dependent object over Sorts -/
instance instCoeFam : Coe (σ.Interpret α) (σ.IdxFam →ₛ α) where
  coe := get

@[ext]
lemma ext {xs ys : σ.Interpret α} (h : ∀ (s : S) (v : σ.Idx s),
        xs.get s v = ys.get s v) : xs = ys := by
  induction σ
  case nil => simp_all only [reduce_nil, PUnit.default_eq_unit, implies_true]
  case of s  =>
    have conc := h s (Idx.var)
    simp only [get] at conc
    exact conc
  case prod σ τ ihσ ihτ =>
    rcases xs with ⟨xsσ, xsτ⟩
    rcases ys with ⟨ysσ, ysτ⟩
    rw[Prod.mk.injEq]
    constructor
    case left =>
      apply ihσ
      intro s v
      have h' := h s (v.left)
      simp only [get] at h'
      exact h'
    case right =>
      apply ihτ
      intro s v
      have h' := h s (v.right)
      simp only [get] at h'
      exact h'

lemma ext_iff' {xs ys : σ.Interpret α} :
    xs = ys ↔ ∀ (s : S) (v : σ.Idx s), xs.get s v = ys.get s v := by
  constructor
  · exact fun h s v ↦ by rw [h]
  · exact ext
end instances

section quotients

open Fam
/--
If the underlying family `α` carries a many-sorted setoid, then each interpretation
`α[^]σ` inherits a setoid by transporting the pointwise setoid on maps
`σ.IdxFam →ₛ α` along `SortedTuple.get`.
-/
instance instSetoidInterpret [MSSetoid α] : {σ : Signature S} → Setoid (α[^]σ)
  | nil => {
    r := fun _ _ ↦ True
    iseqv := {
      refl := fun _ ↦ True.intro
      symm := id
      trans := fun _ ↦ id
    }
  }
  | of _ => inferInstance
  | prod σ τ => Setoid.prod (instSetoidInterpret (σ := σ)) (instSetoidInterpret (σ := τ))

@[simp]
lemma prod_equiv [MSSetoid α] {xs xs' : α [^] σ} {ys ys' : α [^] ξ} :
    instSetoidInterpret (σ := σ ⨯ ξ) (xs, ys) (xs', ys') ↔ (xs ≈ xs' ∧ ys ≈ ys') := by
  rfl

instance instMSSetoidInterpret [Fam.MSSetoid α] : MSSetoid (MapFam σ.IdxFam α) := inferInstance

variable [R : MSSetoid α]

lemma interpret_equiv_iff (xs ys : α [^] σ) :
    xs ≈ ys ↔ ∀ (s : S) (v : σ.Idx s), xs.get s v ≈ ys.get s v := by
  induction σ with
  | nil => simp
  | of s =>
    constructor
    · intro h s' v
      cases v
      exact h
    · intro h
      rw [←get_of s xs, ←get_of s ys]
      exact h _ _
  | prod σ τ hσ hτ =>
    constructor
    · intro h s v
      cases v
      · exact (hσ xs.1 ys.1).mp h.1 s _
      · exact (hτ xs.2 ys.2).mp h.2 s _
    · intro h
      refine ⟨?_, ?_⟩
      · exact (hσ xs.1 ys.1).mpr (fun s v ↦ h s (Idx.left v))
      · exact (hτ xs.2 ys.2).mpr (fun s v ↦ h s (Idx.right v))

@[simp]
lemma interpret_equiv_iff' (xs ys : σ.IdxFam →ₛ α) :
  xs ≈ ys ↔ fromGet xs ≈ fromGet ys := by
  simp_all only [interpret_equiv_iff, fromGet_get]
  rfl

local instance : Fam.MSSetoid α := R

/-- Map an interpretation into the componentwise-quotiented interpretation
  (componentwise `Quotient.mk`). -/
def toQuot {σ : Signature S} (xs : α [^] σ) : (MSQuotient R)[^]σ:=
  (Fam.MSQuotient.mk (M := α) R) <$>ₛ xs

@[simp]
lemma get_toQuot {σ : Signature S} (xs : α [^] σ) (s : S) (v : σ.Idx s) :
    (toQuot (σ := σ) (α := α) xs).get s v
      = Quotient.mk (s := (R.toSetoid s)) (xs.get s v) := by
  simp only [toQuot, get_map]
  rfl

lemma toQuot_eq {σ : Signature S} {x y : α [^] σ} : x.toQuot = y.toQuot ↔ x ≈ y := by
  induction σ with
  | nil => simp
  | of _ => exact Quotient.eq
  | prod σ₁ σ₂ h₁ h₂ =>
    cases x
    cases y
    unfold toQuot
    erw [map_prod, Prod.ext_iff, h₁, h₂]
    rfl

lemma toQuot_eq_iff_out {x : α [^] σ} {y : (α /ₛ R) [^] σ} :
    x.toQuot = y ↔ x ≈ MSQuotient.out <$>ₛ y := by
  induction σ with
  | nil =>
    simp only [mapClass_eq_map, Setoid.refl]
  | of s =>
    exact Quotient.mk_eq_iff_out
  | prod σ₁ σ₂ h₁ h₂ =>
    cases x
    cases y
    simp only [Prod.ext_iff]
    exact and_congr h₁ h₂

noncomputable example {σ τ : Signature S} {x : α [^] σ} {y : (α /ₛ R) [^] τ} :=
  ((x, MSQuotient.out <$>ₛ y) : α [^] (σ ⨯ τ))

lemma weird_needs_name {σ τ : Signature S} {x : α [^] σ} {y : (α /ₛ R) [^] τ} :
    (x.toQuot, y) = Interpret.mapClass (MSQuotient.mk R) (σ := σ ⨯ τ) (x, MSQuotient.out <$>ₛ y)
  := by
  rw [map_prod, ←comp_map, MSQuotient.out_eq, map_id]
  rfl

/--
Multisorted analogue of Mathlib's `Quotient.finChoice`:
turn a *tuple of quotients* into a *single quotient of representative tuples*.

Noncomputable: chooses representatives via `Quotient.out`.
-/
noncomputable def choice {σ : Signature S} (xs : (α /ₛ R) [^] σ) :
    Quotient (α := α[^]σ) instSetoidInterpret :=
  ⟦MSQuotient.out <$>ₛ xs⟧

/-- `choice` inverts `toQuot` up to quotient equivalence. -/
theorem choice_toQuot {σ : Signature S} (xs : α [^] σ) :
    choice (toQuot xs) = ⟦xs⟧ := by
  apply Quotient.sound
  simp_all only [interpret_equiv_iff]
  intro s v
  simp_all only [toQuot, get_map]
  exact Quotient.exact (Quotient.out_eq _)

/-- The representative from `choice` maps back to the original tuple of quotients. -/
@[simp]
theorem toQuot_out_choice {σ : Signature S} (xs : (α /ₛ R) [^] σ) :
    (choice xs).out.toQuot = xs := by
  induction σ with
  | nil => rfl
  | of _ =>
    simp [choice, Interpret.mapClass, map, FamMapClass.toFamMap, MSQuotient.out, toQuot,
      MSQuotient.mk]
    exact (Quotient.out_eq _).trans (Quotient.out_eq _)
  | prod σ τ hσ hτ =>
    cases xs
    rw [toQuot_eq_iff_out]
    exact Quotient.eq_mk_iff_out.mp rfl

end quotients

end Interpret

/-! ## Advanced Equivalences -/

section interpret_equivalences
/-!
This section elaborates on how Interpret.get interacts with maps of Idxs,
which will be needed in semantics.
-/

variable {α : Fam S}
open Interpret

/-- The map of interpretations induced by a SigMap on signatures. -/
def Interpret.comap
    {X : Fam.{v} S} {σ τ : Signature S} (f : SigMap σ τ) :
    Interpret X τ → Interpret X σ :=
  fun xs =>
    Interpret.fromGet
      ⟨fun s w => Interpret.get xs s (f s w)⟩

@[simp]
lemma comap_default {σ : Signature S} {M : Fam S} {x : M [^] σ} :
    Interpret.comap (default : SigMap ⦃⦄ σ) x = default := rfl

@[simp]
lemma get_comap
     {X : Fam S} {σ τ : Signature S}
    (xs : Interpret X τ) (f : SigMap σ τ) :
  Interpret.get (xs.comap f) = fun s w => Interpret.get xs s (f s w) := by
  ext; simp_all [comap, fromGet_get];

@[simp] lemma get_comap_incl_left
     {X : Fam S} {σ τ : Signature S} (xs : Interpret X (σ ⨯ τ)) :
  Interpret.get (xs.comap (SigMap.incl_left : SigMap σ (σ ⨯ τ)))
    = fun s w => Interpret.get xs s (Idx.left w) := by
  simp only [get_comap, SigMap.incl_left_apply, get_left]
  rfl

@[simp] lemma comap_fromGet {X : Fam S} {σ τ : Signature S}
    (f : IdxFam τ →ₛ X) (g : SigMap σ τ) :
  (fromGet f).comap g = fromGet (f ∘ₛ g) := by
  ext s v
  simp_all only [get_comap, fromGet_get, FamMap.comp_apply']
  rfl

@[simp]
lemma fromGet_right {σ τ : Signature S} (v : IdxFam (τ ⨯ σ) →ₛ α) :
  (fromGet v).2.get =  (v ∘ₛ SigMap.incl_right) := by
  ext s w
  set xs := fromGet v
  have hv: v = (fromGet v).get := by simp
  rw[hv]
  change xs.2.get s w = (xs.get ∘ₛ SigMap.incl_right) s w
  rcases xs with ⟨x, y⟩
  simp_all only [fromGet_get, FamMap.comp_apply', SigMap.incl_right_apply, get_right]

@[simp]
lemma fromGet_left {σ τ : Signature S} (v : IdxFam (τ ⨯ σ) →ₛ α) :
  (fromGet v).1.get =  (v ∘ₛ SigMap.incl_left) := by
  ext s w
  set xs := fromGet v
  have hv: v = (fromGet v).get := by simp
  rw[hv]
  change xs.1.get s w = (xs.get ∘ₛ SigMap.incl_left) s w
  rcases xs with ⟨x, y⟩
  simp_all only [fromGet_get, FamMap.comp_apply', SigMap.incl_left_apply, get_left]

@[simp] lemma get_comap_incl_right
     {X : Fam S} {σ τ : Signature S} (xs : Interpret X (τ ⨯ σ)) :
  Interpret.get (xs.comap (SigMap.incl_right : SigMap σ (τ ⨯ σ)))
    = fun s w => Interpret.get xs s (Idx.right w) := by
  simp only [get_comap, SigMap.incl_right_apply, get_right]
  rfl

/-- The equivalence on interpretations induced by a `SigEquiv` on signatures. -/
def Interpret.EquivfromSigEquiv
    {X : Fam S} {σ τ : Signature S} (e : SigEquiv σ τ) :
    Interpret X σ ≃ Interpret X τ :=
{ toFun := fun xs => xs.comap (Fam.PerSortEquivLike.inv e)
  , invFun := fun ys => ys.comap (e : SigMap σ τ)
  , left_inv := by
      intro xs
      ext s v
      rw [get_comap, get_comap]
      change xs.get s ((Fam.PerSortEquivLike.inv e) s (e s v)) = xs.get s v
      exact congrArg (fun x => xs.get s x) (Fam.PerSortEquivLike.inv_apply_apply e s v)
  , right_inv := by
      intro ys
      ext s v
      rw [get_comap, get_comap]
      change ys.get s (e s ((Fam.PerSortEquivLike.inv e) s v)) = ys.get s v
      exact congrArg (fun x => ys.get s x) (Fam.PerSortEquivLike.apply_inv_apply e s v) }

/-- Needed to simp away the messiness needed for quantification over "of s" -/
@[simp]
theorem nilLeft_symm_apply (s : S) :
    ((Fam.MSEquiv.symm (Signature.SigEquiv.nilLeft ⦃s⦄) :
      SigMap ⦃s⦄ (nil.prod ⦃s⦄)) s .var) = .right .var := by
  rfl

/-- Needed to simplify the "get" statement after using nilLeft_symm_apply -/
@[simp]
theorem get_right_var {X : Fam.{v} S} {s : S} {u : PUnit} {x : X s} :
    Interpret.get ((u, x) : (nil.prod ⦃s⦄).Interpret X) s (.right .var) = x := by
  simp_all only [get_right, get_of]

end interpret_equivalences
end Signature

/-! ## DepSet tuple coercions -/

namespace Fam

open Signature
open Signature.Interpret

section dep_set_tuples

variable {Sorts : Type u} {M : Fam Sorts}

instance (S : DepSet M) {σ : Signature Sorts} : CoeTC (S.Subtype[^]σ) (M[^]σ) :=
  ⟨fun xs => (S.subtypeVal) <$>ₛ xs⟩

end dep_set_tuples

end Fam

end MSFirstOrder
