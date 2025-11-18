import MultisortedLogic.Fam
import Mathlib.Tactic

/-!
# The supporting datatype of "sorted tuples"

This file defines the SortedTuple datatype, equivalences to different representations and
a mapping over them. A SortedTuple is meant to represent a dependent vector: the type of
the entries is controlled by a list `σ` over some type `S` and an assignment `α → Type*`.
Equivalently, it is an object of type `List (Sigma α)`, with given first projection.
This abstract datatype helps convert between these different avatars while the project evolves.
The representation of SortedTuples in the final iteration might differ drastically, or an entirely
different datatype or formalism might be preferred after further testing.


## Main Definitions

- Given a type `S`, a map `α : S → Type*` and a list `σ : List S`,
  a `SortedTuple α σ` is a `List (Sigma α)` with first projection equal to `σ`
- `Sortedtuple.ofList'` converts a `List (Sigma α)` to a SortedTuple, notation `!ₛ[ ... ]`
- `SortedTuple.toMap` converts a `SortedTuple σ α` to a dependent map
  `(i : Fin σ.length) → α (σ.get i)`
- `SortedTuple.toFMap` converts a `SortedTuple σ α` to a map fibered over `S`: an object of type
  `(s : S) → { (i : Fin σ.length) // σ.get i = s } →  α s`
- `SortedTuple.append` appends two SortedTuples, similar to appending lists
- `SortedTuple.map` maps a dependent function over a SortedTuple,
  similar to List.map. Notation `<$>ₛ`


## Main theorems

- Equivalence between sorted tuples and dependent maps
  in `SortedTuple.toMap_fromMap` and `SortedTuple.fromMap_toMap`
- Equivalence between sorted tuples and maps fibered over a base `S`
  in `SortedTuple.toFMap_fromFMap` and `SortedTuple.fromFmap_toFmap`
- various helper theorems on appending,
  casting over equality of the parametrizing list `σ`, and mapping over SortedTuples
-/

universe u v w z

variable {S : Type u}

@[ext]
structure SortedTuple (σ : List S) (α : S → Type v) where
  toList : List (Sigma α)
  signature_eq : toList.map Sigma.fst = σ

namespace SortedTuple

variable {α : S → Type v} {β : S → Type w} {γ : S → Type z}
variable {σ ξ η : List S} {s : S} {x : α s}
variable {l : List (Sigma α)} {xs : SortedTuple σ α}

open List

/-- Extract the signature from a SortedTuple. -/
def signature (_xs : SortedTuple σ α) : (List S) := σ

/-- Alias for the constructor -/
def fromList (l : List (Sigma α)) (h : l.map Sigma.fst = σ) : SortedTuple σ α :=
  SortedTuple.mk l h

/-- Construct a -SortedTuple from just a List of Sigma α. -/
def fromList' (l : List (Sigma α)) : SortedTuple (l.map Sigma.fst) α :=
  fromList l rfl

syntax (name := sortedTupleNotation) "!ₛ[" term,* "]" : term

/-- Notation for constructing SortedTuples,
  similar to the one for constructing non-dependent vectors. -/
macro_rules
  | `(!ₛ[$term:term, $terms:term,*]) => `(fromList' (List.cons $term [$terms,*]))
  | `(!ₛ[$term:term]) => `(fromList' [$term])
  | `(!ₛ[]) => `(fromList' [])


/-- Abbreviation for toList.get -/
abbrev get (xs : SortedTuple σ α) := xs.toList.get

@[simp]
theorem length_eq (xs : SortedTuple σ α) : xs.toList.length = σ.length := by
  trans (xs.toList.map Sigma.fst).length
  · simp
  · rw[xs.signature_eq]

/-- Get the i-th element of the sorted tuple, casting over the equality from length_eq. -/
abbrev getFinCast (xs : SortedTuple σ α) (i : Fin σ.length) :=
  xs.get (Fin.cast xs.length_eq.symm i)

/-- A version of signature_eq specialized individual elements and taking care of resulting casts. -/
theorem proj_get (xs : SortedTuple σ α) :
    ∀ i, (xs.get i).fst = σ.get (Fin.cast xs.length_eq i) := by
  simp [xs.signature_eq.symm]

/-- A version of signature_eq,
  specialized to individual elements and taking care of resulting casts. -/
theorem proj_get' (xs : SortedTuple σ α) :
    ∀ i, (xs.getFinCast i).fst = σ.get i := by
  intro i
  rw [xs.proj_get]
  simp

/-- Theorem proj_get lifted to dependent types -/
-- TODO: Replace all uses of this theorem by calls to theorems in the Mathlib, if possible
theorem proj_type (xs : SortedTuple σ α) :
    ∀ i, α (xs.get i).fst = α (σ.get (Fin.cast xs.length_eq i)) :=
  fun i => congrArg α (xs.proj_get i)

/-- Theorem proj_get' lifted to dependent types -/
-- TODO: Replace all uses of this theorem by calls to theorems in the Mathlib, if possible
theorem proj_type' (xs : SortedTuple σ α) :  ∀ i, α (xs.getFinCast i).fst = α (σ.get i) :=
  fun i => congrArg α (xs.proj_get' i)

/-- The identity map `α (xs.get_cast i).fst → α (σ.get i)` -/
def castType {xs : SortedTuple σ α} {i : Fin (σ.length)}
    (x : α ((xs.getFinCast i)).fst) : α (σ.get i) :=
  xs.proj_get' i ▸ x

def castTypeInv {xs : SortedTuple σ α} {i : Fin (σ.length)}
    (x : α (σ.get i)) : α ((xs.getFinCast i)).fst :=
  xs.proj_get' i ▸ x

@[simp]
theorem castType_castTypeInv {xs : SortedTuple σ α} {i : Fin σ.length} :
  ∀ (x : α (σ.get i)), castType (xs.castTypeInv x) = x := by
  intro x
  unfold castType castTypeInv
  simp only [get_eq_getElem, Fin.coe_cast, eqRec_eq_cast, cast_cast, cast_eq]

@[simp]
theorem castTypeInv_castType {xs : SortedTuple σ α} {i : Fin (σ.length)} :
    ∀ (x : α ((xs.getFinCast i)).fst), castTypeInv (xs.castType x) = x := by
  intro x
  unfold castType castTypeInv
  simp only [get_eq_getElem, Fin.coe_cast, eqRec_eq_cast, cast_cast, cast_eq]

/-- castType as an equivalence. -/
def castTypeEquiv {xs : SortedTuple σ α} {i : Fin (σ.length)} :
    α ((xs.getFinCast i)).fst ≃ α (σ.get i) where
  toFun := castType
  invFun := castTypeInv
  left_inv := by apply castTypeInv_castType
  right_inv := by apply castType_castTypeInv

/- Lemma to help simplify types. -/
@[simp]
theorem toList_getElem_fst (xs : SortedTuple σ α) (n : ℕ)
    {h₁ : n < xs.toList.length} {h₂ : n < σ.length} : xs.toList[n].fst = σ[n] := by
  have h  : σ[n] = σ.get (Fin.mk n h₂) := rfl
  have h' : xs.toList[n] = xs.get (Fin.mk n h₁) := rfl
  rw [h, h']
  rw [proj_get]
  simp

@[simp]
theorem toList_fromList (l : List (Sigma α)) (h : l.map Sigma.fst = σ) :
    (fromList l h).toList = l := rfl

@[simp]
theorem fromList_toList : fromList xs.toList xs.signature_eq = xs := rfl

/-- Cast over equality of the list signatures. -/
def castL (h : σ = ξ) (xs : SortedTuple σ α) : SortedTuple ξ α :=
  fromList xs.toList (by rw[signature_eq,h])

@[simp]
theorem castL_eq {h : σ = σ} (xs : SortedTuple σ α) : xs.castL h = xs := by
  rfl

@[simp]
theorem castL_trans {η : List S} {h : σ = ξ} {h' : ξ = η} (xs : SortedTuple σ α) :
    castL h' (castL h xs) = castL (h.trans h') xs := by rfl

section asMap

/-- Construct a sorted tuple from a dependent map with domain Fin σ.length -/
def fromMap (f : (i : Fin σ.length) → α (σ.get i)) : SortedTuple σ α :=
  fromList (List.ofFn (fun i => ⟨σ.get i,f i⟩ ))
    (by rw[List.map_ofFn,Function.comp_def]; simp only [List.get_eq_getElem,
    List.ofFn_getElem])

/-- Construct a sorted tuple from a dependent map with domain Fin n and a proof that n = σ.length -/
def fromMap' {n : ℕ} (h : n = σ.length) (f : (i : Fin n) → α (σ.get (Fin.cast h i))) :
    SortedTuple σ α :=
  fromList (List.ofFn (fun i => ⟨σ.get i, f (Fin.cast h.symm i)⟩))
    (by rw[List.map_ofFn,Function.comp_def]; simp only [List.get_eq_getElem, List.ofFn_getElem])

/-- Helper theorem to flatten applications of toMap and fromMap. -/
theorem fromMap_getFinCast_eq_Sigma_mk {f : (i : Fin σ.length) → α (σ.get i)} (i : Fin σ.length) :
    (fromMap f).getFinCast i = Sigma.mk (σ.get i) (f i) := by
  simp_all only [List.get_eq_getElem, Fin.coe_cast]
  unfold fromMap
  simp only [toList_fromList]
  rw [List.getElem_ofFn]
  apply Sigma.ext
  · simp_all only [Fin.eta, List.get_eq_getElem]
  · simp_all only [Fin.eta, List.get_eq_getElem, heq_eq_eq]

/-- Convert a SortedTuple to a dependent map -/
def toMap (xs : SortedTuple σ α) : (i : Fin (σ.length)) → (α (σ.get i)) :=
  fun i =>  (xs.proj_type' i) ▸ (xs.getFinCast i).snd

@[simp]
theorem fromMap_toMap {xs : SortedTuple σ α} : fromMap xs.toMap = xs := by
  unfold toMap fromMap fromList
  apply SortedTuple.ext
  simp only [List.get_eq_getElem, Fin.coe_cast]
  refine List.ext_get ?_ ?_
  · simp
  · intro n h₁ h₂
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    refine Sigma.ext ?_ ?_
    · simp only
      rw [toList_getElem_fst]
    · simp only [eqRec_heq_iff_heq, heq_eq_eq]

-- TODO: is this helper lemma already in the Mathlib?
theorem snd_eq {x y : Sigma α} (h : α x.fst = α y.fst) (h' : x = y) : h ▸ x.snd = y.snd := by
  subst h'
  rfl

@[simp]
theorem toMap_fromMap {f : (i : Fin σ.length) → α (σ.get i)} : toMap (fromMap f) = f := by
  ext i
  unfold toMap
  rw [snd_eq ((fromMap f).proj_type' i) (fromMap_getFinCast_eq_Sigma_mk i)]

/-- Equivalence between SortedTuples and dependent maps -/
def EquivMap {S : Type u} {σ : List S} {α : S → Type v} :
    SortedTuple σ α ≃ ((i : Fin σ.length) → (α (σ.get i))) where
  toFun := toMap
  invFun := fromMap
  left_inv := by
    rw [Function.LeftInverse]
    intro xs
    apply fromMap_toMap
  right_inv := by
    rw [Function.rightInverse_iff_comp]
    funext f
    apply toMap_fromMap

/-- Get the second component of the i-th element, casting over any relevant equalities -/
abbrev get_cast {n : ℕ} {s : S} (xs : SortedTuple σ α) (i : Fin n) (hn : n = σ.length)
    (hσ : σ.get (Fin.cast hn i) = s) : α s :=
  hσ ▸ xs.toMap (Fin.cast hn i)

end asMap

section asFMap

/-- Turn a sorted tuple into a fibered map. -/
def toFMap (xs : SortedTuple σ α) : σ.toFam →ₛ α := fun _ ⟨i,h⟩ => xs.get_cast i rfl h

/-- Build a sorted tuple from a specific kind of fibered map. -/
def fromFMap (f : σ.toFam →ₛ α) : SortedTuple σ α := fromMap (fun i => f (σ.get i) ⟨i,rfl⟩)

theorem toFMap_eq (xs : SortedTuple σ α) : xs.toFMap = fun _s ⟨i,h⟩ => xs.get_cast i rfl h := rfl

@[simp]
theorem toFMap_fromFMap (f : σ.toFam →ₛ α) : (fromFMap f).toFMap = f := by
  unfold toFMap fromFMap get_cast
  funext s ⟨i,h⟩
  subst h
  simp

@[simp]
theorem fromFMap_toFMap (xs : SortedTuple σ α) : fromFMap xs.toFMap = xs := by
  unfold fromFMap toFMap get_cast
  simp

end asFMap

section extensionality

theorem eq_toList_eq_iff {xs ys : SortedTuple σ α} : xs = ys ↔ xs.toList = ys.toList := by
  apply SortedTuple.ext_iff

theorem eq_toMap_eq_iff {xs ys : SortedTuple σ α} : xs = ys ↔ xs.toMap = ys.toMap := by
  refine (Function.Injective.eq_iff ?_).symm
  refine Function.HasLeftInverse.injective ?_
  use fromMap
  apply fromMap_toMap

theorem eq_if_toMap_eq {xs ys : SortedTuple σ α} : xs.toMap = ys.toMap → xs = ys :=
  eq_toMap_eq_iff.mpr

theorem eq_if_list_eq {l₁ l₂ : List (Sigma α)} {h₁ : l₁.map Sigma.fst = σ}
    {h₂ : l₂.map Sigma.fst = σ} (h : l₁ = l₂) : fromList l₁ h₁ = fromList l₂ h₂ := by
  apply SortedTuple.ext
  simpa

end extensionality

section append

def append (xs : SortedTuple σ α) (ys : SortedTuple ξ α) : SortedTuple (σ ++ ξ) α :=
  fromList (xs.toList ++ ys.toList) (by rw [List.map_append,signature_eq,signature_eq])

def extend (xs : SortedTuple σ α) (x : α s) : SortedTuple (σ ++ [s]) α :=
  xs.append (fromList [⟨s, x⟩] rfl)

theorem toList_append (xs : SortedTuple σ α) (ys : SortedTuple ξ α) :
    (xs.append ys).toList = xs.toList ++ ys.toList := by
  unfold append
  rw [toList_fromList]

theorem toList_extend {xs : SortedTuple σ α} :
    (xs.extend x).toList = xs.toList ++ [⟨s,x⟩] := rfl

theorem append_fromList {l m : List (Sigma α)}
    {hl : l.map (Sigma.fst) = σ} {hm : m.map (Sigma.fst) = ξ} :
    (fromList l hl).append (fromList m hm) = fromList (l ++ m) (by rw[List.map_append,hl,hm]) := by
  unfold append
  simp only [toList_fromList]

theorem extend_fromMap {f : (i : Fin σ.length) → α (σ.get i)} :
    (fromMap f).extend x =
    fromList ((fromMap f).toList ++ [Sigma.mk s x]) (by simp [(fromMap f).signature_eq]) := rfl

/-- Appending is associative, up to casting over equality of lists. -/
theorem append_assoc (xs : SortedTuple σ α) (ys : SortedTuple ξ α) (zs : SortedTuple η α) :
    (xs.append ys).append zs =
    castL (Eq.symm (List.append_assoc σ ξ η)) (xs.append (ys.append zs)) := by
  unfold append castL
  simp

end append

/-Applying dependent functions to SortedTuples. -/
section maps

/-- Map a dependent function over a SortedTuple, similar to List.map. -/
def map (f : α →ₛ β) (xs : SortedTuple σ α) : SortedTuple σ β :=
  fromMap (fun i => f (σ.get i) (xs.toMap i))

/--A sorted tuple is comparable to a "dependent functor",
  so we borrow this notation for "Functor.map". -/
infixr:100 " <$>ₛ " => SortedTuple.map

theorem map_eq (f : α →ₛ β) (xs : SortedTuple σ α) :
    f <$>ₛ xs = fromMap (fun i => f (σ.get i) (xs.toMap i)) := rfl

@[simp]
theorem map_id (xs : SortedTuple σ α) : (fun _ => id) <$>ₛ xs = xs := by
  unfold map
  simp only [List.get_eq_getElem, id_eq, fromMap_toMap]

@[simp]
theorem map_id' (xs : SortedTuple σ α) : (fun _ t => t) <$>ₛ xs = xs := by
  have : (fun _ t => t : α →ₛ α) = fun _ => id := rfl
  simp [this]

theorem comp_map (φ : α →ₛ β) (ψ : β →ₛ γ)
    (xs : SortedTuple σ α) : ((ψ ∘ₛ φ) <$>ₛ xs) = ψ <$>ₛ (φ <$>ₛ xs) := by
  unfold map
  simp only [Function.comp_apply, toMap_fromMap]

theorem fromMap_map (f : (i : Fin (σ.length)) → α (σ.get i)) {g : α →ₛ β} :
    fromMap (fun i => g (σ.get i) (f i)) = g <$>ₛ fromMap f := by
  unfold map
  simp

@[simp]
theorem fromMap_map_fun_singleton {s : S} (x : α s) (f : α →ₛ β) :
    fromMap (fun i ↦ f _ (!ₛ[⟨s, x⟩].toMap i)) =  !ₛ[⟨s, f s x⟩] := rfl

-- TODO: cleaner proof preferred, without nonterminal simps
theorem toFMap_map (xs : SortedTuple σ α) (f : α →ₛ β) : (f <$>ₛ xs).toFMap = f ∘ₛ xs.toFMap := by
  funext s x
  unfold toFMap map get_cast
  simp_all only [List.get_eq_getElem, Fin.cast_eq_self, toMap_fromMap, Function.comp_apply]
  split
  rename_i x i h
  subst h
  simp_all only [List.get_eq_getElem]

-- Todo: remove sorries
theorem map_extend {β : S → Type*} {s : S} {f : α →ₛ β} (x : α s) :
    f <$>ₛ (xs.extend x) = (f <$>ₛ xs).extend (f s x) := by
    sorry

theorem map_append {β : S → Type*} {ξ : List S}
    (xs : SortedTuple σ α) (ys : SortedTuple ξ α) (f : α →ₛ β) :
    f <$>ₛ (xs.append ys) =  (f <$>ₛ xs).append (f <$>ₛ ys) := by sorry

end maps

section instances

instance {S : Type u} {α : S → Type v} : Unique (SortedTuple [] α) where
  default := fromList [] rfl
  uniq := fun xs => by
    apply SortedTuple.ext
    rw [toList_fromList,List.eq_nil_iff_length_eq_zero,xs.length_eq]
    rfl

theorem default_toMap {S : Type u} {α : S → Type v} (f : (i : Fin [].length) → α ([].get i)) :
    f = (default : SortedTuple _ _).toMap := funext (fun i => Fin.elim0 i)

@[simp]
theorem default_toFMap {S : Type*} {α : S → Type*} :
    toFMap (default : SortedTuple [] α)
    = fun s (i : [].toFam s) => IsEmpty.elim (by simp) i := by
  funext s i
  exact IsEmpty.elim (by simp) i

@[simp]
theorem default_toList {S : Type u} {α : S → Type*} :
  toList (default : SortedTuple [] α) = [] := rfl

@[simp]
theorem map_default {S : Type u} {α β : S → Type*} {f : α →ₛ β} :
  f <$>ₛ (default : SortedTuple [] α) = default := rfl

instance instDecidableEq [hyp : ∀ i : Fin σ.length, DecidableEq (α (σ.get i))] :
  DecidableEq (SortedTuple σ α) := fun xs ys =>
  if h : xs.toMap = ys.toMap then
    .isTrue <| by
    have h' := congrArg fromMap h
    rw [fromMap_toMap,fromMap_toMap] at h'
    exact h'
  else
    .isFalse fun h' => h (congrArg toMap h')

section coercions

instance CoeMap : Coe (SortedTuple σ α) ((i : Fin σ.length) → α (σ.get i)) where
  coe := toMap
/-- Coercion instance from SortedTuple to a dependent object over Sorts -/
instance instCoeFam : Coe (SortedTuple σ α) (σ.toFam →ₛ α) where
  coe := toFMap

/-- Coercion instance from a dependent map to a SortedTuple -/
instance instCoeFromMap : Coe ((i : Fin σ.length) → α (σ.get i)) (SortedTuple σ α) where
  coe := fromMap

end coercions

end instances

section induction

/- Helper definition-/
def getPrefix (xs : SortedTuple (σ ++ [s]) α) : SortedTuple σ α :=
    let l := take (xs.toList.length - 1) xs.toList
    have hlmap : l.map Sigma.fst = σ := by
      rw [List.map_take, signature_eq]
      simp
    fromList l hlmap

/- Helper definition-/
def getLast (xs : SortedTuple (σ ++ [s]) α) : α s :=
  have : 0 < xs.toList.length := by
    rw [xs.length_eq, List.length_append, List.length_singleton]
    apply Nat.zero_lt_succ
  have h : xs.toList ≠ [] := length_pos_iff.mp this
  let p := xs.toList.getLast h
  have h_proj_ne_nil : xs.toList.map Sigma.fst ≠ [] := fun h' => h (map_eq_nil_iff.mp h')
  have : p.fst = s := by
    rw [(getLast_map h_proj_ne_nil).symm]
    simp [signature_eq]
  this ▸ p.snd

/- Key lemma to define a snocInduction-/
def extend_surj {s : S} (xs : SortedTuple (σ ++ [s]) α) :
    (xs.getPrefix).extend (xs.getLast) = xs := by
  apply SortedTuple.ext
  unfold getPrefix getLast extend append
  simp only [toList_fromList]
  have : 0 < xs.toList.length := by
    rw [xs.length_eq, List.length_append]
    norm_num
  have h : xs.toList ≠ [] := length_pos_iff.mp this
  have hlx := xs.toList.take_append_getLast h
  nth_rw 6 [← hlx]
  have h_proj_ne_nil : xs.toList.map Sigma.fst ≠ [] := fun h' => h (map_eq_nil_iff.mp h')
  congr
  · rw [(getLast_map h_proj_ne_nil).symm]
    simp [signature_eq]
  · simp


/-- An analouge of Fin.snocInduction. -/
@[elab_as_elim]
def snocInduction {motive : {ξ : List S} → SortedTuple ξ α → Sort*} :
    (base :  (xs : SortedTuple [] α) → motive xs) →
    (step : (ξ : List S) → (ys : SortedTuple ξ α) → (s : S) →  (x : α s) →
      (motive ys) → motive (ys.extend x)) →
    {σ  : List S} → (xs : SortedTuple σ α) → motive xs := by
  intro hb ih σ
  apply List.reverseRecOn (motive := fun (σ : List S) => (xs : SortedTuple σ α) → motive xs) σ hb
    (fun ξ s ih' => by
    intro xs
    rw [← xs.extend_surj]
    exact ih ξ xs.getPrefix s xs.getLast (ih' xs.getPrefix)
    )

/-- Alternative SortedTuple.map using snocInduction. -/
def map' {β : S → Type*} (xs : SortedTuple σ α) (f : α →ₛ β) : SortedTuple σ β :=
  snocInduction
    (fun _ => (default : SortedTuple [] β))
    (fun ξ _ s x (ys_mapped : SortedTuple ξ β) => ys_mapped.extend (f s x)) xs

@[simp]
theorem map'_default {β : S → Type*} (f : α →ₛ β) :
    (default : SortedTuple [] α).map' f = default := by
  rw[Unique.uniq inferInstance ((default : SortedTuple [] α).map' f)]


--TODO: remove sorries
theorem map_eq_map' {f : α →ₛ β} : f <$>ₛ xs = xs.map' f := sorry

theorem map_eq_listmap {β : S → Type*} (f : α →ₛ β) :
    (f <$>ₛ xs).toList =  xs.toList.map (fun ⟨s,x⟩ => ⟨s, f s x⟩) := sorry

end induction

section experiments

/-- Convert a SortedTuple to a dependent map -/
def get' (xs : SortedTuple σ α) (s : S) (i : Fin σ.length) (h : s = σ.get i) : α s :=
  h ▸ (xs.proj_type' i) ▸ (xs.getFinCast i).snd

syntax:max term noWs "[" withoutPosition(term) "]ₛ" : term
macro_rules | `($x[$i]ₛ) => `((SortedTuple.toMap $x (Fin.mk $i (by get_elem_tactic))))

--TODO: replace this (by metaprogramming?)
/-- Evaluate a SortedTuple of length at least one at the first element. -/
def eval₁ {α : S → Type*} {σ : List S} {s : S} (xs : SortedTuple (s :: σ) α) : α s :=
  xs.toMap (Fin.mk 0 (by simp))

/-- Evaluate a SortedTuple of length at least two at the first element. -/
def eval₂₁ {α : S → Type*} {σ : List S} {s₁ s₂ : S}
    (xs : SortedTuple (s₁ :: (s₂ :: σ)) α) : α s₁ :=
  xs.toMap (Fin.mk 0 (by simp))

/-- Evaluate a SortedTuple of length at least two at the second element. -/
def eval₂₂ {α : S → Type*} {σ : List S} {s₁ s₂ : S}
    (xs : SortedTuple (s₁ :: (s₂ :: σ)) α) : α s₂ :=
  xs.toMap (Fin.mk 1 (by simp))


end experiments
end SortedTuple
