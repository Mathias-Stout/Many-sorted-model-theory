import MultisortedLogic.Fam
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort


/- Basic definitions and operations for Signatures and Sorted Tuples-/

namespace MSFirstOrder

open Fam Finsupp

section signature_defs

open Finset List Finsupp

abbrev Signature (Sorts : Type z) := Sorts →₀ ℕ

namespace Signature

variable {Sorts : Type z} {σ : Signature Sorts}

def toFam {Sorts : Type z} (σ : Signature Sorts) : Sorts → Type := fun s => Fin (σ s)

open Finsupp
/-- The finite set of sorts actually used in `σ`. -/
def sorts {Sorts} (σ : Signature Sorts) : Finset Sorts :=
  σ.support

/-- The null signature: everywhere zero. -/
protected def zero Sorts : Signature Sorts := 0

/-- Add one more occurrence of sort `s` to the signature. -/
noncomputable def push {Sorts} (σ : Signature Sorts) (s : Sorts) : Signature Sorts :=
  σ.update s (σ s + 1)

lemma push_apply {Sorts : Type z} [DecidableEq Sorts]
  (σ : Signature Sorts) (s s' : Sorts) :
  (σ.push s) s' = if s = s' then σ s + 1 else σ s' :=
by
 -- unfold `push := update s (σ s + 1)`
  dsimp [push]
  simp[Function.update_apply]
  -- split on the (first) `if` which is `s' = s`
  split_ifs with h g i
  simp
  exfalso
  exact g h.symm
  simp[i]
  exfalso
  exact h i.symm
  rfl

--New proof, without the need for a DecidableEq-instance
--This is not entirely surprising: we assume the existence of a proof for s = s'
--Note: this proof is likely far from optimal
lemma push_same_imp {Sorts : Type z}
  (σ : Signature Sorts) {s s' : Sorts} : s = s' →  (σ.push s) s' = σ s' + 1  := by
  intro h
  subst h
  rw [push,update_eq_erase_add_single,add_apply,
      erase_same,single_eq_same,zero_add]

--see notes above
lemma push_diff_imp {Sorts : Type z}
  (σ : Signature Sorts) {s s' : Sorts} : (¬ s = s') →  (σ.push s) s' = σ s'  := by
  intro h
  rw[push,update_eq_erase_add_single,add_apply,
      erase_ne,single_eq_of_ne,add_zero]
  · intro h'
    exact h h'
  · intro h'
    exact h h'.symm

@[simp]
def arity (σ  : Signature Sorts):  ℕ :=  σ.sum (fun _ => id)

@[simp]
theorem arity_eq (σ : Signature Sorts) : σ.arity = ∑ s ∈ σ.support, σ s := rfl

@[simp]
theorem arity_add (σ ξ : Signature Sorts) : arity (σ + ξ) = arity σ + arity ξ :=
  Finsupp.sum_hom_add_index (fun _ => AddMonoidHom.id ℕ)

theorem arity_single {s : Sorts} {n : ℕ} : arity (single s n) = n := by simp

@[simp]
def fromList [DecidableEq Sorts] (l : List Sorts) : Signature Sorts :=
  (l : Multiset Sorts).toFinsupp

--low-level implementation which does not require Multisets
noncomputable def fromList' : (l : List Sorts) → Signature Sorts
  | [] => 0
  | x :: xs => (single x 1) + fromList' xs

/-- the two ways to create a Signature from a list agree-/
@[simp]
theorem fromList_prime_eq [DecidableEq Sorts] (l : List Sorts) :
    fromList' l = fromList l :=
  match l with
  | [] => rfl
  | x :: xs => by
    have : ((x :: xs) : Multiset Sorts) = {x} + xs  :=  rfl
    rw[fromList,this,Multiset.toFinsupp_add,Multiset.toFinsupp_singleton,fromList']
    congr
    rw [← fromList,fromList_prime_eq]


instance [DecidableEq Sorts] : Coe (List Sorts) (Signature Sorts) where
  coe := fromList

/--From Signature to List. AOC is implicitly used to order the sorts -/
noncomputable def toList : Signature Sorts → List Sorts :=
  fun σ => (σ.toMultiset).toList

/--Given an explicit total antisymmetric order on Sorts, a Signature produces an ordered list -/
def toOrderedList (r : Sorts → Sorts → Prop) [DecidableRel r] [IsTrans Sorts r] [IsAntisymm Sorts r] [IsTotal Sorts r]
    (σ : Signature Sorts) :   List Sorts :=
  Multiset.sort r (σ.toMultiset)

/-- Produce ordered given an order typeclass on the Sorts, rather than by passing an explicit order relation -/
def toOrderedList' [LinearOrder Sorts] [DecidableLE Sorts] (σ : Signature Sorts) : List Sorts :=
  toOrderedList (· ≤ ·) σ

theorem toOrderedList'_sub_supp [LinearOrder Sorts] [DecidableLE Sorts] (σ : Signature Sorts) :
  ∀ s ∈ toOrderedList' σ, s ∈ σ.support := by
  intro s hs
  rw [toOrderedList',toOrderedList,Multiset.mem_sort _] at hs
  exact (mem_toMultiset σ s).mp hs


#check List (Prop)

/- Temporary structure -/
structure sigPoint (σ : Signature Sorts) where
  sort : Sorts
  occ  : Fin (σ sort)

/-Keep track of the last sort we have seen and how many times we have seen this sort, given an *ordered* list -/
protected def toAnnotatedList_aux [LinearOrder Sorts] [DecidableLE Sorts] (l : List Sorts) (h : ∀ s ∈ l, s ∈ σ.support)
    (s : Sorts) (n : ℕ) : List (sigPoint σ) :=
  match l, h, s, n with
  | [], _,  _, _ => []
  | x :: xs, h, s, n =>
    have : NeZero (σ x) := neZero_iff.mpr <| mem_support_iff.mp (h x mem_cons_self)
    if (x = s) then
       ⟨x, Fin.ofNat (σ x) n⟩  :: Signature.toAnnotatedList_aux xs (fun s hs => h s (mem_cons_of_mem _ hs)) x (n+1)
    else
      ⟨x, Fin.ofNat (σ x) 0⟩  :: Signature.toAnnotatedList_aux xs (fun s hs => h s (mem_cons_of_mem _ hs)) x 1

/-- Produce a list an ordered List out of a signature,
  where we additionally count the number of times a sort has already occured -/
def toAnnotatedList [LinearOrder Sorts] [DecidableLE Sorts] (σ : Signature Sorts) : List (sigPoint σ) :=
  let l := σ.toOrderedList'
  have ms : ∀ s ∈ l, s ∈ σ.support := by apply toOrderedList'_sub_supp
  match l with
  | [] => []
  | x :: xs =>
    have : NeZero (σ x) := neZero_iff.mpr <| mem_support_iff.mp (ms x mem_cons_self)
    ⟨x,0⟩ :: Signature.toAnnotatedList_aux xs (fun s hs => ms s (mem_cons_of_mem _ hs)) x 1


/-- The list associated to a Signature has length equal to the arity of the given Signature -/
theorem len_list_eq_arity (σ : Signature Sorts) : (toList σ).length = (arity σ) :=
  Finsupp.induction_linear σ
      (by simp[toList,arity])
      (fun σ ξ ihs ihx => by
        rw[toList,Multiset.length_toList,card_toMultiset,arity])
      (fun s i => by simp[arity,toList])

/-- The ordered list associated to a Signature has length equal to the arity of the given Signature -/
theorem len_orderedList_eq_arity {r : Sorts → Sorts → Prop} [DecidableRel r] [IsTrans Sorts r]
    [IsAntisymm Sorts r] [IsTotal Sorts r] (σ : Signature Sorts) :
    (toOrderedList r σ).length = (arity σ) :=
  Finsupp.induction_linear σ
      (by simp[toOrderedList,arity])
      (fun σ ξ ihs ihx => by
        rw[toOrderedList,Multiset.length_sort,card_toMultiset,arity])
      (fun s i => by simp[arity,toOrderedList])

theorem len_orderedList'_eq_arity [LinearOrder Sorts] [DecidableLE Sorts] (σ : Signature Sorts) :
    (toOrderedList' σ).length = (arity σ) :=
  len_orderedList_eq_arity σ

/- Might be relevant or not
theorem len_annotatedList_eq_arity [LinearOrder Sorts] [DecidableLE Sorts] (σ : Signature Sorts) :
    (toAnnotatedList σ).length = (arity σ) := by
  have : (toAnnotatedList σ).length = (toOrderedList' σ).length := by
-/

/-- Produces a list of sorts from a Signature when the Sorts are linearly ordered -/
@[simp]
noncomputable def listOfSorts [LinearOrder Sorts] : Signature Sorts → List Sorts := fun σ =>
  sort (· ≤ ·) σ.support

@[simp]
theorem listOfSorts_nodup [LinearOrder Sorts] (σ : Signature Sorts) : Nodup σ.listOfSorts := by
  apply Finset.sort_nodup

theorem listOf_eq_zero_eq_nil [LinearOrder Sorts] {σ : Signature Sorts} (h : σ = 0) : listOfSorts σ = [] := by
  rw [listOfSorts]
  simp [h]

-- auxiliary theorem: necessary?
theorem listOfSorts_single {n : ℕ} {s : Sorts} [LinearOrder Sorts] : listOfSorts (single s n) = match n with
    | 0 => []
    | _ + 1 => [s]
  := match n with
    | 0 => by simp [listOfSorts]
    | n + 1 => by
      rw[listOfSorts, support_single_ne_zero s (Nat.succ_ne_zero n)]
      simp

/-- Summing σ over its list of sorts yields its arity -/
@[simp]
theorem arity_eq_sum_listOfSorts [LinearOrder Sorts] (σ : Signature Sorts) :
    ((listOfSorts σ).map (⇑σ)).sum = σ.arity := by
  rw[arity_eq,← List.sum_toFinset _ (listOfSorts_nodup σ)]
  simp


@[simp]
theorem toOrderedList_equiv_prime [LinearOrder Sorts] [DecidableLE Sorts] (σ : Signature Sorts) :
  toOrderedList' σ = toOrderedList (· ≤ ·) σ := rfl

theorem toList_of_eq_zero_eq_nil [LinearOrder Sorts] {σ : Signature Sorts} (h : σ = 0) : toList σ = [] := by
  simp[toList,h]

 /-- Convert a Signature σ to a map of type Fin (arity σ) → Sorts
  A linear order on the sorts ensures that this conversion is canonical-/
def toFinMap [LinearOrder Sorts] (σ : Signature Sorts) :
    Fin (arity σ) → Sorts :=
  fun i => (toOrderedList' σ).get (len_orderedList'_eq_arity σ ▸ i)

def toFinMap' [LinearOrder Sorts] (σ : Signature Sorts) :
    Fin (σ.toOrderedList'.length) → Sorts :=
  fun i => (toOrderedList' σ).get i

theorem toFinMap_eq' [LinearOrder Sorts] (σ : Signature Sorts) :
   toFinMap' σ = fun i => (toOrderedList' σ).get i := rfl

theorem toFinMap_eq [LinearOrder Sorts] (σ : Signature Sorts) :
   toFinMap σ = fun i => (toOrderedList' σ).get (len_orderedList'_eq_arity σ ▸ i) := rfl

theorem toFinMap_toFinMap' [LinearOrder Sorts] (σ : Signature Sorts) :
    toFinMap σ = toFinMap' σ ∘ (len_orderedList'_eq_arity σ ▸ ·) := by
  ext i
  rw [toFinMap_eq,toFinMap_eq']
  rfl

def fromFinMap [DecidableEq Sorts] {n : ℕ} (f : Fin n → Sorts) : Signature Sorts :=
  fromList (List.ofFn f)

lemma aux {n m : ℕ} (h : n = m) (f : Fin n → Sorts) : List.map (fun i => f i) (finRange n) = List.map (fun i => f (h ▸ i)) (finRange m) := by
  subst h
  rfl

theorem listOfFn_toFinMap [LinearOrder Sorts] (σ : Signature Sorts) : (List.ofFn (toFinMap σ)) = toOrderedList' σ := by
  rw[toFinMap_eq,ofFn_eq_map, ← aux (len_orderedList'_eq_arity σ)]
  simp

theorem fromFinMap_toFinMap [LinearOrder Sorts] (σ : Signature Sorts) :
    fromFinMap (toFinMap σ) = σ := by
  simp[fromFinMap,listOfFn_toFinMap,toOrderedList',toOrderedList]

theorem fromFinMap_arity [LinearOrder Sorts] {n : ℕ} (f : Fin n → Sorts) :
    (fromFinMap f).arity = n := by simp[fromFinMap]

instance CoeNFinarity [LinearOrder Sorts] {n : ℕ} (f : Fin n → Sorts) : Coe (Fin n) (Fin (fromFinMap f).arity) where
  coe := Fin.cast (fromFinMap_arity f).symm

instance CoeOutFinArityN [LinearOrder Sorts] {n : ℕ} (f : Fin n → Sorts) : CoeOut (Fin (fromFinMap f).arity) (Fin n) where
  coe := Fin.cast (fromFinMap_arity f)

-- Note that toFinMap (fromFinMap f) is not automatically equal to f, only a "sorted" version of f
-- todo: write a suitable Theorem that asserts this

end Signature
end signature_defs

section sorted_tuples

open Fin Signature

variable {Sorts : Type z}
variable {σ ξ : Signature Sorts}
variable {α : Sorts →  Type u'} {β : Sorts →  Type v'} {γ : Sorts → Type u₁}

abbrev sorted_tuple (σ : Signature Sorts) (g : Sorts → Type w) :=
    (s : Sorts) → Fin (σ s) → g s

instance {M}: Inhabited (sorted_tuple (0 : Signature Sorts) M) := ⟨λ t => (default : Fin 0 → M t)⟩

@[simp]
abbrev famSum (α : Sorts → Type*) (β : Sorts → Type*) := fun s => (α s) ⊕ (β s)

@[simp]
abbrev addSigVars (α : Sorts → Type*) (ξ : Signature Sorts) :=  famSum α ξ.toFam

--short definition
noncomputable def sorted_tupleToList [LinearOrder Sorts] [DecidableLE Sorts] (xs : sorted_tuple σ α) :
     List (Σ s, α s) := (σ.listOfSorts).flatMap (fun s => List.ofFn (fun i : Fin (σ s) => ⟨s, xs s i⟩))

--alternative definition
noncomputable def sorted_tupleToList' [LinearOrder Sorts] [DecidableLE Sorts] (xs : sorted_tuple σ α) :
  List (Sigma α) := σ.toAnnotatedList.map (fun ⟨s,i⟩ => ⟨s, xs s i⟩)

theorem sorted_tupleToList_len [LinearOrder Sorts] [DecidableLE Sorts] (xs : sorted_tuple σ α) :
  (sorted_tupleToList xs).length = σ.arity := by
    rw[sorted_tupleToList, List.length_flatMap]
    simp only [List.length_ofFn,arity_eq_sum_listOfSorts]

noncomputable def sorted_tupleToFinMap [LinearOrder Sorts] [DecidableLE Sorts] (xs : sorted_tuple σ α) :
    Fin σ.arity → Σ s, α s :=
  fun i => List.get (sorted_tupleToList xs) (Fin.cast (sorted_tupleToList_len xs).symm i)

--Todo: is this the correct type of coercion?
noncomputable instance CoeOutSortedTupleToListFinMap [LinearOrder Sorts] [DecidableLE Sorts] :
    CoeOut (sorted_tuple σ α) (Fin σ.arity → Σ s, α s)   where
  coe := fun xs => sorted_tupleToFinMap xs

/-- Keep only entries with first component `s`, transporting payloads to `α s`. -/
def bucket [DecidableEq Sorts] (s : Sorts) (gs : List (Sigma α)) : List (α s) :=
  gs.filterMap (fun ⟨t, a⟩ =>
    if h : t = s then
      some (h ▸ a)
    else
      none)

lemma bucket_cons [DecidableEq Sorts] (s t : Sorts) (a : α t) (gs : List (Sigma α)) :
    bucket (α := α) s (⟨t, a⟩ :: gs) =
      if h : t = s then
        (h ▸ a) :: bucket s gs
      else
        bucket s gs := by
  simp [bucket]
  split_ifs with h
  · simp[h]
  · simp[h]


/-- Low-level equivalent version of bucket-/
def bucket' [DecidableEq Sorts] (s : Sorts) (gs : List (Sigma α)) : List (α s) :=
  match gs with
  | [] => []
  | ⟨t,a⟩ :: xs =>
    if h : t = s then
      (h ▸ a) :: bucket' s xs
    else
      bucket' s xs

/-- The two ways to define the `s`-bucket agree. -/
lemma bucket_eq_bucket' [DecidableEq Sorts] (s : Sorts) (gs : List (Sigma α)) :
    bucket (α := α) s gs = bucket' s gs := by
    induction gs with
    | nil => rfl
    | cons x xs ih =>
      rcases x with ⟨t, a⟩
      by_cases h : t = s <;>
        rw[bucket_cons,bucket',ih]

@[simp] lemma bucket_nil [DecidableEq Sorts] (s : Sorts) : bucket (α := α) s [] = [] := rfl

example (x : ℕ) (xs : List ℕ) : x :: xs = [x] ++ xs := rfl

/-- The size of the `s`-bucket equals the multiplicity of `s` among first-components. -/
lemma bucket_length_eq_count [DecidableEq Sorts] (gs : List (Sigma α)) (s : Sorts) :
    (bucket (α := α) s gs).length = (gs.map Sigma.fst).count s := by
  induction gs with
  | nil => simp [bucket]
  | cons x xs ih =>
      have : x :: xs = [x] ++ xs := rfl
      rcases x with ⟨t, a⟩
      by_cases h : t = s <;>
        rw[this,bucket,List.filterMap_append] <;>
        unfold bucket at ih <;>
        simp [h,ih]

def Signature_of_sortedTuple (_gs : sorted_tuple σ α) : Signature Sorts := σ

def listToSortedTuple [DecidableEq Sorts] (gs : List (Sigma α)) :
    sorted_tuple (gs.map Sigma.fst) α :=
  fun s =>
    -- N = signature value at `s`
    let σ  := (Signature.fromList (gs.map Sigma.fst)) s
    -- N equals the length of the s-bucket
    let h : σ = (bucket (α := α) s gs).length := by

      have hb : (gs.map Sigma.fst).count s = (bucket (α := α) s gs).length := by
        simpa using (bucket_length_eq_count (α := α) gs s).symm
      have ha : (Signature.fromList (gs.map Sigma.fst)) s
                  = (gs.map Sigma.fst).count s := by simp
      exact ha.trans hb
    -- core function composed with the domain cast
    (bucket (α := α) s gs).get ∘ Fin.cast h

/-- Dependent coercion:
    `(gs : List (Σ s, α s))`  ⇝  `sorted_tuple (gs.map Sigma.fst) α`. -/
instance [DecidableEq Sorts] (gs : List (Sigma α)) : CoeDep (List (Sigma α)) gs
    (sorted_tuple (gs.map Sigma.fst) α) where
  coe := listToSortedTuple gs

/-An example of a theorem we probably want at some point
theorem signature_from_sorted_tupleTolist [LinearOrder Sorts] [DecidableLE Sorts] :
  ∀ gs : sorted_tuple σ α, List.map Sigma.fst (sorted_tupleToList gs) = σ.toOrderedList' := by sorry
-/

end sorted_tuples
