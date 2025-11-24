import MultisortedLogic.Semantics
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic

/-
Basic examples with vector spaces
We use a similar set-up as in Mathlib\ModelTheory\Algebra\Ring\Basic.lean
(authored by Chrish Hughes under the Apache 2.0 license)
Still, dependent types seem to make life harder, as is illustrated by
relatively awkward proofs for simple statements. -/


namespace MSFirstOrder

namespace MSLanguage

open MSLanguage

universe u v w z u' v'

open Finsupp Fam MSStructure Term

/- Introducing these simp lemmas to make realize expressions
easier to compress. This is obviously horrible and should be done
inductively -/
@[simp]
lemma realize_compactifier₁ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (t : Sorts) [MSStructure L' M] [NeZero ([t].length)] (b : M t) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    ((default : SortedTuple [] M).extend b).toFMap) ([t]&0) = b := rfl
@[simp]
lemma realize_compactifier₂₁ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (s t : Sorts) [MSStructure L' M] [NeZero ([s, t].length)] (a : M s) (b : M t) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    (((default : SortedTuple [] M).extend a).extend b).toFMap) ([s,t]&0) = a := rfl
@[simp]
lemma realize_compactifier₂₂ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (s t : Sorts) [MSStructure L' M] [NeZero ([s, t].length)] (a : M s) (b : M t) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    (((default : SortedTuple [] M).extend a).extend b).toFMap) ([s,t]&1) = b := rfl
@[simp]
lemma realize_compactifier₃₁ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (s t r : Sorts) [MSStructure L' M] [NeZero ([s, t, r].length)] (a : M s) (b : M t) (c : M r) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    ((((default : SortedTuple [] M).extend a).extend b).extend c).toFMap) ([s,t,r]&0) = a := rfl
@[simp]
lemma realize_compactifier₃₂ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (s t r : Sorts) [MSStructure L' M] [NeZero ([s, t, r].length)] (a : M s) (b : M t) (c : M r) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    ((((default : SortedTuple [] M).extend a).extend b).extend c).toFMap) ([s,t,r]&1) = b := rfl
@[simp]
lemma realize_compactifier₃₃ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (s t r : Sorts) [MSStructure L' M] [NeZero ([s, t, r].length)] (a : M s) (b : M t) (c : M r) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    ((((default : SortedTuple [] M).extend a).extend b).extend c).toFMap) ([s,t,r]&2) = c := rfl
@[simp]
lemma realize_compactifier₄₁ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (s t r x : Sorts) [MSStructure L' M]
    [NeZero ([s, t, r, x].length)] (a : M s) (b : M t) (c : M r) (d : M x) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    (((((default : SortedTuple [] M).extend a).extend b).extend c).extend d).toFMap)
      ([s,t,r,x]&0) = a := rfl
@[simp]
lemma realize_compactifier₄₂ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (s t r x : Sorts) [MSStructure L' M]
    [NeZero ([s, t, r, x].length)] (a : M s) (b : M t) (c : M r) (d : M x) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    (((((default : SortedTuple [] M).extend a).extend b).extend c).extend d).toFMap)
      ([s,t,r,x]&1) = b := rfl
@[simp]
lemma realize_compactifier₄₃ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (s t r x : Sorts) [MSStructure L' M]
    [NeZero ([s, t, r, x].length)] (a : M s) (b : M t) (c : M r) (d : M x) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    (((((default : SortedTuple [] M).extend a).extend b).extend c).extend d).toFMap)
      ([s,t,r,x]&2) = c := rfl
@[simp]
lemma realize_compactifier₄₄ {Sorts : Type _} {L' : MSLanguage Sorts} (M : Sorts → Type u)
  (s t r x : Sorts) [MSStructure L' M]
    [NeZero ([s, t, r, x].length)] (a : M s) (b : M t) (c : M r) (d : M x) :
  realize (L := L') (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
    (((((default : SortedTuple [] M).extend a).extend b).extend c).extend d).toFMap)
      ([s,t,r,x]&3) = d := rfl

lemma lists_are_the_same {Sorts : Type*} {σ : List Sorts} {α : Sorts → Type*}
  {s : Sorts} :
  α (σ ++ [s])[σ.length] = α s := by simp
@[simp]
lemma realize_compactifier
    {Sorts : Type u} {L' : MSLanguage Sorts}
    (M : Sorts → Type v) (σ : List Sorts) (s : Sorts)
    [MSStructure L' M] (b : M s) :
  realize (L := L')
    (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
      (SortedTuple.extend (SortedTuple.{u, v} σ M) b).toFMap)
    ((σ ++ [s])&⟨σ.length, by
      simp [List.length_append]⟩)
  = b :=
rfl

@[simp]
lemma realize_compactifier
    {Sorts : Type u} {L' : MSLanguage Sorts}
    (M : Sorts → Type v) (σ : List Sorts) (s : Sorts)
    [MSStructure L' M] (b : M s) :
  realize (L := L')
    (Fam.sumElim (fun _ (a : Empty) => Empty.elim a)
      (SortedTuple.extend (SortedTuple σ M) b).toFMap)
    ((σ ++ [s]) & Fin.last (σ.length))
  = b := by
  -- This is the key fact:
  simpa using
    SortedTuple.extend_getElem_self (σ := σ) (M := M) (b := b)

end MSLanguage
end MSFirstOrder
