/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/

module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# Many-sorted first-order logic: languages and structures

Arities, languages, structures, and the maps between structures of many-sorted first-order logic.
Terms and formulas are defined in `Syntax.lean` and their realization in `Semantics.lean`.

## Main declarations

* `Arity S`: encodes the shape of a product of types. Mathematically, an object `σ : Arity S`
  corresponds to an element of the free magma on `S ⊔ {0}`. Given a realization `M : S → Type*`
  of the sorts, `M [^] σ` denotes the (non-associative!) product of types `M s` of shape `σ`.
* `σ.Idx s`: an element `σ : Arity S` may be viewed as a tree. Then `σ.Idx s` is the type of the
  leaves in `σ` with label `s`.
* `Language`, `Language.Structure`: definition of the type of a many-sorted first-order language
  and structure
* `Language.Hom`, `Language.Embedding`, `Language.Equiv` (`M →[L] N`, `M ↪[L] N`, `M ≃[L] N`):
  homomorphisms, embeddings and equivalences, with corresponding classes `HomClass` and
  `StrongHomClass`.

## Design notes
* `Arity S` occurs essentially everywhere where `ℕ` would be used to denote arity in a one-sorted
  development.
* `M [^] σ` is reducible and computes nested products, with `M [^] ⦃s⦄ = M s`. This is what
  makes a sentence `∀' s φ` unfold to a statement quantifying over `M s`.
* A sort coerces to the one-sort arity, so `∀' s φ` and `∀' ⦃s⦄ φ` are the same notation.
* Concrete languages should be reducible (`abbrev`), so that their symbols have the type
  `L.Functions σ t` without unfolding `L`; otherwise `simp` cannot rewrite their realization.
* Unification trap: `?M ?t =?= M [^] ⦃t⦄` is solved by `?M := Interpret M`. Where the carrier of
  `funMap` is only determined by the expected type, pass it explicitly as `(M := M)`.
* In the interest of conciseness, we do not provide the left-handed counterpart to `extendRight`.
  As it turns out, this is never needed in our following development.

## References

This file was originally based on `Mathlib/ModelTheory/Basic.lean`, by Aaron Anderson, Jesse Michael
Han and Floris van Doorn.
-/

@[expose] public section

universe u v w w' z u'

namespace ManySorted

/-! ### Arities -/

/-- An arity over the sorts `S`: it encodes a finite non-associative product of model-theoretic
  sorts. As an example, `(σ ⨯ τ) ⨯ ρ` and `σ ⨯ (τ ⨯ ρ)` are different, but their interpretations
  are canonically isomorphic. See also the definition of `Interpret`. -/
inductive Arity (S : Type z) where
  /-- The empty product. -/
  | nil : Arity S
  /-- A single sort. -/
  | of : S → Arity S
  /-- The product of two arities. -/
  | prod : Arity S → Arity S → Arity S
  deriving DecidableEq

-- Write as `\X`, not as `\x`.
@[inherit_doc] scoped[ManySorted] infixl:70 " ⨯ " => ManySorted.Arity.prod
@[inherit_doc] scoped[ManySorted] notation "⦃" s "⦄" => ManySorted.Arity.of s
@[inherit_doc] scoped[ManySorted] notation "⦃⦄" => ManySorted.Arity.nil

namespace Arity

variable {S : Type z}

instance : Coe S (Arity S) := ⟨of⟩

/-- `M [^] σ` is the product of the carriers `M s` over the sorts of `σ`, bracketed like `σ`.
For a single sort it is `M s` itself. -/
@[reducible] def Interpret (M : S → Type w) : Arity S → Type w
  | ⦃⦄ => PUnit
  | ⦃s⦄ => M s
  | σ ⨯ τ => Interpret M σ × Interpret M τ

@[inherit_doc] scoped[ManySorted] notation:80 M " [^] " σ:81 => ManySorted.Arity.Interpret M σ

/-- `σ.Idx s` is the type of positions of sort `s` in the arity `σ`. Short for 'Index'. -/
inductive Idx : Arity S → S → Type z
  /-- The unique position of `⦃s⦄`. -/
  | var {s : S} : Idx ⦃s⦄ s
  /-- A position in the left factor of a product. -/
  | left {σ τ : Arity S} {s : S} : Idx σ s → Idx (σ ⨯ τ) s
  /-- A position in the right factor of a product. -/
  | right {σ τ : Arity S} {s : S} : Idx τ s → Idx (σ ⨯ τ) s

namespace Idx

/-- Extend a map of positions by the identity on an extra right factor. -/
def extendRight {σ τ ρ : Arity S} (g : ∀ s, σ.Idx s → τ.Idx s) :
    ∀ s, (σ ⨯ ρ).Idx s → (τ ⨯ ρ).Idx s
  | _, .left i => .left (g _ i)
  | _, .right j => .right j

@[simp]
lemma extendRight_left {σ τ ρ : Arity S} (g : ∀ s, σ.Idx s → τ.Idx s) {s : S}
    (i : σ.Idx s) : extendRight (ρ := ρ) g s (.left i) = .left (g s i) := rfl

@[simp]
lemma extendRight_right {σ τ ρ : Arity S} (g : ∀ s, σ.Idx s → τ.Idx s) {s : S}
    (j : ρ.Idx s) : extendRight g s (.right j) = .right j := rfl

/-- Build a (dependent) map on `(σ ⨯ τ).Idx` from a map `σ.Idx` and `τ.Idx`. -/
def elim {σ τ : Arity S} {C : S → Sort*} (f : ∀ s, σ.Idx s → C s) (g : ∀ s, τ.Idx s → C s) :
    ∀ s, (σ ⨯ τ).Idx s → C s
  | _, .left i => f _ i
  | _, .right j => g _ j

@[simp]
lemma elim_left {σ τ : Arity S} {C : S → Sort*} (f : ∀ s, σ.Idx s → C s)
    (g : ∀ s, τ.Idx s → C s) {s : S} (i : σ.Idx s) : elim f g s (.left i) = f s i := rfl

@[simp]
lemma elim_right {σ τ : Arity S} {C : S → Sort*} (f : ∀ s, σ.Idx s → C s)
    (g : ∀ s, τ.Idx s → C s) {s : S} (j : τ.Idx s) : elim f g s (.right j) = g s j := rfl

@[simp]
lemma elim_comp_left {σ τ : Arity S} {C : S → Sort*} (f : ∀ s, σ.Idx s → C s)
    (g : ∀ s, τ.Idx s → C s) (s : S) : elim f g s ∘ .left = f s := rfl

@[simp]
lemma elim_comp_right {σ τ : Arity S} {C : S → Sort*} (f : ∀ s, σ.Idx s → C s)
    (g : ∀ s, τ.Idx s → C s) (s : S) : elim f g s ∘ .right = g s := rfl

/-- The empty arity has no positions. -/
def elimNil {C : S → Sort*} : ∀ s, (⦃⦄ : Arity S).Idx s → C s := fun _ i => nomatch i

/-- Drop an empty right factor, `σ ⨯ ⦃⦄ → σ`. -/
def nilRight {σ : Arity S} : ∀ s, (σ ⨯ ⦃⦄).Idx s → σ.Idx s
  | _, .left i => i

/-- Reassociate positions, `σ ⨯ (τ ⨯ ρ) → (σ ⨯ τ) ⨯ ρ`. -/
def assoc {σ τ ρ : Arity S} : ∀ s, (σ ⨯ (τ ⨯ ρ)).Idx s → ((σ ⨯ τ) ⨯ ρ).Idx s
  | _, .left i => .left (.left i)
  | _, .right (.left j) => .left (.right j)
  | _, .right (.right k) => .right k

/- ## OPEN QUESTION:
  We would be interested in experimenting with some metaprogramming to help deal with associativity
  of arities. Any input from the community on this is appreciated.
-/

end Idx

section Mem

variable {s : S}

/-- Membership of sort `s` in Arity `σ`, mirroring the construction for `List`. -/
inductive Mem (s : S) : Arity S → Prop
 | of : Mem s ⦃s⦄
 | left {σ τ : Arity S} : Mem s σ → Mem s (σ ⨯ τ)
 | right {σ τ : Arity S} : Mem s τ → Mem s (σ ⨯ τ)

/-- A sort `s` occurs in `σ`, written `s ∈ σ`, if `σ` has a position of sort `s`. -/
instance : Membership S (Arity S) where
  mem σ s := Mem s σ

@[simp]
theorem notMem_nil : s ∉ (⦃⦄ : Arity S) := nofun

@[simp]
theorem mem_of {t : S} : s ∈ ⦃t⦄ ↔ s = t := ⟨fun h => by cases h; rfl, fun h => h ▸ Mem.of⟩

theorem mem_of_self : s ∈ ⦃s⦄ := by simp only [mem_of]

theorem mem_left {σ τ : Arity S} : s ∈ σ → s ∈ σ ⨯ τ := .left

theorem mem_right {σ τ : Arity S} : s ∈ τ → s ∈ σ ⨯ τ := .right

@[simp]
theorem mem_prod {σ τ : Arity S} : s ∈ σ ⨯ τ ↔ s ∈ σ ∨ s ∈ τ :=
  ⟨fun h => by cases h with
    | left hl => exact .inl hl
    | right hr => exact .inr hr,
   fun h => h.elim mem_left mem_right⟩

/-- A sort with a position in `σ` occurs in `σ`. -/
theorem Idx.mem {σ : Arity S} : σ.Idx s → s ∈ σ
  | .var => mem_of_self
  | .left i => mem_left i.mem
  | .right i => mem_right i.mem

theorem mem_iff_nonempty {σ : Arity S} : s ∈ σ ↔ Nonempty (σ.Idx s) :=
  ⟨fun h => by
    induction h with
    | of => exact ⟨.var⟩
    | left _ ih => exact ih.map .left
    | right _ ih => exact ih.map .right,
   fun ⟨i⟩ => i.mem⟩

end Mem

namespace Interpret

variable {M : S → Type w}

/-- The entry of a tuple at a position `i : σ.Idx s`. -/
def get : {σ : Arity S} → M [^] σ → (s : S) → σ.Idx s → M s
  | _, x, _, .var => x
  | _, x, _, .left i => get x.1 _ i
  | _, x, _, .right i => get x.2 _ i

@[simp]
lemma get_var {s : S} (x : M [^] ⦃s⦄) : get x s .var = x := rfl

@[simp]
lemma get_left {σ τ : Arity S} {s : S} (x : M [^] (σ ⨯ τ)) (i : σ.Idx s) :
    get x s (.left i) = get x.1 s i := rfl

@[simp]
lemma get_right {σ τ : Arity S} {s : S} (x : M [^] (σ ⨯ τ)) (i : τ.Idx s) :
    get x s (.right i) = get x.2 s i := rfl

/-- The tuple with prescribed entries at each position of `σ.Idx`. -/
def ofFn : {σ : Arity S} → (∀ s, σ.Idx s → M s) → M [^] σ
  | nil, _ => PUnit.unit
  | of s, f => f s .var
  | prod _ _, f => (ofFn fun s i => f s (.left i), ofFn fun s i => f s (.right i))

/-- `get` is a left inverse of `ofFn`. -/
@[simp]
theorem get_ofFn : ∀ {σ : Arity S} (f : ∀ s, σ.Idx s → M s) (s : S) (i : σ.Idx s),
    get (ofFn f) s i = f s i
  | _, _, _, .var => rfl
  | _, f, _, .left i => get_ofFn (fun s i => f s (.left i)) _ i
  | _, f, _, .right i => get_ofFn (fun s i => f s (.right i)) _ i

@[simp]
lemma ofFn_fst {σ τ : Arity S} (f : ∀ s, (σ ⨯ τ).Idx s → M s) :
    (ofFn f).1 = ofFn fun s i => f s (.left i) := rfl

@[simp]
lemma ofFn_snd {σ τ : Arity S} (f : ∀ s, (σ ⨯ τ).Idx s → M s) :
    (ofFn f).2 = ofFn fun s i => f s (.right i) := rfl

/-- `get` is a right inverse of `ofFn`. -/
@[simp]
theorem ofFn_get : ∀ {σ : Arity S} (x : M [^] σ), ofFn (get x) = x
  | nil, _ => rfl
  | of _, _ => rfl
  | prod _ _, (x, y) => congrArg₂ Prod.mk (ofFn_get x) (ofFn_get y)

theorem get_injective {σ : Arity S} : Function.Injective (get : M [^] σ → _) :=
  Function.LeftInverse.injective ofFn_get

theorem ext {σ : Arity S} {x y : M [^] σ} (h : ∀ s i, get x s i = get y s i) : x = y :=
  get_injective (funext₂ h)

theorem ext_iff {σ : Arity S} {x y : M [^] σ} : x = y ↔ ∀ s i, get x s i = get y s i :=
  ⟨fun h _ _ => h ▸ rfl, ext⟩

/-- Pull a tuple back along a map of positions. -/
def comap {τ : Arity S} : {σ : Arity S} → (∀ s, σ.Idx s → τ.Idx s) →  M [^] τ →  M [^] σ
  | nil, _ , _ => PUnit.unit
  | of s, g, x => x.get s (g s .var)
  | prod _ _, g, x => (comap (fun s => g s ∘ .left) x, comap (fun s => g s ∘ .right) x)

theorem comap_eq_ofFn {σ τ : Arity S} (g : ∀ s, σ.Idx s → τ.Idx s) (x : M [^] τ) :
    x.comap g = ofFn (fun s i => x.get s (g s i)) := by
  cases σ with
  | nil => rfl
  | of s => rfl
  | prod σ₁ σ₂ =>
    rw [Interpret.comap, ofFn, comap_eq_ofFn, comap_eq_ofFn]
    simp only [Function.comp_apply]

@[simp]
lemma get_comap {σ τ : Arity S} (g : ∀ s, σ.Idx s → τ.Idx s) (x : M [^] τ) (s : S)
    (i : σ.Idx s) : get (comap g x) s i = get x s (g s i) := by
  rw [comap_eq_ofFn]
  exact get_ofFn _ _ _

/-! The tuple form of the `Idx` combinators: pulling back along each of them. The input tuple is a
variable rather than a literal pair, so that `simp` also applies these lemmas under binders. -/

@[simp]
theorem comap_id {σ : Arity S} (x : M [^] σ) : x.comap (fun _ i => i) = x := by
  rw [comap_eq_ofFn]
  exact ofFn_get x

@[simp]
theorem comap_ofFn {σ τ : Arity S} (g : ∀ s, σ.Idx s → τ.Idx s) (f : ∀ s, τ.Idx s → M s) :
    (ofFn f).comap g = ofFn fun s => f s ∘ g s := by
  rw [comap_eq_ofFn]
  simp only [get_ofFn]
  rfl

@[simp]
theorem comap_left {σ τ : Arity S} (x : M [^] (σ ⨯ τ)) : x.comap (fun _ => .left) = x.1 := by
  rw [comap_eq_ofFn]
  exact ofFn_get x.1

@[simp]
theorem comap_right {σ τ : Arity S} (x : M [^] (σ ⨯ τ)) : x.comap (fun _ => .right) = x.2 := by
  rw [comap_eq_ofFn]
  exact ofFn_get x.2

@[simp]
theorem comap_extendRight {σ τ ρ : Arity S} (g : ∀ s, σ.Idx s → τ.Idx s) (x : M [^] (τ ⨯ ρ)) :
    x.comap (Idx.extendRight g) = ((x.1.comap g, x.2) : M [^] (σ ⨯ ρ)) := by
  rw [comap_eq_ofFn, comap_eq_ofFn]
  exact Prod.ext rfl (ofFn_get x.2)

@[simp]
theorem comap_nilRight {σ : Arity S} (x : M [^] σ) :
    x.comap (Idx.nilRight (σ := σ)) = ((x, PUnit.unit) : M [^] (σ ⨯ ⦃⦄)) := by
  rw [comap_eq_ofFn]
  exact Prod.ext (ofFn_get x) rfl

@[simp]
theorem comap_assoc {σ τ ρ : Arity S} (x : M [^] ((σ ⨯ τ) ⨯ ρ)) :
    x.comap Idx.assoc = ((x.1.1, (x.1.2, x.2)) : M [^] (σ ⨯ (τ ⨯ ρ))) := by
  rw [comap_eq_ofFn]
  exact Prod.ext (ofFn_get x.1.1) (Prod.ext (ofFn_get x.1.2) (ofFn_get x.2))

/-- Apply a family of maps entrywise. -/
def map {N : S → Type w'} (f : ∀ s, M s → N s) : {σ : Arity S} → M [^] σ → N [^] σ
  | nil, _ => PUnit.unit
  | of s, x => f s x
  | prod _ _, x => (map f x.1, map f x.2)

section map

variable {N : S → Type w'} {P : S → Type u'} (f : ∀ s, M s → N s)

@[simp]
lemma map_of {s : S} (x : M [^] ⦃s⦄) : map f x = f s x := rfl

@[simp]
lemma map_mk {σ τ : Arity S} (x : M [^] σ) (y : M [^] τ) :
    map (σ := σ ⨯ τ) f (x, y) = (map f x, map f y) := rfl

@[simp]
lemma map_fst {σ τ : Arity S} (x : M [^] (σ ⨯ τ)) :
    (map (σ := σ ⨯ τ) f x).1 = map f x.1 := rfl

@[simp]
lemma map_snd {σ τ : Arity S} (x : M [^] (σ ⨯ τ)) :
    (map (σ := σ ⨯ τ) f x).2 = map f x.2 := rfl

@[simp]
theorem get_map : ∀ {σ : Arity S} (x : M [^] σ) (s : S) (i : σ.Idx s),
    get (map f x) s i = f s (get x s i)
  | _, _, _, .var => rfl
  | _, x, _, .left i => get_map x.1 _ i
  | _, x, _, .right i => get_map x.2 _ i

theorem map_map (g : ∀ s, N s → P s) :
    ∀ {σ : Arity S} (x : M [^] σ), map g (map f x) = map (fun s => g s ∘ f s) x
  | nil, _ => rfl
  | of _, _ => rfl
  | prod _ _, x => congrArg₂ Prod.mk (map_map g x.1) (map_map g x.2)

theorem map_ofFn {σ : Arity S} (g : ∀ s, σ.Idx s → M s) :
    map f (ofFn g) = ofFn fun s => (f s) ∘ (g s) :=
  ext fun s i => by simp only [get_map, get_ofFn, Function.comp_apply]

@[simp]
theorem map_id : ∀ {σ : Arity S} (x : M [^] σ), map (fun _ => id) x = x
  | nil, _ => rfl
  | of _, _ => rfl
  | prod _ _, x => congrArg₂ Prod.mk (map_id x.1) (map_id x.2)

@[simp]
theorem map_id' {σ : Arity S} (x : M [^] σ) : map (fun _ a => a) x = x :=
  map_id x

variable {f}

theorem map_injective (hf : ∀ s, Function.Injective (f s)) :
    ∀ {σ : Arity S}, Function.Injective (map f : M [^] σ → N [^] σ)
  | nil => Function.injective_of_subsingleton _
  | of s => hf s
  | prod _ _ => (map_injective hf).prodMap (map_injective hf)

/-- `map f` is surjective on tuples of shape `σ` as soon as `f s` is surjective for all `s ∈ σ`. -/
theorem map_surjective : ∀ {σ : Arity S}, (∀ s ∈ σ, Function.Surjective (f s)) →
    Function.Surjective (map f : M [^] σ → N [^] σ)
  | nil, _ => fun _ => ⟨PUnit.unit, rfl⟩
  | of _, hf => hf _ mem_of_self
  | prod _ _, hf =>
    (map_surjective fun s h => hf s (mem_left h)).prodMap
      (map_surjective fun s h => hf s (mem_right h))

end map

section merge

/- A map `n₁ : ∀ s, ctx₁.Idx s → α s` can be seen as assigning names from `α` to each position in
 ctx₁.Idx. -/
variable {α : S → Type u'} {σ ctx₁ ctx₂ : Arity S} (n₁ : ∀ s, ctx₁.Idx s → α s)
  (n₂ : ∀ s, ctx₂.Idx s → α s) (v : ∀ s, α s → M s) (xs : M [^] σ)

/-- Merging two families of names, seen from the left family: the entries of the named part
`ctx₁` of a tuple are unchanged when `ctx₂` is placed next to it. -/
theorem get_ofFn_elim_left (s : S) (i : (ctx₁ ⨯ σ).Idx s) :
    get (σ := ctx₁ ⨯ σ) (ofFn fun s => v s ∘ n₁ s, xs) s i =
      get (σ := (ctx₁ ⨯ ctx₂) ⨯ σ) (ofFn fun s => v s ∘ Idx.elim n₁ n₂ s, xs) s
        (Idx.extendRight (fun _ => .left) s i) := by
  cases i <;> simp

/-- Merging two families of names, seen from the right family. -/
theorem get_ofFn_elim_right (s : S) (i : (ctx₂ ⨯ σ).Idx s) :
    get (σ := ctx₂ ⨯ σ) (ofFn fun s => v s ∘ n₂ s, xs) s i =
      get (σ := (ctx₁ ⨯ ctx₂) ⨯ σ) (ofFn fun s => v s ∘ Idx.elim n₁ n₂ s, xs) s
        (Idx.extendRight (fun _ => .right) s i) := by
  cases i <;> simp

end merge

instance nonempty [∀ s, Nonempty (M s)] {σ : Arity S} : Nonempty (M [^] σ) := by
  induction σ with
  | nil => exact ⟨PUnit.unit⟩
  | of s => exact inferInstanceAs (Nonempty (M s))
  | prod σ τ ih₁ ih₂ =>
    obtain ⟨a⟩ := ih₁
    obtain ⟨b⟩ := ih₂
    exact ⟨(a, b)⟩

end Interpret

/-- Resolves the de Bruijn index `n` to a position of sort `s` in a stack-shaped arity
`((⦃s₀⦄ ⨯ ⦃s₁⦄) ⨯ …) ⨯ ⦃sₖ⦄` (possibly starting with `⦃⦄`), counting from the right. -/
class VarIndex (σ : Arity S) (n : ℕ) (s : outParam S) where
  /-- The position that the numeral resolves to. -/
  get : σ.Idx s

instance VarIndex.instOf {s : S} : VarIndex ⦃s⦄ 0 s := ⟨.var⟩

instance VarIndex.instZero {σ : Arity S} {s : S} : VarIndex (σ ⨯ ⦃s⦄) 0 s := ⟨.right .var⟩

instance VarIndex.instSucc {σ τ : Arity S} {n : ℕ} {s : S} [i : VarIndex σ n s] :
    VarIndex (σ ⨯ τ) (n + 1) s :=
  ⟨.left i.get⟩

/-! `simp` does not rewrite inside instance arguments, so tagging the instances `@[simp]` would
not reduce `VarIndex.get`; these lemmas name the instance on the left-hand side instead. -/

@[simp]
lemma VarIndex.get_instOf {s : S} : (instOf (s := s)).get = .var := rfl

@[simp]
lemma VarIndex.get_instZero {σ : Arity S} {s : S} :
    (instZero (σ := σ) (s := s)).get = .right .var := rfl

@[simp]
lemma VarIndex.get_instSucc {σ τ : Arity S} {n : ℕ} {s : S} [i : VarIndex σ n s] :
    (instSucc (τ := τ) (i := i)).get = .left i.get := rfl

end Arity

open Arity

/-! ### Languages and structures -/

/-- A many-sorted first-order language: function symbols with an input arity and an output sort,
and relation symbols with an arity. -/
structure Language (S : Type z) where
  /-- The function symbols `σ → t`. -/
  Functions : Arity S → S → Type u
  /-- The relation symbols on `σ`. -/
  Relations : Arity S → Type v

namespace Language

variable {S : Type z} (L : Language.{u, v} S)

/-- Constant symbols of sort `t`: function symbols with empty input. -/
protected abbrev Constants (t : S) := L.Functions ⦃⦄ t

/-- An `L`-structure on a family of carriers `M`. -/
class Structure (M : S → Type w) where
  /-- The interpretation of a function symbol. -/
  funMap : ∀ {σ t}, L.Functions σ t → M [^] σ → M t
  /-- The interpretation of a relation symbol. -/
  RelMap : ∀ {σ}, L.Relations σ → M [^] σ → Prop

open Structure

/-! ### Homomorphisms, embeddings and equivalences

These are families of Mathlib's maps, embeddings and equivalences, one per sort, commuting with
the symbols. They coerce to families of functions through `DFunLike`. -/

section Maps

variable (M : S → Type w) (N : S → Type w') [L.Structure M] [L.Structure N]

/-- A homomorphism of `L`-structures: a family of maps that commutes with the function symbols and
preserves the relation symbols. -/
structure Hom where
  /-- The underlying family of maps. -/
  toFun : ∀ s, M s → N s
  /-- The maps commute with the interpretations of the function symbols. -/
  map_fun' : ∀ {σ t} (f : L.Functions σ t) (x : M [^] σ),
    toFun t (funMap f x) = funMap f (x.map toFun)
  /-- The maps send related tuples to related tuples. -/
  map_rel' : ∀ {σ} (r : L.Relations σ) (x : M [^] σ), RelMap r x → RelMap r (x.map toFun)

/-- An embedding of `L`-structures: a family of embeddings that commutes with the function
symbols and preserves and reflects the relation symbols. -/
structure Embedding where
  /-- The underlying family of embeddings. -/
  toEmbedding : ∀ s, M s ↪ N s
  /-- The embeddings commute with the interpretations of the function symbols. -/
  map_fun' : ∀ {σ t} (f : L.Functions σ t) (x : M [^] σ),
    toEmbedding t (funMap f x) = funMap f (x.map (fun s => toEmbedding s))
  /-- The embeddings preserve and reflect the relations. -/
  map_rel' : ∀ {σ} (r : L.Relations σ) (x : M [^] σ),
    RelMap r (x.map fun s => toEmbedding s) ↔ RelMap r x

/-- An isomorphism of `L`-structures: a family of equivalences that commutes with the function
symbols and preserves and reflects the relation symbols. -/
structure Equiv where
  /-- The underlying family of equivalences. -/
  toEquiv : ∀ s, M s ≃ N s
  /-- The equivalences commute with the interpretations of the function symbols. -/
  map_fun' : ∀ {σ t} (f : L.Functions σ t) (x : M [^] σ),
    toEquiv t (funMap f x) = funMap f (x.map fun s => toEquiv s)
  /-- The equivalences preserve and reflect the relations. -/
  map_rel' : ∀ {σ} (r : L.Relations σ) (x : M [^] σ),
    RelMap r (x.map fun s => toEquiv s) ↔ RelMap r x

@[inherit_doc] scoped[ManySorted] notation:25 A " →[" L "] " B => ManySorted.Language.Hom L A B
@[inherit_doc] scoped[ManySorted] notation:25 A " ↪[" L "] " B =>
  ManySorted.Language.Embedding L A B
@[inherit_doc] scoped[ManySorted] notation:25 A " ≃[" L "] " B => ManySorted.Language.Equiv L A B

instance : DFunLike (M →[L] N) S fun s => M s → N s where
  coe φ := φ.toFun
  coe_injective φ ψ h := by cases φ; cases ψ; cases h; rfl

instance : DFunLike (M ↪[L] N) S fun s => M s → N s where
  coe φ s := φ.toEmbedding s
  coe_injective φ ψ h := by
    obtain ⟨φ, _, _⟩ := φ
    obtain ⟨ψ, _, _⟩ := ψ
    obtain rfl : φ = ψ := funext fun s => DFunLike.coe_injective (congrFun h s)
    rfl

instance : DFunLike (M ≃[L] N) S fun s => M s → N s where
  coe φ s := φ.toEquiv s
  coe_injective φ ψ h := by
    obtain ⟨φ, _, _⟩ := φ
    obtain ⟨ψ, _, _⟩ := ψ
    obtain rfl : φ = ψ := funext fun s => DFunLike.coe_injective (congrFun h s)
    rfl

end Maps

/-- `HomClass L F M N`: the elements of `F` are homomorphisms of `L`-structures `M → N`. -/
class HomClass (L : outParam (Language.{u, v} S)) (F : Type*) (M : outParam (S → Type w))
    (N : outParam (S → Type w')) [DFunLike F S fun s => M s → N s] [L.Structure M]
    [L.Structure N] : Prop where
  /-- The maps commute with the interpretations of the function symbols. -/
  map_fun : ∀ (φ : F) {σ t} (f : L.Functions σ t) (x : M [^] σ),
    φ t (funMap f x) = funMap f (x.map φ)
  /-- The maps send related tuples to related tuples. -/
  map_rel : ∀ (φ : F) {σ} (r : L.Relations σ) (x : M [^] σ), RelMap r x → RelMap r (x.map φ)

/-- `StrongHomClass L F M N`: the elements of `F` are homomorphisms of `L`-structures `M → N`
that also reflect the relation symbols. -/
class StrongHomClass (L : outParam (Language.{u, v} S)) (F : Type*) (M : outParam (S → Type w))
    (N : outParam (S → Type w')) [DFunLike F S fun s => M s → N s] [L.Structure M]
    [L.Structure N] : Prop where
  /-- The maps commute with the interpretations of the function symbols. -/
  map_fun : ∀ (φ : F) {σ t} (f : L.Functions σ t) (x : M [^] σ),
    φ t (funMap f x) = funMap f (x.map φ)
  /-- The maps preserve and reflect the relations. -/
  map_rel : ∀ (φ : F) {σ} (r : L.Relations σ) (x : M [^] σ), RelMap r (x.map φ) ↔ RelMap r x

section ToHom

variable {L F} {M : S → Type w} {N : S → Type w'} [L.Structure M] [L.Structure N]
  [DFunLike F S fun s => M s → N s]

/-- A `HomClass` consists of `L`-homomorphisms. -/
@[simps]
def HomClass.toHom [HomClass L F M N] : F → M →[L] N := fun φ => ⟨φ, map_fun φ, map_rel φ⟩

/-- A sortwise injective `StrongHomClass` consists of `L`-embeddings. Note that we need
  to require sortwise injectivity, since the definition of `StrongHomClass` does not assume
  that we reflect equality. This is in line with the one-sorted definition this is modeled after. -/
@[simps]
def StrongHomClass.toEmbedding' [StrongHomClass L F M N]
    (h : ∀ (φ : F) s, Function.Injective (φ s)) :
  F → M ↪[L] N := fun φ => ⟨fun s => ⟨φ s, h φ s⟩, map_fun φ, map_rel φ⟩

end ToHom

section Maps

variable {L} {M : S → Type w} {N : S → Type w'} [L.Structure M] [L.Structure N]

instance (priority := 100) StrongHomClass.homClass {F : Type*}
    [DFunLike F S fun s => M s → N s] [StrongHomClass L F M N] : HomClass L F M N where
  map_fun := StrongHomClass.map_fun
  map_rel φ _ r x := (StrongHomClass.map_rel φ r x).2

instance : HomClass L (M →[L] N) M N where
  map_fun φ := φ.map_fun'
  map_rel φ := φ.map_rel'

instance : StrongHomClass L (M ↪[L] N) M N where
  map_fun φ := φ.map_fun'
  map_rel φ := φ.map_rel'

instance : StrongHomClass L (M ≃[L] N) M N where
  map_fun φ := φ.map_fun'
  map_rel φ := φ.map_rel'

theorem Embedding.injective (φ : M ↪[L] N) (s : S) : Function.Injective (φ s) :=
  (φ.toEmbedding s).injective

theorem Equiv.injective (φ : M ≃[L] N) (s : S) : Function.Injective (φ s) :=
  (φ.toEquiv s).injective

theorem Equiv.surjective (φ : M ≃[L] N) (s : S) : Function.Surjective (φ s) :=
  (φ.toEquiv s).surjective

end Maps

end Language

end ManySorted
