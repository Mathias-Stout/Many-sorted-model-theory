/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Maps
public import MultisortedLogic.Parameters

/-!
# Elementary embeddings

An elementary embedding of `L`-structures is a family of maps that preserves and reflects every
formula.

## Main definitions

* `ElementaryEmbedding L M N` (`M ↪ₑ[L] N`), with `refl`, `comp`, `toEmbedding` and `toHom`.
* `Embedding.toElementaryEmbedding`, `Equiv.toElementaryEmbedding`.
* `ElementarilyEquivalent.symm`, `ElementarilyEquivalent.theory_model`,
  `ElementarilyEquivalent.nonempty_iff`: elementarily equivalent structures have the same models
  and the same nonempty sorts.
* `elementaryDiagram L N`: the sentences `φ(x)` with parameters from `N` that hold in `N`, for `φ`
  a positional `L`-formula.

## Main results

* `Embedding.isElementary_of_exists`: the Tarski–Vaught test.
* `ElementaryEmbedding.ofElementaryDiagram`, `ElementaryEmbedding.realize_elementaryDiagram`: the
  realizations of the elementary diagram of `N` are the elementary embeddings of `N`.

## Implementation notes

* Quantifiers bind blocks of variables, so the Tarski–Vaught test first passes from single
  elements to blocks (`Embedding.exists_map_of_exists`).
* Mathlib's elementary diagram is the complete `L[[N]]`-theory of `N`. The one here consists of the
  sentences `φ(x)` with `φ` an `L`-formula, which have the same models. Both directions of
  `ofElementaryDiagram` hold for it without translating constants back into variables.

## References

This file was originally based on `Mathlib/ModelTheory/ElementaryMaps.lean`, by Aaron Anderson.
-/

@[expose] public section

universe u v w w' w'' w''' z

namespace ManySorted.Language

open Arity Structure

variable {S : Type z}

variable (L : Language.{u, v} S) (M : S → Type w) (N : S → Type w') [L.Structure M]
  [L.Structure N]

/-- An elementary embedding: a family of maps that preserves and reflects every formula. -/
structure ElementaryEmbedding where
  /-- The underlying family of maps. -/
  toFun : ∀ s, M s → N s
  /-- The maps preserve and reflect every formula. -/
  map_formula' : ∀ {σ : Arity S} (φ : L.Formula σ) (xs : M [^] σ),
    φ.Realize (xs.map toFun) ↔ φ.Realize xs

@[inherit_doc] scoped[ManySorted] notation:25 A " ↪ₑ[" L "] " B =>
  ManySorted.Language.ElementaryEmbedding L A B

variable {L M N} {P : S → Type w''} {Q : S → Type w'''} [L.Structure P] [L.Structure Q]

namespace ElementaryEmbedding

instance : DFunLike (M ↪ₑ[L] N) S fun s => M s → N s where
  coe j := j.toFun
  coe_injective j k h := by cases j; cases k; cases h; rfl

@[simp]
theorem toFun_eq_coe (j : M ↪ₑ[L] N) : j.toFun = ⇑j :=
  rfl

@[ext]
theorem ext {j k : M ↪ₑ[L] N} (h : ∀ s x, j s x = k s x) : j = k :=
  DFunLike.coe_injective (funext fun s => funext (h s))

/-- Elementary embeddings preserve and reflect every formula. -/
@[simp]
theorem map_formula (j : M ↪ₑ[L] N) {σ : Arity S} (φ : L.Formula σ) (xs : M [^] σ) :
    φ.Realize (xs.map j) ↔ φ.Realize xs :=
  j.map_formula' φ xs

theorem map_sentence (j : M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  (j.map_formula φ PUnit.unit).symm

theorem theory_model_iff (j : M ↪ₑ[L] N) (T : L.Theory) : M ⊨ T ↔ N ⊨ T := by
  simp only [Theory.model_iff, j.map_sentence]

/-- An elementary extension of a model of `T` is a model of `T`. -/
theorem theory_model (j : M ↪ₑ[L] N) {T : L.Theory} [h : M ⊨ T] : N ⊨ T :=
  (j.theory_model_iff T).1 h

theorem elementarilyEquivalent (j : M ↪ₑ[L] N) : L.ElementarilyEquivalent M N :=
  elementarilyEquivalent_iff.2 j.map_sentence

/-- A family of maps that preserves every formula is an elementary embedding: reflection follows by
negation. -/
def ofMapFormula (g : ∀ s, M s → N s)
    (h : ∀ {σ : Arity S} (φ : L.Formula σ) (xs : M [^] σ), φ.Realize xs → φ.Realize (xs.map g)) :
    M ↪ₑ[L] N :=
  ⟨g, fun φ xs => ⟨fun h' => by_contra fun hn => h φ.not xs hn h', h φ xs⟩⟩

@[simp]
theorem coe_ofMapFormula (g : ∀ s, M s → N s)
    (h : ∀ {σ : Arity S} (φ : L.Formula σ) (xs : M [^] σ), φ.Realize xs → φ.Realize (xs.map g)) :
    ⇑(ofMapFormula g h) = g :=
  rfl

theorem injective (j : M ↪ₑ[L] N) (s : S) : Function.Injective (j s) := fun a b h =>
  (j.map_formula (.equal (.var (.left .var)) (.var (.right .var)))
    ((a, b) : M [^] (⦃s⦄ ⨯ ⦃s⦄))).1 h

theorem map_fun (j : M ↪ₑ[L] N) {σ : Arity S} {t : S} (f : L.Functions σ t) (x : M [^] σ) :
    j t (funMap f x) = funMap f (x.map j) := by
  have := (j.map_formula (.equal (.func f (Term.vars (Interpret.ofFn fun _ i => .left i)))
    (.var (.right .var))) ((x, funMap (M := M) f x) : M [^] (σ ⨯ ⦃t⦄))).2
    (by simp [Interpret.map_ofFn, Function.comp_def])
  simpa [Interpret.map_ofFn, Function.comp_def, -Interpret.get_map] using this.symm

theorem map_rel (j : M ↪ₑ[L] N) {σ : Arity S} (r : L.Relations σ) (x : M [^] σ) :
    RelMap r (x.map j) ↔ RelMap r x := by
  simpa [Interpret.map_ofFn, Function.comp_def, -Interpret.get_map, -map_formula] using
    j.map_formula (.rel r (Term.vars (Interpret.ofFn fun _ i => i))) x

instance : StrongHomClass L (M ↪ₑ[L] N) M N where
  map_fun := map_fun
  map_rel := map_rel

/-- An elementary embedding is an embedding. -/
def toEmbedding (j : M ↪ₑ[L] N) : M ↪[L] N where
  toEmbedding s := ⟨j s, j.injective s⟩
  map_fun' := j.map_fun
  map_rel' := j.map_rel

@[simp]
theorem coe_toEmbedding (j : M ↪ₑ[L] N) : ⇑j.toEmbedding = ⇑j :=
  rfl

/-- An elementary embedding is a homomorphism. -/
def toHom (j : M ↪ₑ[L] N) : M →[L] N :=
  j.toEmbedding.toHom

@[simp]
theorem coe_toHom (j : M ↪ₑ[L] N) : ⇑j.toHom = ⇑j :=
  rfl

theorem toEmbedding_toHom (j : M ↪ₑ[L] N) : j.toEmbedding.toHom = j.toHom :=
  rfl

variable (L M) in
/-- The identity is elementary. -/
def refl : M ↪ₑ[L] M where
  toFun _ a := a
  map_formula' _ xs := by rw [Interpret.map_id']

instance : Inhabited (M ↪ₑ[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply {s : S} (x : M s) : refl L M s x = x :=
  rfl

/-- The composition of elementary embeddings. -/
def comp (k : N ↪ₑ[L] P) (j : M ↪ₑ[L] N) : M ↪ₑ[L] P where
  toFun s := k s ∘ j s
  map_formula' φ xs := by rw [← Interpret.map_map, k.map_formula, j.map_formula]

@[simp]
theorem comp_apply (k : N ↪ₑ[L] P) (j : M ↪ₑ[L] N) {s : S} (x : M s) :
    k.comp j s x = k s (j s x) :=
  rfl

theorem comp_assoc (l : P ↪ₑ[L] Q) (k : N ↪ₑ[L] P) (j : M ↪ₑ[L] N) :
    (l.comp k).comp j = l.comp (k.comp j) :=
  rfl

end ElementaryEmbedding

/-! ### The Tarski–Vaught test -/

namespace Embedding

variable (f : M ↪[L] N)

/-- The Tarski–Vaught condition passes from single elements to blocks of variables: if every
formula with one variable over the image that has a witness in `N` has one in the image, the same
holds for formulas with a block of variables. -/
theorem exists_map_of_exists
    (htv : ∀ {σ : Arity S} {s : S} (φ : L.Formula (σ ⨯ ⦃s⦄)) (x : M [^] σ) (b : N s),
      φ.Realize ((x.map f, b) : N [^] (σ ⨯ ⦃s⦄)) →
        ∃ a : M s, φ.Realize ((x.map f, f s a) : N [^] (σ ⨯ ⦃s⦄))) :
    ∀ {τ σ : Arity S} (φ : L.Formula (σ ⨯ τ)) (x : M [^] σ) (ys : N [^] τ),
      φ.Realize ((x.map f, ys) : N [^] (σ ⨯ τ)) →
        ∃ zs : M [^] τ, φ.Realize ((x.map f, zs.map f) : N [^] (σ ⨯ τ))
  | .nil, _, _, _, _, h => ⟨PUnit.unit, h⟩
  | .of _, _, φ, x, ys, h => htv φ x ys h
  | .prod _ τ₂, _, φ, x, ys, h => by
    obtain ⟨zs₁, h₁⟩ := exists_map_of_exists htv (Formula.ex τ₂ (φ.relabel Idx.assoc)) x ys.1
      (Formula.realize_ex.2 ⟨ys.2, by simpa [Formula.realize_relabel] using h⟩)
    obtain ⟨y₂, h₂⟩ := Formula.realize_ex.1 h₁
    obtain ⟨zs₂, h₃⟩ := exists_map_of_exists htv (φ.relabel Idx.assoc) (x, zs₁) y₂ h₂
    exact ⟨(zs₁, zs₂), by simpa [Formula.realize_relabel] using h₃⟩

/-- **The Tarski–Vaught test**: an embedding is elementary if every formula with one variable over
the image that has a witness in `N` has one in the image. -/
theorem isElementary_of_exists
    (htv : ∀ {σ : Arity S} {s : S} (φ : L.Formula (σ ⨯ ⦃s⦄)) (x : M [^] σ) (b : N s),
      φ.Realize ((x.map f, b) : N [^] (σ ⨯ ⦃s⦄)) →
        ∃ a : M s, φ.Realize ((x.map f, f s a) : N [^] (σ ⨯ ⦃s⦄))) :
    ∀ {σ : Arity S} (φ : L.Formula σ) (x : M [^] σ), φ.Realize (x.map f) ↔ φ.Realize x
  | _, .falsum, _ => Iff.rfl
  | _, .equal t₁ t₂, x => StrongHomClass.realize_of_isAtomic f f.injective (.equal t₁ t₂) x
  | _, .rel R ts, x => StrongHomClass.realize_of_isAtomic f f.injective (.rel R ts) x
  | _, .imp φ ψ, x => by
    simp only [Formula.realize_imp, isElementary_of_exists htv φ x, isElementary_of_exists htv ψ x]
  | _, .all _ φ, x => by
    simp only [Formula.realize_all]
    refine ⟨fun h zs => (isElementary_of_exists htv φ (x, zs)).1 (h (zs.map f)),
      fun h ys => by_contra fun hn => ?_⟩
    obtain ⟨zs, hzs⟩ := f.exists_map_of_exists htv φ.not x ys hn
    exact hzs ((isElementary_of_exists htv φ (x, zs)).2 (h zs))

/-- An embedding that passes the Tarski–Vaught test, as an elementary embedding. -/
def toElementaryEmbedding
    (htv : ∀ {σ : Arity S} {s : S} (φ : L.Formula (σ ⨯ ⦃s⦄)) (x : M [^] σ) (b : N s),
      φ.Realize ((x.map f, b) : N [^] (σ ⨯ ⦃s⦄)) →
        ∃ a : M s, φ.Realize ((x.map f, f s a) : N [^] (σ ⨯ ⦃s⦄))) :
    M ↪ₑ[L] N :=
  ⟨f, f.isElementary_of_exists htv⟩

@[simp]
theorem coe_toElementaryEmbedding
    (htv : ∀ {σ : Arity S} {s : S} (φ : L.Formula (σ ⨯ ⦃s⦄)) (x : M [^] σ) (b : N s),
      φ.Realize ((x.map f, b) : N [^] (σ ⨯ ⦃s⦄)) →
        ∃ a : M s, φ.Realize ((x.map f, f s a) : N [^] (σ ⨯ ⦃s⦄))) :
    ⇑(f.toElementaryEmbedding htv) = ⇑f :=
  rfl

end Embedding

namespace Equiv

/-- An isomorphism is an elementary embedding. -/
def toElementaryEmbedding (f : M ≃[L] N) : M ↪ₑ[L] N :=
  ⟨f, f.realize_formula⟩

@[simp]
theorem coe_toElementaryEmbedding (f : M ≃[L] N) : ⇑f.toElementaryEmbedding = ⇑f :=
  rfl

theorem toElementaryEmbedding_toEmbedding (f : M ≃[L] N) :
    f.toElementaryEmbedding.toEmbedding = f.toEmbedding :=
  rfl

end Equiv

/-! ### The elementary diagram -/

variable (L N) in
/-- The elementary diagram of `N`: the sentences `φ(x)` with parameters from `N` such that
`N ⊨ φ(x)`, for `φ` a positional `L`-formula and `x` a tuple of `N`. -/
def elementaryDiagram : L[[N]].Theory :=
  {ψ | ∃ (τ : Arity S) (φ : L.Formula τ) (x : N [^] τ), φ.Realize x ∧ ψ = φ.ofNames x.get}

namespace ElementaryEmbedding

/-- A family of maps realizing the elementary diagram of `N` is an elementary embedding. -/
def ofElementaryDiagram {v : ∀ s, N s → P s}
    (h : (elementaryDiagram L N).RealizeWith v PUnit.unit) : N ↪ₑ[L] P :=
  ofMapFormula v fun φ xs hφ => by
    have := (Formula.realize_ofNames v φ xs.get).1 (h _ ⟨_, φ, xs, hφ, rfl⟩)
    convert this using 1
    exact Interpret.ext fun s i => by simp [Interpret.get_map, Interpret.get_ofFn]

@[simp]
theorem coe_ofElementaryDiagram {v : ∀ s, N s → P s}
    (h : (elementaryDiagram L N).RealizeWith v PUnit.unit) : ⇑(ofElementaryDiagram h) = v :=
  rfl

/-- An elementary embedding realizes the elementary diagram of its domain. -/
theorem realize_elementaryDiagram (j : N ↪ₑ[L] P) :
    (elementaryDiagram L N).RealizeWith j PUnit.unit := by
  rintro _ ⟨τ, φ, x, hφ, rfl⟩
  refine (Formula.realize_ofNames _ φ x.get).2 ?_
  convert (j.map_formula φ x).2 hφ using 1
  exact Interpret.ext fun s i => by simp [Interpret.get_map, Interpret.get_ofFn]

end ElementaryEmbedding

/-! ### Elementary equivalence -/

namespace ElementarilyEquivalent

theorem symm (h : L.ElementarilyEquivalent M N) : L.ElementarilyEquivalent N M :=
  Eq.symm h

theorem realize_sentence (h : L.ElementarilyEquivalent M N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  elementarilyEquivalent_iff.1 h φ

theorem theory_model_iff (h : L.ElementarilyEquivalent M N) (T : L.Theory) : M ⊨ T ↔ N ⊨ T := by
  simp only [Theory.model_iff, h.realize_sentence]

theorem theory_model (h : L.ElementarilyEquivalent M N) {T : L.Theory} [M ⊨ T] : N ⊨ T :=
  (h.theory_model_iff T).1 inferInstance

end ElementarilyEquivalent

variable (L M) in
/-- A sort is nonempty exactly when the structure satisfies `∃ x : s, ⊤`. -/
theorem nonempty_iff_realize_ex_top (s : S) :
    Nonempty (M s) ↔ M ⊨ (∃' s (⊤ : L.Formula (⦃⦄ ⨯ ⦃s⦄))) := by
  simp [Formula.realize_ex, Formula.realize_top]

/-- Elementarily equivalent structures have the same nonempty sorts. -/
theorem ElementarilyEquivalent.nonempty_iff (h : L.ElementarilyEquivalent M N) (s : S) :
    Nonempty (M s) ↔ Nonempty (N s) := by
  rw [nonempty_iff_realize_ex_top L M, nonempty_iff_realize_ex_top L N]
  exact elementarilyEquivalent_iff.1 h _

end ManySorted.Language
