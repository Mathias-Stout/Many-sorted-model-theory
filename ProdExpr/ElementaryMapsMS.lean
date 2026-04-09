/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Init
import Mathlib.Data.Fintype.Basic
import ProdExpr.SubstructureMS
import ProdExpr.SemanticTactics

/-!
# Elementary Maps Between Multi-Sorted First-Order Structures

This file defines elementary embeddings for multi-sorted first-order logic,
generalizing the one-sorted case from `ElementaryMaps.lean`.

## Main Definitions

- A `MSFirstOrder.MSLanguage.ElementaryEmbedding` is an embedding that commutes with the
  realizations of formulas.
- The `MSFirstOrder.MSLanguage.elementaryDiagram` of a structure is the set of all sentences with
  parameters that the structure satisfies.
- `MSFirstOrder.MSLanguage.ElementaryEmbedding.ofModelsElementaryDiagram` is the canonical
  elementary embedding of any structure into a model of its elementary diagram.

## Main Results

- The Tarski-Vaught Test for embeddings: `MSFirstOrder.MSLanguage.Embedding.isElementary_of_exists`
  gives a simple criterion for an embedding to be elementary.
-/

universe u u' v w w' z

namespace MSFirstOrder

namespace MSLanguage

open MSStructure Signature Interpret

variable {Sorts : Type z} (L : MSLanguage.{u, v, z} Sorts)
variable (M : Fam.{w} Sorts) (N : Fam.{w'} Sorts) {P : Fam Sorts}{ Q : Fam Sorts}
variable [L.MSStructure M] [L.MSStructure N] [L.MSStructure P] [L.MSStructure Q]

/-- An elementary embedding of multi-sorted first-order structures is an embedding that commutes
  with the realizations of formulas. -/
structure ElementaryEmbedding where
  /-- The underlying sorted family map -/
  toFun : M →ₛ N
  /-- The embedding preserves formula realization -/
  map_boundedFormula' :
    ∀ {σ : Signature Sorts} (φ : L.BoundedFormula Fam.EmptyFam σ) (x : M [^] σ),
      φ.Realize default (toFun <$>ₛ x) ↔ φ.Realize default x := by
    aesop

@[inherit_doc MSFirstOrder.MSLanguage.ElementaryEmbedding]
scoped[MSFirstOrder] notation:25 A " ↪ₑ[" L "] " B =>
  MSFirstOrder.MSLanguage.ElementaryEmbedding L A B

variable {L} {M} {N}

namespace ElementaryEmbedding

instance instFamMapClass : Fam.FamMapClass (M ↪ₑ[L] N) M N where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have hfg : f = g := by
      ext s x
      exact congrFun (congrArg (fun φ => φ s) h) x
    cases hfg
    have hh :
        (hf :
          ∀ {σ : Signature Sorts} (φ : L.BoundedFormula Fam.EmptyFam σ) (x : M [^] σ),
            φ.Realize default (f <$>ₛ x) ↔ φ.Realize default x) =
        (hg :
          ∀ {σ : Signature Sorts} (φ : L.BoundedFormula Fam.EmptyFam σ) (x : M [^] σ),
            φ.Realize default (f <$>ₛ x) ↔ φ.Realize default x) := by
      exact Subsingleton.elim _ _
    cases hh
    rfl

open Formula BoundedFormula

@[simp]
theorem map_formula {α} (f : M ↪ₑ[L] N)
    (φ : L.Formula α) (x : α →ₛ M) :
    Realize φ ((f: M →ₛ N) ∘ₛ x) ↔ Realize φ x := by
  classical
  letI : DecidableEq Sorts := Classical.typeDecidableEq _
  letI : ∀ s, DecidableEq (α s) := fun s => Classical.typeDecidableEq _
  let φ_loc := φ.localize
  rw[φ_loc.realize_toBoundedFormula x, φ_loc.realize_toBoundedFormula ((f: M →ₛ N) ∘ₛ x)]
  have hmap : φ_loc.toTuple N (f ∘ₛ x) = f <$>ₛ (φ_loc.toTuple M x) := by
    apply Interpret.ext'
    intro s v
    rename_i this_1
    simp_all only [LocalForm.get_toTuple, mapClass_eq_map, this_1, this, φ_loc]
    change (φ.localize.comap N (↑f ∘ₛ x)) s v = ((↑f) <$>ₛ (φ.localize.toTuple M x)).get s v
    rw[get_map]
    simp_all only [LocalForm.get_toTuple, Fam.FamMap.comp_apply', this_1, this]
    rfl
  rw [hmap]
  simpa using f.map_boundedFormula' φ_loc.toBoundedFormula (φ_loc.toTuple M x)

@[simp]
theorem map_boundedFormula {α} (f : M ↪ₑ[L] N) {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ) (v : α →ₛ M) (xs : M [^] σ) :
    φ.Realize (f ∘ₛ v) (f <$>ₛ xs) ↔ φ.Realize v xs := by
  classical
  let φ' : L.BoundedFormula α (Signature.nil ⨯ σ) :=
    φ.reindex (SigEquiv.nilLeft σ).symm
  let ψ : L.BoundedFormula (α ⊕ₛ σ.IdxFam) nil := φ'.openVars
  have hM :
       ψ.Realize (Fam.sumElim v xs.get) default ↔ φ.Realize v xs := by
    unfold ψ φ'; rw[realize_openVars]
    simp only [PUnit.default_eq_unit, reduce_nil, realize_reindex, comap, SigEquiv.nilLeft,
      reduce_nil, SigEquiv.symm]
    congr!
    refine Interpret.ext' (fun s w ↦ ?_)
    simp_all only [reduce_nil, fromGet_get]; rfl
  have hN :
      ψ.Realize (Fam.sumElim (f ∘ₛ v) (f <$>ₛ xs).get) default ↔ φ.Realize (f ∘ₛ v) (f <$>ₛ xs) :=
    by
    unfold ψ φ'; rw[realize_openVars]
    simp only [PUnit.default_eq_unit, reduce_nil, realize_reindex, comap, SigEquiv.nilLeft,
      reduce_nil, SigEquiv.symm]
    congr!
    refine Interpret.ext' (fun s w ↦ ?_)
    simp_all only [reduce_nil, fromGet_get]; rfl
  have hmap :
      ψ.Realize (Fam.sumElim (f ∘ₛ v) (f <$>ₛ xs).get) default ↔
        ψ.Realize (Fam.sumElim v xs.get) default := by
    simpa only [get_map, PUnit.default_eq_unit, reduce_nil, Fam.sumComp_elim] using
      f.map_formula ψ (Fam.sumElim v xs.get)
  rw[← hN, ←hM, hmap]


theorem map_sentence (f : M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  have h := f.map_formula φ default
  simp only [Sentence.Realize] at h ⊢
  have hf : ((f : M →ₛ N) ∘ₛ (default : Fam.EmptyFam →ₛ M)) = default := by
    ext s v; cases v
  rw[hf] at h
  exact h.symm

theorem theory_model_iff (f : M ↪ₑ[L] N) (T : L.Theory) : M ⊨ T ↔ N ⊨ T := by
  simp only [Theory.model_iff, f.map_sentence]

theorem elementarilyEquivalent (f : M ↪ₑ[L] N) : M ≅[L] N :=
  elementarilyEquivalent_iff.2 f.map_sentence

/-- An elementary embedding is injective in each sort. -/
@[simp]
theorem injective (f : M ↪ₑ[L] N) (s : Sorts) : Function.Injective (f s) := by
  intro x y hxy
  -- Use the formula asserting equality of two variables of sort s
  -- The signature (of s) ⨯ (of s) has two variables of sort s
  let σ : Signature Sorts := (of s) ⨯ (of s)
  let t₁ : L.Term₁ σ.IdxFam s := Term.var s (.left .var)
  let t₂ : L.Term₁ σ.IdxFam s := Term.var s (.right .var)
  let φ : L.Formula σ.IdxFam := t₁.equal t₂
  -- Define valuation using Interpret and fromGet
  let xs : M [^] σ := ⟨x, y⟩
  -- Convert to a valuation on Idx
  let v : σ.IdxFam →ₛ M := xs.get
  have hRealize : φ.Realize v ↔ x = y := by
    unfold φ t₁ t₂ v xs
    simp_all only [realize_equal, Term.realize_var, get_left, get_of, get_right, σ]
  have hRealize' : φ.Realize ((f : M →ₛ N) ∘ₛ v) ↔ f s x = f s y := by
    unfold φ t₁ t₂ v xs
    simp_all only [realize_equal, Term.realize_var, get_left, get_of, get_right,
      Fam.FamMap.comp_apply', iff_true, σ, φ, t₁, t₂, v, xs]
    obtain ⟨fst, snd⟩ := xs
    exact hxy
  rw [← hRealize, ← f.map_formula φ v, hRealize']
  exact hxy

/-- An elementary embedding is injective per sort as a family. -/
instance : Fam.InjectivePerSort (M ↪ₑ[L] N) M N where
  inj' f s := f.injective s

/-- An elementary embedding preserves function symbols. -/
theorem map_fun (f : M ↪ₑ[L] N) {σ : Signature Sorts} {t : Sorts}
    (fn : L.Functions σ t) (x : M [^] σ) :
    f t (funMap fn x) = funMap fn (f <$>ₛ x) := by
  change (Fam.FamMapClass.toFamMap f) t (funMap fn x) = funMap fn (f <$>ₛ x)
  let φ : L.Formula (σ ⨯ ⦃t⦄).IdxFam := Formula.graph fn
  let v : (σ ⨯ ⦃t⦄).IdxFam →ₛ M := ⟨fun s' i =>
    match i with
    | .left i' => x.get s' i'
    | .right .var => funMap fn x⟩
  have hvArgs : fromGet ⟨fun s i => v s (.left i)⟩ = x := by
    refine Interpret.ext' (fun s w ↦ ?_)
    simp [v, fromGet_get]
  have hv : φ.Realize v := by
    have : v t (.right .var) = funMap fn (fromGet ⟨fun s i => v s (.left i)⟩) := by
      simpa [v] using congrArg (fun y => funMap fn y) hvArgs.symm
    simpa only [φ, Formula.realize_graph] using this
  have hN : φ.Realize ((f : M →ₛ N) ∘ₛ v) := (f.map_formula φ v).2 hv
  have hN' :
      ((f : M →ₛ N) ∘ₛ v) t (.right .var) =
        funMap fn (fromGet ⟨fun s i => ((f : M →ₛ N) ∘ₛ v) s (.left i)⟩) := by
    simpa only [φ, Formula.realize_graph] using hN
  calc
    (Fam.FamMapClass.toFamMap f) t (funMap fn x) = ((f : M →ₛ N) ∘ₛ v) t (.right .var) := by
      simp [Fam.FamMap.comp_apply', v]
    _ = funMap fn (fromGet ⟨fun s i => ((f : M →ₛ N) ∘ₛ v) s (.left i)⟩) := hN'
    _ = funMap fn (f <$>ₛ x) := by
      congr 1
      refine Interpret.ext' (fun s w ↦ ?_)
      simp only [Fam.FamMap.comp_apply', Fam.FamMap.mk_apply, fromGet_get, get_map, v]

/-- An elementary embedding preserves and reflects relation symbols. -/
theorem map_rel (f : M ↪ₑ[L] N) {σ : Signature Sorts}
    (r : L.Relations σ) (x : M [^] σ) :
    RelMap r (f <$>ₛ x) ↔ RelMap r x := by
  let φ : L.Formula σ.IdxFam := r.formula (Term.varTerm σ)
  have hFromGet : fromGet x.get = x := by
    apply Interpret.ext'
    intro s i
    simp only [fromGet_get]
  have hMapGet :
      fromGet ((f : M →ₛ N) ∘ₛ x.get) = (f <$>ₛ x) := by
    apply Interpret.ext'
    intro s i
    have hget : (f <$>ₛ x).get s i = f s (x.get s i) := by
      simp_all only [get_fromGet, get_map, Fam.FamMap.comp_apply']
      rfl
    calc
      (fromGet ((f : M →ₛ N) ∘ₛ x.get)).get s i = ((f : M →ₛ N) ∘ₛ x.get) s i := by
        simp only [fromGet_get]
      _ = f s (x.get s i) := rfl
      _ = (f <$>ₛ x).get s i := by simpa using hget.symm
  have hM : φ.Realize x.get ↔ RelMap r x := by
    calc
      φ.Realize x.get ↔ RelMap r (Term.realize x.get (Term.varTerm σ)) := by
        simpa only [φ] using
          (realize_rel (L := L) (M := M) (R := r) (ts := Term.varTerm σ) (v := x.get))
      _ ↔ RelMap r (fromGet x.get) := by
        simp only [Term.realize_varterm]
      _ ↔ RelMap r x := by simp_all only [get_fromGet]
  have hN : φ.Realize ((f : M →ₛ N) ∘ₛ x.get) ↔ RelMap r (f <$>ₛ x) := by
    calc
      φ.Realize ((f : M →ₛ N) ∘ₛ x.get) ↔
      RelMap r (Term.realize ((f : M →ₛ N) ∘ₛ x.get) (Term.varTerm σ)) := by
        simpa only [φ] using
          (realize_rel (L := L) (M := N) (R := r) (ts := Term.varTerm σ)
            (v := ((f : M →ₛ N) ∘ₛ x.get)))
      _ ↔ RelMap r (fromGet ((f : M →ₛ N) ∘ₛ x.get)) := by
        simp only [Term.realize_varterm]
      _ ↔ RelMap r (f <$>ₛ x) := by simp_all only [get_fromGet, Formula.realize_rel,
          Term.realize_varterm, φ]
  exact hN.symm.trans ((f.map_formula φ x.get).trans hM)

instance strongHomClass : StrongHomClass L (M ↪ₑ[L] N) M N where
  toFamMapClass := inferInstance
  map_fun := map_fun
  map_rel := map_rel

theorem map_constants (f : M ↪ₑ[L] N) {s : Sorts} (c : L.Constants s) : f s c = c :=
  HomClass.map_constants f c

/-- An elementary embedding is also a first-order embedding. -/
def toEmbedding (f : M ↪ₑ[L] N) : M ↪[L] N where
  toFun := f.toFun
  inj' s := f.injective s
  map_fun' fn x := f.map_fun fn x
  map_rel' r x := f.map_rel r x

/-- An elementary embedding is also a first-order homomorphism. -/
def toHom (f : M ↪ₑ[L] N) : M →[L] N where
  toFun := f.toFun
  map_fun' fn x := f.map_fun fn x
  map_rel' r x h := (f.map_rel r x).2 h

@[simp]
theorem toEmbedding_toHom (f : M ↪ₑ[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
theorem coe_toHom {f : M ↪ₑ[L] N} : (f.toHom : ∀ s, M s → N s) = (f : ∀ s, M s → N s) :=
  rfl

@[simp]
theorem coe_toEmbedding (f : M ↪ₑ[L] N) : (f.toEmbedding : ∀ s, M s → N s) = (f : ∀ s, M s → N s) :=
  rfl

theorem coe_injective : @Function.Injective (M ↪ₑ[L] N) (∀ s, M s → N s) (↑) :=
  DFunLike.coe_injective

@[ext]
theorem ext ⦃f g : M ↪ₑ[L] N⦄ (h : ∀ s x, f s x = g s x) : f = g :=
  DFunLike.ext f g (fun s => funext (h s))

variable (L) (M)

/-- The identity elementary embedding from a structure to itself -/
@[refl]
def refl : M ↪ₑ[L] M where
  toFun := Fam.FamMap.idₛ
  map_boundedFormula' := fun φ x => by simp only [map_id]

variable {L} {M}

instance : Inhabited (M ↪ₑ[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (s : Sorts) (x : M s) : refl L M s x = x :=
  rfl

/-- Composition of elementary embeddings -/
@[trans]
def comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P where
  toFun := hnp.toFun ∘ₛ hmn.toFun
  map_boundedFormula' φ x := by
    rw [comp_map, hnp.map_boundedFormula', hmn.map_boundedFormula']

@[simp]
theorem comp_apply (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (s : Sorts) (x : M s) :
    g.comp f s x = g s (f s x) :=
  rfl

/-- Composition of elementary embeddings is associative. -/
theorem comp_assoc (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

end ElementaryEmbedding


lemma sumElim_comp_get
  {σ : Signature Sorts} (f : M ↪[L] N) (xs : M [^] σ) :
    Fam.sumElim (default : Fam.EmptyFam →ₛ N) (fun s => f s ∘ xs.get s) =
      f ∘ₛ (Fam.sumElim (default : Fam.EmptyFam →ₛ M) xs.get) := by
  ext s i
  cases i with
  | inl e => cases e
  | inr j => rfl

@[simp]
lemma get_map_apply {σ : Signature Sorts} (f : M ↪[L] N) (xs : M [^] σ) (s : Sorts) (i : σ.Idx s) :
    (f <$>ₛ xs).get s i = f s (xs.get s i) := by
  simp_all only [get_map, Fam.FamMap.comp_apply']
  rfl

@[simp]
lemma comap_assocR
  {X : Fam Sorts} {σ τ η : Signature Sorts} (xs : X [^] ((σ ⨯ τ) ⨯ η)) :
    Signature.Interpret.comap (Signature.SigMap.assocR (S := Sorts) σ τ η) xs =
      (⟨xs.1.1, ⟨xs.1.2, xs.2⟩⟩ : X[^](σ ⨯ (τ ⨯ η))) := by
  let fAssoc := Signature.SigMap.assocR (S := Sorts) σ τ η
  apply Prod.ext
  · apply Interpret.ext'
    intro s iσ
    have hget := congrArg
      (fun g => g s (Signature.Idx.left iσ))
      (Signature.get_comap (xs := xs) (f := fAssoc))
    have hleft :
        (Signature.Interpret.comap fAssoc xs).1.get s iσ =
          (Signature.Interpret.comap fAssoc xs).get s (Signature.Idx.left iσ) := by
      simpa using
        (get_left (xs := (Signature.Interpret.comap fAssoc xs)) (v := iσ)).symm
    calc
      (Signature.Interpret.comap fAssoc xs).1.get s iσ
          = (Signature.Interpret.comap fAssoc xs).get s (Signature.Idx.left iσ) := hleft
      _ = xs.get s (fAssoc s (Signature.Idx.left iσ)) := hget
      _ = xs.get s (Signature.Idx.left (Signature.Idx.left iσ)) := by
            simp [fAssoc, SigMap.assocR]
      _ = xs.1.1.get s iσ := by
            simp [get_left]
  · apply Prod.ext
    · apply Interpret.ext'
      intro s iτ
      have hget := congrArg
        (fun g => g s (Signature.Idx.right (Signature.Idx.left iτ)))
        (Signature.get_comap (xs := xs) (f := fAssoc))
      have hleft :
          (Signature.Interpret.comap fAssoc xs).2.1.get s iτ =
            (Signature.Interpret.comap fAssoc xs).2.get s (Signature.Idx.left iτ) := by
        simpa only using (get_left (xs := (Signature.Interpret.comap fAssoc xs).2) (v := iτ)).symm
      have hright :
          (Signature.Interpret.comap fAssoc xs).2.get s (Signature.Idx.left iτ) =
          (Signature.Interpret.comap fAssoc xs).get s
          (Signature.Idx.right (Signature.Idx.left iτ)) := by
        simpa using
          (get_right (xs := (Signature.Interpret.comap fAssoc xs))
            (v := (Signature.Idx.left iτ))).symm
      calc
        (Signature.Interpret.comap fAssoc xs).2.1.get s iτ
            = (Signature.Interpret.comap fAssoc xs).2.get s (Signature.Idx.left iτ) := hleft
        _ = (Signature.Interpret.comap fAssoc xs).get s
            (Signature.Idx.right (Signature.Idx.left iτ)) := hright
        _ = xs.get s (fAssoc s (Signature.Idx.right (Signature.Idx.left iτ))) := hget
        _ = xs.get s (Signature.Idx.left (Signature.Idx.right iτ)) := by
              simp [fAssoc, SigMap.assocR]
        _ = xs.1.2.get s iτ := by
              simp [get_left, get_right]
    · apply Interpret.ext'
      intro s iη
      have hget := congrArg
        (fun g => g s (Signature.Idx.right (Signature.Idx.right iη)))
        (Signature.get_comap (xs := xs) (f := fAssoc))
      have hright₁ :
          (Signature.Interpret.comap fAssoc xs).2.2.get s iη =
            (Signature.Interpret.comap fAssoc xs).2.get s (Signature.Idx.right iη) := by
        simpa only using (get_right (xs := (Signature.Interpret.comap fAssoc xs).2) (v := iη)).symm
      have hright₂ :
          (Signature.Interpret.comap fAssoc xs).2.get s (Signature.Idx.right iη) =
            (Signature.Interpret.comap fAssoc xs).get s
            (Signature.Idx.right (Signature.Idx.right iη)) := by
        simpa using
          (get_right (xs := (Signature.Interpret.comap fAssoc xs))
            (v := (Signature.Idx.right iη))).symm
      calc
        (Signature.Interpret.comap fAssoc xs).2.2.get s iη
            = (Signature.Interpret.comap fAssoc xs).2.get s (Signature.Idx.right iη) := hright₁
        _ = (Signature.Interpret.comap fAssoc xs).get s
            (Signature.Idx.right (Signature.Idx.right iη)) := hright₂
        _ = xs.get s (fAssoc s (Signature.Idx.right (Signature.Idx.right iη))) := hget
        _ = xs.get s (Signature.Idx.right iη) := by
              simp [fAssoc, SigMap.assocR]
        _ = xs.2.get s iη := by
              simp [get_right]

variable (L) (M)

/-- The elementary diagram of an `L`-structure is the set of all sentences with parameters it
  satisfies. -/
abbrev elementaryDiagram : L[[M]].Theory :=
  L[[M]].completeTheory M

variable {L} {M}

def ElementaryEmbedding.ofModelsElementaryDiagram (N : Fam Sorts) [L.MSStructure N]
    [L[[M]].MSStructure N] [(lhomWithConstants L M).IsExpansionOn N] [N ⊨ L.elementaryDiagram M] :
    M ↪ₑ[L] N :=
  let constantsInr : M →ₛ (⟨fun s => L[[M]].Constants s⟩ : Fam Sorts) :=
    ⟨fun s (x : M s) => (Sum.inr x : L[[M]].Constants s)⟩
  let evalConst : (⟨fun s => L[[M]].Constants s⟩ : Fam Sorts) →ₛ N :=
    ⟨fun s c => (L[[M]].constantMap (M := N) (t := s) c)⟩
  ⟨evalConst ∘ₛ constantsInr, fun {σ : Signature Sorts} φ x => by
  --Term consisting of a tuple of constants representing x:
  let t : L[[M]].Term (Fam.EmptyFam ⊕ₛ Signature.nil.IdxFam) σ :=
    (Term.varTerm σ).bind
      (⟨fun s v => Constants.term (Sum.inr (x.get s v))⟩ :
        σ.IdxFam →ₛ L[[M]].Term₁ (Fam.EmptyFam ⊕ₛ Signature.nil.IdxFam))
  let φ' := ((L.lhomWithConstants M).onBoundedFormula φ).fully_instantiate t
  refine
      _root_.trans ?_
        ((realize_iff_of_model_completeTheory M N φ').trans
          ?_)
  · simp only [Sentence.Realize, BoundedFormula.realize_fully_instantiate, PUnit.default_eq_unit,
    reduce_nil, varFreeAssign_eq_default, LHom.realize_onBoundedFormula, φ']
    congr!
    simp_all only [Theory.model_iff, mem_completeTheory, constantsOn_Functions,
      constantsOnFunc.eq_1, Term.realize_bind,  Term.realize_varterm, t]
    refine Interpret.ext' (fun s w ↦ ?_)
    simp_all only [constantsOn_Functions, constantsOnFunc.eq_1, get_map, Fam.FamMap.comp_apply',
      Fam.FamMap.mk_apply, Term.realize_constants, fromGet_get, Fam.coeFun_apply, evalConst,
      constantsInr]
    rfl
  · simp only [Sentence.Realize, BoundedFormula.realize_fully_instantiate, PUnit.default_eq_unit,
    reduce_nil, varFreeAssign_eq_default, LHom.realize_onBoundedFormula, φ']
    congr!
    simp_all only [Theory.model_iff, mem_completeTheory, constantsOn_Functions,
      constantsOnFunc.eq_1, Term.realize_bind, Term.realize_varterm, t]
    refine Interpret.ext' (fun s w ↦ ?_)
    simp_all only [fromGet_get]
    rfl
  ⟩

namespace Embedding

/-- If `f` is injective on each sort, then mapping a tuple by `f` is injective. -/
theorem map_tuple_injective
  (f : M ↪[L] N)
  {σ : Signature Sorts} :
  Function.Injective (fun xs : M [^] σ => f <$>ₛ xs) := by
  intro xs ys h
  -- ext on tuples, reduce to ext on `get`
  apply Interpret.ext'
  intro s i
  -- compare components after applying `f`
  have : f s (xs.get s i) = f s (ys.get s i) := by
    -- use `h : f <$>ₛ xs = f <$>ₛ ys`
    -- and then read off the `get` component
    -- (this line is the only place you might need to tweak simp-lemmas)
    simpa only [at_eq_iff, get_map_apply] using congrArg (fun t => t.get s i) h
  exact f.injective s this

theorem map_term_realize {σ}
  {f : M ↪[L] N}
  {α : Fam Sorts}
  {t : L.Term α σ}
  {v : α →ₛ M} :
  (t.realize v).map f = t.realize ((f : M →ₛ N) ∘ₛ v) := by
  simpa only using (HomClass.realize_term (g := (f : M ↪[L] N)) (v := v) (t := t)).symm

/-- The **Tarski-Vaught test** for elementarity of an embedding.
    For a multi-sorted language, we need to check the existential condition for each sort.
    The proof is slightly complicated by the fact that out induction works at the block level,
    but the test looks at existential quantifiers over a single `of s` factor. This means that the
    `all` case of the induction goes through by contrapositive, but only after proving a
    strenghtened version of the hypothesis `htv` where the existentially quantified component is
    an arbitrary signature.
-/
theorem isElementary_of_exists
  (f : M ↪[L] N)
  (htv :
    ∀ (s : Sorts) (σ : Signature Sorts)
      (φ : L.BoundedFormula Fam.EmptyFam (σ.prod (.of s)))
      (xs : M [^] σ) (a : N s),
        φ.Realize default ⟨f <$>ₛ xs, a⟩ →
          ∃ b : M s, φ.Realize default ⟨f <$>ₛ xs, f s b⟩) :
  ∀ {σ : Signature Sorts} (φ : L.BoundedFormula Fam.EmptyFam σ) (xs : M [^] σ),
             φ.Realize default (f <$>ₛ xs) ↔ φ.Realize default xs :=
by
  classical
  intro σ φ xs
  induction φ with
  | falsum =>
      simp only [BoundedFormula.Realize]
  | @equal τ σ' t₁ t₂ =>

      let vM : (Fam.EmptyFam ⊕ₛ τ.IdxFam) →ₛ M :=
        Fam.sumElim default xs.get
      let vF : (Fam.EmptyFam ⊕ₛ τ.IdxFam) →ₛ N :=
        Fam.sumElim default (f <$>ₛ xs).get
      let vN : (Fam.EmptyFam ⊕ₛ τ.IdxFam) →ₛ N :=
        Fam.sumElim default (fun s ↦ f s ∘ xs.get s)

      have hv : vF = vN := by
        ext s i
        cases i with
        | inl e => cases e
        | inr j =>
            simp_all only [get_map, Fam.sumElim_eval_r, Fam.FamMap.comp_apply', Fam.coeFun_apply,
              Function.comp_apply, vF, vN]
            rfl
      have hv' : vN = (f : M →ₛ N) ∘ₛ vM := by
        ext s i
        cases i with
        | inl e => cases e
        | inr j =>
            rfl

      have hreal (u : L.Term (Fam.EmptyFam ⊕ₛ τ.IdxFam) σ') :
          Term.realize vN u = (f : M ↪[L] N) <$>ₛ Term.realize vM u := by
        calc
          Term.realize vN u = Term.realize ((f : M →ₛ N) ∘ₛ vM) u := by simp only [hv',
            HomClass.realize_term]
          _ = (f : M ↪[L] N) <$>ₛ Term.realize vM u := by
            simp only [(HomClass.realize_term (g := (f : M ↪[L] N)) (t := u) (v := vM))]

      rw [BoundedFormula.Realize, BoundedFormula.Realize]
      constructor
      · intro h
        have hN : Term.realize vN t₁ = Term.realize vN t₂ := by
          simpa only [get_map] using h
        have hmap :
            (f : M ↪[L] N) <$>ₛ Term.realize vM t₁ =
              (f : M ↪[L] N) <$>ₛ Term.realize vM t₂ := by
          simpa [hreal t₁, hreal t₂] using hN
        exact (map_tuple_injective (L := L) (M := M) (N := N) f (σ := σ')) hmap
      · intro h
        have hmap :
            (f : M ↪[L] N) <$>ₛ Term.realize vM t₁ =
              (f : M ↪[L] N) <$>ₛ Term.realize vM t₂ := by
          simpa using congrArg (fun x => (f : M ↪[L] N) <$>ₛ x) h
        have hN : Term.realize vN t₁ = Term.realize vN t₂ := by
          simpa [hreal t₁, hreal t₂] using hmap
        simpa only [vF, hv] using hN
  | @rel τ σ' R ts =>
      -- `rel` reduces to a `RelMap` statement on the realized tuple of terms.
      let vM : (Fam.EmptyFam ⊕ₛ τ.IdxFam) →ₛ M :=
        Fam.sumElim default xs.get
      let vF : (Fam.EmptyFam ⊕ₛ τ.IdxFam) →ₛ N :=
        Fam.sumElim default (f <$>ₛ xs).get
      let vN : (Fam.EmptyFam ⊕ₛ τ.IdxFam) →ₛ N :=
        Fam.sumElim default (fun s ↦ f s ∘ xs.get s)

      have hv : vF = vN := by
        ext s i
        cases i with
        | inl e => cases e
        | inr j =>
            simp_all only [get_map, Fam.sumElim_eval_r, Fam.FamMap.comp_apply', Fam.coeFun_apply,
              Function.comp_apply, vF, vN]
            rfl
      have hv' : vN = (f : M →ₛ N) ∘ₛ vM := by
        ext s i
        cases i with
        | inl e => cases e
        | inr j =>
            rfl

      have hts : Term.realize vN ts = (f : M ↪[L] N) <$>ₛ Term.realize vM ts := by
        calc
          Term.realize vN ts = Term.realize ((f : M →ₛ N) ∘ₛ vM) ts := by simp only [hv',
            HomClass.realize_term]
          _ = (f : M ↪[L] N) <$>ₛ Term.realize vM ts := by
            simp only [(HomClass.realize_term (g := (f : M ↪[L] N)) (t := ts) (v := vM))]

      rw [BoundedFormula.Realize, BoundedFormula.Realize]
      calc
        RelMap R (Term.realize vF ts)
            ↔ RelMap R (Term.realize vN ts) := by simp only [hv, vF]
        _ ↔ RelMap R ((f : M ↪[L] N) <$>ₛ Term.realize vM ts) := by simp only [hts]
        _ ↔ RelMap R (Term.realize vM ts) := by
          simp only [(f.map_rel R (Term.realize vM ts))]
        _ ↔ RelMap R (Term.realize (Fam.sumElim default xs.get) ts) := by rfl

  | imp φ ψ ihφ ihψ =>
      simp_all only [BoundedFormula.Realize]

  | @all τ σ ψ ih =>
      -- `all σ ψ` quantifies over a whole right factor `σ`.
      -- We first generalize the single-sort TV hypothesis `htv` to a block version `htv'`.

      have htv' :
          ∀ (σ₀ τ₀ : Signature Sorts)
            (φ : L.BoundedFormula Fam.EmptyFam (σ₀.prod τ₀))
            (xs₀ : M [^] σ₀) (a₀ : N[^]τ₀),
              φ.Realize default ⟨f <$>ₛ xs₀, a₀⟩ →
                ∃ bs : M[^]τ₀, φ.Realize default ⟨f <$>ₛ xs₀, f <$>ₛ bs⟩ := by
        intro σ₀ τ₀ φ xs₀ a₀ ha₀
        induction τ₀ generalizing σ₀ xs₀ with
        | nil =>
            refine ⟨(default : M[^](Signature.nil)), ?_⟩
            simpa only [Pi.default_def, PUnit.default_eq_unit] using ha₀
        | of s =>
            rcases htv s σ₀ (φ := φ) xs₀ (a := a₀) ha₀ with ⟨b, hb⟩
            refine ⟨(b : M[^](Signature.of s)), ?_⟩
            simpa only [Pi.default_def] using hb
        | prod τ₁ τ₂ ih₁ ih₂ =>
            -- write the N-witness as a pair
            rcases a₀ with ⟨a₁, a₂⟩

            -- reassociate so the last block is on the outside: σ₀ ⨯ (τ₁ ⨯ τ₂)  ≃  (σ₀ ⨯ τ₁) ⨯ τ₂
            let g : Signature.SigMap (σ₀ ⨯ (τ₁ ⨯ τ₂)) ((σ₀ ⨯ τ₁) ⨯ τ₂) :=
              Signature.SigMap.assocR (S := Sorts) σ₀ τ₁ τ₂
            let φ' : L.BoundedFormula Fam.EmptyFam (((σ₀ ⨯ τ₁) ⨯ τ₂)) :=
              φ.reindex g

            have hpull : Signature.Interpret.comap g
                (⟨⟨(f <$>ₛ xs₀), a₁⟩, a₂⟩ : N[^](((σ₀ ⨯ τ₁) ⨯ τ₂)))
                = (⟨(f <$>ₛ xs₀), (⟨a₁, a₂⟩ : N[^](τ₁ ⨯ τ₂))⟩ : N[^](σ₀ ⨯ (τ₁ ⨯ τ₂))) := by
              simp_all only [Prod.forall, Interpret.map_prod, comap_assocR, g]
            have ha' : φ'.Realize default (⟨⟨(f <$>ₛ xs₀), a₁⟩, a₂⟩ : N[^](((σ₀ ⨯ τ₁) ⨯ τ₂))) := by
              -- use realize_reindex to move between φ and φ'
              have := (BoundedFormula.realize_reindex (L := L) (α := Fam.EmptyFam) (M := N)
                (g := g) (φ := φ) (v := (default : Fam.EmptyFam →ₛ N))
                (xs := (⟨⟨(f <$>ₛ xs₀), a₁⟩, a₂⟩ : N[^](((σ₀ ⨯ τ₁) ⨯ τ₂))))).2
              -- after rewriting the comap, this is exactly ha₀
              refine this ?_
              simpa only [Pi.default_def, hpull] using ha₀


            -- Step 1: pull back τ₁ using IH₁ applied to ∃τ₂ φ'
            have hex₁ : (φ'.ex τ₂).Realize default (⟨(f <$>ₛ xs₀), a₁⟩ : N[^](σ₀ ⨯ τ₁)) := by
              -- witness is a₂
              refine (BoundedFormula.realize_ex (L := L) (α := Fam.EmptyFam) (M := N)
                (θ := φ') (η := τ₂) (v := (default : Fam.EmptyFam →ₛ N))
                (xs := (⟨(f <$>ₛ xs₀), a₁⟩ : N[^](σ₀ ⨯ τ₁)))).2 ?_
              exact ⟨a₂, by simpa only [Pi.default_def] using ha'⟩

            rcases ih₁ (σ₀ := σ₀) (φ := (φ'.ex τ₂)) (xs₀ := xs₀) (a₀ := a₁) hex₁ with ⟨b₁, hb₁⟩


            rcases (BoundedFormula.realize_ex (L := L) (α := Fam.EmptyFam) (M := N)
              (θ := φ') (η := τ₂) (v := (default : Fam.EmptyFam →ₛ N))
              (xs := (⟨(f <$>ₛ xs₀), (f <$>ₛ b₁)⟩ : N[^](σ₀ ⨯ τ₁)))).1 hb₁ with ⟨a₂', ha₂'⟩

            -- Step 2: pull back τ₂ using IH₂, now with left tuple ⟨xs₀, b₁⟩ in M
            have ha₂'' : φ'.Realize default
                (⟨⟨(f <$>ₛ xs₀), (f <$>ₛ b₁)⟩, a₂'⟩ : N[^](((σ₀ ⨯ τ₁) ⨯ τ₂))) := by
              simpa only [Pi.default_def] using ha₂'

            have hb₂_src : ∃ b₂ : M[^]τ₂,  φ'.Realize default
                (⟨⟨(f <$>ₛ xs₀), (f <$>ₛ b₁)⟩, (f <$>ₛ b₂)⟩ : N[^](((σ₀ ⨯ τ₁) ⨯ τ₂))) := by
              -- apply IH₂ with σ₀ := (σ₀ ⨯ τ₁)
              apply ih₂ (σ₀ := (σ₀ ⨯ τ₁)) (φ := φ')
                (xs₀ := (⟨xs₀, b₁⟩ : M[^](σ₀ ⨯ τ₁))) (a₀ := a₂')
              simpa only [Pi.default_def, Interpret.map_prod] using ha₂'

            rcases hb₂_src with ⟨b₂, hb₂⟩

            refine ⟨(⟨b₁, b₂⟩ : M[^](τ₁ ⨯ τ₂)), ?_⟩

            have hb₂' : φ.Realize default (Signature.Interpret.comap g
                (⟨⟨(f <$>ₛ xs₀), (f <$>ₛ b₁)⟩, (f <$>ₛ b₂)⟩ : N[^](((σ₀ ⨯ τ₁) ⨯ τ₂)))) := by
              exact (BoundedFormula.realize_reindex (L := L) (α := Fam.EmptyFam) (M := N)
                (g := g) (φ := φ) (v := (default : Fam.EmptyFam →ₛ N))
                (xs := (⟨⟨(f <$>ₛ xs₀), (f <$>ₛ b₁)⟩, (f <$>ₛ b₂)⟩ : N[^](((σ₀ ⨯ τ₁) ⨯ τ₂))))).1 (by
                  simpa only [Pi.default_def, BoundedFormula.realize_reindex, comap_assocR, g, φ']
                    using hb₂)

            have hpull2 :
                Signature.Interpret.comap g
                  (⟨⟨(f <$>ₛ xs₀), (f <$>ₛ b₁)⟩, (f <$>ₛ b₂)⟩ : N[^](((σ₀ ⨯ τ₁) ⨯ τ₂)))
                  = (⟨(f <$>ₛ xs₀), (⟨(f <$>ₛ b₁), (f <$>ₛ b₂)⟩ : N[^](τ₁ ⨯ τ₂))⟩
                  : N[^](σ₀ ⨯ (τ₁ ⨯ τ₂))) := by
              simp_all only [Prod.forall, Interpret.map_prod, comap_assocR,
                BoundedFormula.realize_reindex, BoundedFormula.realize_ex, g, φ']
            rw[hpull2] at hb₂'
            exact hb₂'

      simp only [BoundedFormula.Realize]
      constructor
      · intro h b
        have hbN : ψ.Realize default (⟨f <$>ₛ xs, f <$>ₛ b⟩ : N[^](τ.prod σ)) := h (f <$>ₛ b)
        have hbN' : ψ.Realize default (f <$>ₛ (⟨xs, b⟩ : M[^](τ.prod σ))) := by
          simpa only [Pi.default_def, Interpret.map_prod] using hbN
        exact (ih (xs := (⟨xs, b⟩ : M[^](τ.prod σ)))).1 hbN'
      · intro h a
        by_contra hna
        rw[←BoundedFormula.realize_not (M:= N) (φ:= ψ) (v:= default) (xs := (f <$>ₛ xs, a))] at hna

        have hnot : (ψ.not).Realize default (⟨f <$>ₛ xs, a⟩ : N[^](τ.prod σ)) := by
          simpa only [Pi.default_def, BoundedFormula.realize_not] using hna
        rcases htv' τ σ (φ := ψ.not) xs a hnot with ⟨bs, hbs⟩

        have hψM : ψ.Realize default (⟨xs, bs⟩ : M[^](τ.prod σ)) := h bs

        have hψN : ψ.Realize (default : Fam.EmptyFam →ₛ N) (f <$>ₛ (⟨xs, bs⟩ : M[^](τ.prod σ))) :=
          (ih (xs := (⟨xs, bs⟩ : M[^](τ.prod σ)))).2 hψM
        apply hbs
        exact hψN

/-- Bundles an embedding satisfying the Tarski-Vaught test as an elementary embedding. -/
def toElementaryEmbedding (f : M ↪[L] N)
    (htv :
    ∀ (s : Sorts) (σ : Signature Sorts)
      (φ : L.BoundedFormula Fam.EmptyFam (σ.prod (.of s)))
      (xs : M [^] σ) (a : N s),
        φ.Realize default ⟨f <$>ₛ xs, a⟩ →
          ∃ b : M s, φ.Realize default ⟨f <$>ₛ xs, f s b⟩) :
    M ↪ₑ[L] N where
  toFun := Fam.FamMapClass.toFamMap f
  map_boundedFormula' := f.isElementary_of_exists htv


end Embedding

namespace Equiv

/-- A first-order equivalence is also an elementary embedding. -/
def toElementaryEmbedding (f : M ≃[L] N) : M ↪ₑ[L] N where
  toFun := Fam.FamMapClass.toFamMap f
  map_boundedFormula' := fun φ x => by
    have h := StrongHomClass.realize_boundedFormula (g := f) φ
      (v := (default : Fam.EmptyFam →ₛ M)) (xs := x)
    have hdefault : ((f : M →ₛ N) ∘ₛ (default : Fam.EmptyFam →ₛ M)) = default := by
      ext s e
      cases e
    simpa [hdefault] using h

@[simp]
theorem toElementaryEmbedding_toEmbedding (f : M ≃[L] N) :
    f.toElementaryEmbedding.toEmbedding = f.toEmbedding :=
  rfl

@[simp]
theorem coe_toElementaryEmbedding (f : M ≃[L] N) :
    (f.toElementaryEmbedding : ∀ s, M s → N s) = (f : ∀ s, M s → N s) :=
  rfl

end Equiv

@[simp]
theorem realize_term_substructure {α : Fam Sorts} {S : L.Substructure M} {σ : Signature Sorts}
    (v : α →ₛ S) (t : L.Term α σ) :
    t.realize (S.subtype ∘ₛ v) = S.subtype <$>ₛ (t.realize v) :=
  HomClass.realize_term (g := S.subtype) (v := v) (t := t)

end MSLanguage

end MSFirstOrder
