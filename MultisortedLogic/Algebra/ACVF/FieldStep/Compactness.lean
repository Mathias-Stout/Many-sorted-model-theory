/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.FieldStep.ReflectData
public import MultisortedLogic.Algebra.ACVF.Reduction
public import MultisortedLogic.RealizingTypes

/-!
# The value-comparison type, and `FieldStep` by compactness

`Algebra/ACVF/FieldStep/ReflectData.lean` reduces `FieldStep` to producing, for an element `a` of
the field sort outside `F`, an element `b` of an elementary extension of the target with
`ReflectData` — the single statement that the order of the values of polynomials at `a` and at `b`
agree. This file states that as `ValuePatternExt` and derives `FieldStep` from it
(`fieldStep_of_valuePatternExt`).

The element to adjoin is chosen by `ValuePatternExt` itself, not fixed in advance: `FieldStep`
only asks that the subfield grow, so any `a ∉ F` will do, and Rideau-Kikuchi's routing scales and
translates the given `y` before landing in one of the three cases.

The pattern is turned into a **partial type**, `reflectTypeOn`: for each pair of polynomials over
`F` in a given set, the formula `val (rv (P x)) ≤ val (rv (Q x))` or its negation, according to
which holds at `a`. Compactness (`exists_reflectData_ext_of_finsat`) then turns finite fragments
of the pattern, each matched by an element of the target, into the whole pattern in an elementary
extension. That is how `Algebra/ACVF/FieldStep/Routing.lean` proves `ValuePatternExt` in five of the
six sub-cases of Rideau-Kikuchi's three cases. In the immediate algebraic case, the far-side
element must be a root of an image polynomial *and* at prescribed distances from the whole
coefficient field, so it is produced in an elementary extension directly.

## Main definitions

* `Language.valLeFormula` : the formula `val (rv (P x)) ≤ val (rv (Q x))`.
* `Language.reflectTypeOn` : the value-comparison type of `a` over `F`, on a set of pairs of
  polynomials.
* `Language.ReflectDataExt` : the whole pattern of `a` is realized in an elementary extension of
  the target.
* `Language.ValuePatternExt` : every `y ∉ F` gives an `a ∉ F` with `ReflectDataExt`.

## Main statements

* `Language.exists_reflectData_ext_of_finsat` : the compactness step, from finite fragments in the
  target to `ReflectDataExt`.
* `Language.fieldStep_of_valuePatternExt` : `FieldStep` from `ValuePatternExt`.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial

universe w

/-! ### The comparison formula

The formula has the coefficients of `P` and `Q` as parameters, that is, it is an
`rvLang[[N]]`-formula. Its polynomial terms are built with the ring symbols of `rvLang`, read in
`rvLang[[α]]` through `Sum.inl` (`instRingLKWithConstants`). -/

/-- The term `val (rv (P x))` in the bound variable `x` of the field sort, with the coefficients
of `P` as parameters. -/
noncomputable def valRvPolyT (N : RVSort → Type w) [rvLang.Structure N] [N ⊨ ACVFTheory]
    (P : Polynomial (N RVSort.K)) : rvLang[[N]].Term ⦃RVSort.K⦄ ⦃RVSort.Γ⦄ :=
  .func (Sum.inl RVFunc.val) (.func (Sum.inl RVFunc.rv)
    (polyT (.var .var) P.natDegree fun i => Term.con rvLang (P.coeff i)))

/-- The formula `val (rv (P x)) ≤ val (rv (Q x))` in one bound variable `x` of the field sort,
with the coefficients of `P` and of `Q` as parameters. -/
noncomputable def valLeFormula (N : RVSort → Type w) [rvLang.Structure N] [N ⊨ ACVFTheory]
    (P Q : Polynomial (N RVSort.K)) : rvLang[[N]].Formula ⦃RVSort.K⦄ :=
  .rel (Sum.inl RVRel.leΓ) (.prod (valRvPolyT N P) (valRvPolyT N Q))

theorem realize_valRvPolyT {N N'' : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]
    [rvLang.Structure N''] [N'' ⊨ ACVFTheory] (v : ∀ s, N s → N'' s)
    (P : Polynomial (N RVSort.K)) (c : N'' RVSort.K) :
    @Term.realize _ rvLang[[N]] _ N'' (withConstantsStructure v) (c : N'' [^] ⦃RVSort.K⦄) _
        (valRvPolyT N P) =
      valMap (rvMap (polyVal c P.natDegree (fun i => v RVSort.K (P.coeff i)))) := by
  let := withConstantsStructure (L := rvLang) v
  have : CompatibleRingL rvLang[[N]] N'' RVSort.K :=
    { funMap_add := fun _ => rfl, funMap_mul := fun _ => rfl, funMap_neg := fun _ => rfl,
      funMap_zero := rfl, funMap_one := rfl }
  simp only [valRvPolyT, Term.realize_func, realize_polyT, Term.realize_con]
  rfl

@[simp]
theorem realize_valLeFormula {N N'' : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]
    [rvLang.Structure N''] [N'' ⊨ ACVFTheory] (v : ∀ s, N s → N'' s)
    (P Q : Polynomial (N RVSort.K)) (c : N'' RVSort.K) :
    (valLeFormula N P Q).RealizeWith v (c : N'' [^] ⦃RVSort.K⦄) ↔
      valMap (rvMap (polyVal c P.natDegree (fun i => v RVSort.K (P.coeff i))))
        ≤ valMap (rvMap (polyVal c Q.natDegree (fun i => v RVSort.K (Q.coeff i)))) := by
  rw [← realize_valRvPolyT v P c, ← realize_valRvPolyT v Q c]
  exact Iff.rfl

/-! ### Comparisons realized in an extension -/

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]
variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]

/-- The Horner value of the pushed-forward coefficients is the value of the polynomial. -/
theorem polyVal_eq_evalOn' {N'' : RVSort → Type w} [rvLang.Structure N''] [N'' ⊨ ACVFTheory]
    (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N) (k : N ↪[rvLang] N'')
    (v : ∀ s, N s → N'' s) (hv : ∀ (s : RVSort) (x : N s), v s x = k s x) (b : N'' RVSort.K)
    (P : Polynomial F) :
    polyVal b (P.map d.hom).natDegree (fun i => v RVSort.K ((P.map d.hom).coeff i))
      = evalOn' (d.comp k).hom b P := by
  have hfun : (fun i => v RVSort.K ((P.map d.hom).coeff i))
      = fun i => embRingHom k ((P.map d.hom).coeff i) :=
    funext fun i => hv RVSort.K _
  rw [hfun, polyVal_map_eq_eval (embRingHom k) (P.map d.hom) b, Polynomial.map_map]
  exact Polynomial.eval_map ((embRingHom k).comp d.hom) b

/-- A comparison or its negation, according to `hc`, realized at `b` gives the comparison at
`b` the same truth value as at `a`. -/
theorem iff_of_realize_valLe {N'' : RVSort → Type w} [rvLang.Structure N''] [N'' ⊨ ACVFTheory]
    (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N) (a : M RVSort.K)
    (k : N ↪[rvLang] N'') (v : ∀ s, N s → N'' s) (hv : ∀ (s : RVSort) (x : N s), v s x = k s x)
    (b : N'' RVSort.K) (P Q : Polynomial F)
    (hreal : ∀ ψ, ((valMap (rvMap (evalOn F.subtype a P)) ≤ valMap (rvMap (evalOn F.subtype a Q))
          ∧ ψ = valLeFormula N (P.map d.hom) (Q.map d.hom)) ∨
        (¬ valMap (rvMap (evalOn F.subtype a P)) ≤ valMap (rvMap (evalOn F.subtype a Q)) ∧
          ψ = ∼(valLeFormula N (P.map d.hom) (Q.map d.hom)))) →
        ψ.RealizeWith v (b : N'' [^] ⦃RVSort.K⦄)) :
    (valMap (rvMap (evalOn F.subtype a P)) ≤ valMap (rvMap (evalOn F.subtype a Q))
      ↔ valMap (rvMap (evalOn' (d.comp k).hom b P))
        ≤ valMap (rvMap (evalOn' (d.comp k).hom b Q))) := by
  by_cases hc : valMap (rvMap (evalOn F.subtype a P)) ≤ valMap (rvMap (evalOn F.subtype a Q))
  · have hm := hreal _ (Or.inl ⟨hc, rfl⟩)
    rw [realize_valLeFormula, polyVal_eq_evalOn' F d k v hv b P,
      polyVal_eq_evalOn' F d k v hv b Q] at hm
    exact iff_of_true hc hm
  · have hm : ¬ (valLeFormula N (P.map d.hom) (Q.map d.hom)).RealizeWith v
        (b : N'' [^] ⦃RVSort.K⦄) := hreal _ (Or.inr ⟨hc, rfl⟩)
    rw [realize_valLeFormula, polyVal_eq_evalOn' F d k v hv b P,
      polyVal_eq_evalOn' F d k v hv b Q] at hm
    exact iff_of_false hc hm

/-! ### The round trip between an embedding and its algebraic data -/

theorem toEmbedding_ofEmbedding {F : Subfield (M RVSort.K)}
    (h : (fun s => ↥(fieldSubstructure M F s)) ↪[rvLang] N) (s : RVSort)
    (m : fieldSubstructure M F s) :
    (FieldEmbeddingData.ofEmbedding h).toEmbedding s m = h s m := by
  match s with
  | RVSort.K => rfl
  | RVSort.RV =>
    obtain ⟨x, hx, hxm⟩ := m.2
    have hcast : m = ⟨rvMap x, ⟨x, hx, rfl⟩⟩ := Subtype.ext hxm.symm
    subst hcast
    change (FieldEmbeddingData.ofEmbedding h).rvComp ⟨rvMap x, ⟨x, hx, rfl⟩⟩ = _
    rw [(FieldEmbeddingData.ofEmbedding h).rvComp_apply hx ⟨x, hx, rfl⟩,
      FieldEmbeddingData.ofEmbedding_hom]
    exact (emb_rvMap h hx ⟨x, hx, rfl⟩).symm
  | RVSort.Γ =>
    obtain ⟨x, hx, hxm⟩ := m.2
    have hcast : m = ⟨valMap (rvMap x), ⟨x, hx, rfl⟩⟩ := Subtype.ext hxm.symm
    subst hcast
    change (FieldEmbeddingData.ofEmbedding h).gammaComp ⟨valMap (rvMap x), ⟨x, hx, rfl⟩⟩ = _
    rw [(FieldEmbeddingData.ofEmbedding h).gammaComp_apply hx ⟨x, hx, rfl⟩,
      FieldEmbeddingData.ofEmbedding_hom, ← emb_rvMap h hx ⟨x, hx, rfl⟩]
    exact (emb_valMap h ⟨x, hx, rfl⟩ ⟨x, hx, rfl⟩).symm

/-- The Horner value of the coefficients of `P^d`, in the target itself. -/
theorem polyVal_self_eq_evalOn' (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)
    (b : N RVSort.K) (P : Polynomial F) :
    polyVal b (P.map d.hom).natDegree (fun i => (P.map d.hom).coeff i) = evalOn' d.hom b P := by
  rw [polyVal_coeff_eq_eval]
  exact Polynomial.eval_map d.hom b

/-! ### The pattern, and the compactness step -/

/-- The pattern is realized exactly, with no finiteness needed, when `a` already lies in `F`:
`d a` does it, because `d` reflects the order of values. -/
theorem exists_valuePattern_of_mem (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)
    {a : M RVSort.K} (ha : a ∈ F) (P Q : Polynomial F) :
    valMap (rvMap (evalOn F.subtype a P)) ≤ valMap (rvMap (evalOn F.subtype a Q))
      ↔ valMap (rvMap (evalOn' d.hom (d.hom ⟨a, ha⟩) P))
        ≤ valMap (rvMap (evalOn' d.hom (d.hom ⟨a, ha⟩) Q)) := by
  have hK : ∀ R : Polynomial F, evalOn F.subtype a R = ((R.eval ⟨a, ha⟩ : F) : M RVSort.K) :=
    fun R => Polynomial.eval₂_at_apply F.subtype ⟨a, ha⟩
  have hL : ∀ R : Polynomial F,
      evalOn' d.hom (d.hom ⟨a, ha⟩) R = d.hom (R.eval ⟨a, ha⟩) :=
    fun R => Polynomial.eval₂_at_apply d.hom ⟨a, ha⟩
  rw [hK, hK, hL, hL]
  exact d.val_iff (P.eval ⟨a, ha⟩) (Q.eval ⟨a, ha⟩)

/-- **The whole pattern of `a` over `F`, realized in an elementary extension of the target.**
This is what `FieldStep` needs of a candidate element. It lets the target grow, and the immediate
algebraic case needs that freedom: there the far-side element must be a root of an image
polynomial *and* at prescribed distances from the whole coefficient field, and no element of `N`
need be both. -/
def ReflectDataExt {M N : RVSort → Type} [rvLang.Structure M] [rvLang.Structure N]
    [M ⊨ ACVFTheory] [N ⊨ ACVFTheory]
    (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N) (a : M RVSort.K) : Prop :=
  ∃ (P : RVSort → Type) (_ : rvLang.Structure P) (_ : ∀ s, Nonempty (P s))
    (j : N ↪ₑ[rvLang] P),
    haveI : P ⊨ ACVFTheory := j.theory_model
    ∃ b : P RVSort.K,
      ReflectData F.subtype (d.comp j.toEmbedding).hom (modelValSubring M) (modelValSubring P) a b

/-- The finite fragments of a set of comparisons, each realized by some `b : N`, are realized in
`N`. This is the finite satisfiability the compactness step needs, for any set `S` of pairs. -/
theorem finsat_reflectTypeOn (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)
    (a : M RVSort.K) (S : Set (Polynomial F × Polynomial F))
    (hfin : ∀ t : Finset (Polynomial F × Polynomial F), (↑t : Set _) ⊆ S →
      ∃ b : N RVSort.K, ∀ p ∈ t,
        (valMap (rvMap (evalOn F.subtype a p.1)) ≤ valMap (rvMap (evalOn F.subtype a p.2))
          ↔ valMap (rvMap (evalOn' d.hom b p.1)) ≤ valMap (rvMap (evalOn' d.hom b p.2))))
    (p₀ : Finset (rvLang[[N]].Formula ⦃RVSort.K⦄))
    (hp₀ : ∀ ψ ∈ p₀, ∃ p ∈ S,
      (valMap (rvMap (evalOn F.subtype a p.1)) ≤ valMap (rvMap (evalOn F.subtype a p.2)) ∧
          ψ = valLeFormula N (p.1.map d.hom) (p.2.map d.hom)) ∨
        (¬ valMap (rvMap (evalOn F.subtype a p.1)) ≤ valMap (rvMap (evalOn F.subtype a p.2)) ∧
          ψ = ∼(valLeFormula N (p.1.map d.hom) (p.2.map d.hom)))) :
    ∃ xs : N [^] ⦃RVSort.K⦄,
      FormulaSet.RealizeWith (↑p₀ : rvLang[[N]].FormulaSet ⦃RVSort.K⦄) (fun _ => id) xs := by
  classical
  choose pf hpfS hpf using fun ψ : {ψ // ψ ∈ p₀} => hp₀ ψ.1 ψ.2
  obtain ⟨b, hb⟩ := hfin (p₀.attach.image pf) (by
    intro p hp
    obtain ⟨ψ, -, hψ⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    exact hψ ▸ hpfS ψ)
  refine ⟨b, fun ψ hψ => ?_⟩
  have hiff := hb _ (Finset.mem_image_of_mem pf (Finset.mem_attach _ ⟨ψ, Finset.mem_coe.mp hψ⟩))
  rcases hpf ⟨ψ, Finset.mem_coe.mp hψ⟩ with ⟨hle, hform⟩ | ⟨hnle, hform⟩
  · change ψ.RealizeWith (fun _ => id) b
    dsimp only at hform
    rw [hform, realize_valLeFormula]
    simp only [id, polyVal_self_eq_evalOn']
    exact hiff.mp hle
  · change ψ.RealizeWith (fun _ => id) b
    dsimp only at hform
    rw [hform]
    change ¬ (valLeFormula N _ _).RealizeWith (fun _ => id) (b : N [^] ⦃RVSort.K⦄)
    rw [realize_valLeFormula]
    simp only [id, polyVal_self_eq_evalOn']
    exact fun hcon => hnle (hiff.mpr hcon)

/-- **The value-comparison type of `a` over `F`, restricted to a set of pairs.** -/
def reflectTypeOn (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N) (a : M RVSort.K)
    (S : Set (Polynomial F × Polynomial F)) : rvLang[[N]].FormulaSet ⦃RVSort.K⦄ :=
  {ψ | ∃ p ∈ S,
    (valMap (rvMap (evalOn F.subtype a p.1)) ≤ valMap (rvMap (evalOn F.subtype a p.2)) ∧
        ψ = valLeFormula N (p.1.map d.hom) (p.2.map d.hom)) ∨
      (¬ valMap (rvMap (evalOn F.subtype a p.1)) ≤ valMap (rvMap (evalOn F.subtype a p.2)) ∧
        ψ = ∼(valLeFormula N (p.1.map d.hom) (p.2.map d.hom)))}

/-- A realization of the restricted type matches the pattern on every pair of `S`. -/
theorem realize_reflectTypeOn (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)
    (a : M RVSort.K) (S : Set (Polynomial F × Polynomial F))
    {N'' : RVSort → Type w} [rvLang.Structure N''] [N'' ⊨ ACVFTheory]
    (k : N ↪[rvLang] N'') (v : ∀ s, N s → N'' s) (hv : ∀ (s : RVSort) (x : N s), v s x = k s x)
    (b : N'' RVSort.K)
    (hreal : (reflectTypeOn F d a S).RealizeWith v (b : N'' [^] ⦃RVSort.K⦄)) :
    ∀ p ∈ S, (valMap (rvMap (evalOn F.subtype a p.1))
        ≤ valMap (rvMap (evalOn F.subtype a p.2))
      ↔ valMap (rvMap (evalOn' (d.comp k).hom b p.1))
        ≤ valMap (rvMap (evalOn' (d.comp k).hom b p.2))) :=
  fun p hp => iff_of_realize_valLe F d a k v hv b p.1 p.2 fun ψ hψ => hreal ψ ⟨p, hp, hψ⟩

/-- **The compactness step on a restricted set of pairs.** -/
theorem exists_realize_ext_of_finsat_on {M N : RVSort → Type} [rvLang.Structure M]
    [rvLang.Structure N] [∀ s, Nonempty (N s)] [M ⊨ ACVFTheory]
    [N ⊨ ACVFTheory] (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)
    (a : M RVSort.K) (S : Set (Polynomial F × Polynomial F))
    (hfin : ∀ t : Finset (Polynomial F × Polynomial F), (↑t : Set _) ⊆ S →
      ∃ b : N RVSort.K, ∀ p ∈ t,
        (valMap (rvMap (evalOn F.subtype a p.1)) ≤ valMap (rvMap (evalOn F.subtype a p.2))
          ↔ valMap (rvMap (evalOn' d.hom b p.1)) ≤ valMap (rvMap (evalOn' d.hom b p.2)))) :
    ∃ (P : RVSort → Type) (_ : rvLang.Structure P) (_ : ∀ s, Nonempty (P s))
      (j : N ↪ₑ[rvLang] P),
      haveI : P ⊨ ACVFTheory := j.theory_model
      ∃ b : P RVSort.K, ∀ p ∈ S,
        (valMap (rvMap (evalOn F.subtype a p.1)) ≤ valMap (rvMap (evalOn F.subtype a p.2))
          ↔ valMap (rvMap (evalOn' (d.comp j.toEmbedding).hom b p.1))
            ≤ valMap (rvMap (evalOn' (d.comp j.toEmbedding).hom b p.2))) := by
  obtain ⟨P, _, _, j, b, hreal⟩ := exists_elementaryEmbedding_realize (reflectTypeOn F d a S)
    fun p₀ hp₀ => finsat_reflectTypeOn F d a S hfin p₀ fun ψ hψ => hp₀ hψ
  have : P ⊨ ACVFTheory := j.theory_model
  exact ⟨P, inferInstance, inferInstance, j, b,
    realize_reflectTypeOn F d a S j.toEmbedding j (fun _ _ => rfl) b hreal⟩

/-- **The compactness step.** For every finite set of polynomials over `F` some element of the
target has the same pattern of value comparisons among them as `a` does; compactness turns that
into a single element of an elementary extension with the *whole* pattern. -/
theorem exists_reflectData_ext_of_finsat {M N : RVSort → Type} [rvLang.Structure M]
    [rvLang.Structure N] [∀ s, Nonempty (N s)] [M ⊨ ACVFTheory]
    [N ⊨ ACVFTheory] (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)
    (a : M RVSort.K)
    (hfin' : ∀ t : Finset (Polynomial F), ∃ b : N RVSort.K, ∀ P ∈ t, ∀ Q ∈ t,
      (valMap (rvMap (evalOn F.subtype a P)) ≤ valMap (rvMap (evalOn F.subtype a Q))
        ↔ valMap (rvMap (evalOn' d.hom b P)) ≤ valMap (rvMap (evalOn' d.hom b Q)))) :
    ReflectDataExt F d a := by
  classical
  obtain ⟨P, _, _, j, b, hb⟩ := exists_realize_ext_of_finsat_on F d a Set.univ fun t _ => by
    obtain ⟨b, hb⟩ := hfin' (t.image Prod.fst ∪ t.image Prod.snd)
    exact ⟨b, fun p hp => hb _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))⟩
  have : P ⊨ ACVFTheory := j.theory_model
  refine ⟨P, inferInstance, inferInstance, j, b, ⟨fun P' Q' => ?_⟩⟩
  rw [← valMap_le_iff_valuation, ← valMap_le_iff_valuation]
  exact hb (Q', P') (Set.mem_univ _)

/-! ### The pattern realized in an elementary extension

`FieldStep` lets the target grow, so the pattern only has to be realized in *some* elementary
extension of it. That is what `exists_reflectData_ext_of_finsat` turns the finite fragment into,
and it is what the immediate algebraic case supplies directly — there the far-side element is a root
of an image polynomial *and* at prescribed distances from the whole coefficient field, which no
single element of the target need satisfy. -/

/-- **The statement `FieldStep` really needs.** For `y ∉ F` there is an `a ∉ F` whose whole
pattern of value comparisons over `F` is realized in an elementary extension of the target. -/
def ValuePatternExt : Prop :=
  ∀ (M N : RVSort → Type) [rvLang.Structure M] [rvLang.Structure N]
    [∀ s, Nonempty (M s)] [∀ s, Nonempty (N s)] [M ⊨ ACVFTheory] [N ⊨ ACVFTheory]
    (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N) (y : M RVSort.K), y ∉ F →
    ∃ a : M RVSort.K, a ∉ F ∧ ReflectDataExt F d a

/-- **`FieldStep` from it.** -/
theorem fieldStep_of_valuePatternExt (hext : ValuePatternExt) : FieldStep := by
  intro M N _ _ _ _ _ _ F h hy
  obtain ⟨y, hyF⟩ := hy
  set d : FieldEmbeddingData F N := FieldEmbeddingData.ofEmbedding h with hd
  obtain ⟨a, haF, P, _, _, j, hb⟩ := hext M N F d y hyF
  have : P ⊨ ACVFTheory := j.theory_model
  obtain ⟨b, href⟩ := hb
  obtain ⟨F', hFF', x, hxF', hxF, h', hcomm⟩ :=
    exists_fieldStep_target F (d.comp j.toEmbedding) haF href
  refine ⟨P, inferInstance, inferInstance, j, F', hFF', x, hxF', hxF, h', fun s m => ?_⟩
  rw [hcomm s m, FieldEmbeddingData.comp_toEmbedding, hd, toEmbedding_ofEmbedding]
  rfl

end ManySorted.Language
