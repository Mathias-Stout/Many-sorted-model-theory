/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Substructure.RingEmbeddingData
public import MultisortedLogic.Algebra.ACVF.ValuedField.Extend

/-!
# Adjoining one element to a field-like embedding

Given the algebraic data of an embedding of the field-like substructure of a subfield `F`, an
element `a ∉ F` and an element `b` of the target with `ReflectData` — the order of the values of
polynomials over `F` is the same at `a` and at `b` — the embedding extends to the field-like
substructure of `F(a)`, sending `a` to `b` (`exists_fieldEmbeddingData_adjoin`). The map on the new
leading terms is not read off any given map: it is *forced* by the ring homomorphism. Both halves
of the proof use this step:

* the `Γ`-part step of `RVLift` (`Algebra/ACVF/RVLift/GammaPart.lean`) adjoins an element with a
  new value, the ramified situation, for which this file also restates the hypotheses in the
  model's own terms (`ramifiedReflectAll_infinite_of_model`, `ramifiedReflectAll_finite_of_model`);
* `FieldStep` (`Algebra/ACVF/FieldStep/ReflectData.lean`) uses it in every case.

By contrast, `Algebra/ACVF/RVLift/Ramified.lean` and `Algebra/ACVF/RVLift/Residual.lean` adjoin an
element whose leading term is **already** in the `RV`-part, so that the map on it can be read off
the given embedding.

What makes this possible is that `FieldEmbeddingData` asks only for two reflection properties of a
ring homomorphism, and `ReflectData` delivers exactly those for `F[a]` — with no map of
leading-term structures anywhere, hence no circularity. Concretely:

* the kernel condition gives the homomorphism of `F[a]` (`adjoinHom`, via `extendOfKer`);
* the two reflection properties for polynomials give them for `F[a]`
  (`ringEmbeddingDataAdjoin`);
* `RingEmbeddingData.toFieldEmbeddingData` passes to the subfield `F(a)`.

Nothing here needs an elementary extension of the target, and — perhaps surprisingly — in the
ramified situation nothing needs the leading terms of `a` and `b` to correspond. Below the
ramification order the degree of the dominant monomial is determined by the value, so the two
sides match degree by degree; all that is asked of `b` is that its monomials be ordered like those
of `a`, and, in finite order, that it satisfy the image equation.

## Main definitions

* `Language.adjoinHom` : the homomorphism of `F[a]`.
* `Language.ringEmbeddingDataAdjoin` : the embedding data on `F[a]`.

## Main statements

* `Language.ramifiedReflectAll_infinite_of_model`,
  `Language.ramifiedReflectAll_finite_of_model` : the two shapes of the hypothesis, in the terms
  a model of `ACVFTheory` speaks.
* `Language.exists_fieldEmbeddingData_adjoin` : the enlargement to `F(a)`, packaged.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]
variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]

/-- The strict order of the `Γ` sort is the reverse strict order of the valuation. -/
theorem valMap_lt_iff_valuation (x y : M RVSort.K) :
    valMap (rvMap x) < valMap (rvMap y)
      ↔ (modelValSubring M).valuation y < (modelValSubring M).valuation x := by
  rw [← not_le, ← not_le, not_iff_not, valMap_le_iff_valuation]

/-! ### The hypotheses, in the terms a model speaks -/

section Hypotheses

variable (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)

variable {a : M RVSort.K} {b : N RVSort.K}

/-- **The domination hypothesis**, from its model-level form: the monomials `r · aⁱ` are ordered
by value exactly as the monomials `d r · bⁱ` are. -/
theorem ramifiedMono_of_model
    (hmono : ∀ (r r' : F) (i i' : ℕ),
      valMap (rvMap ((r : M RVSort.K) * a ^ i)) < valMap (rvMap ((r' : M RVSort.K) * a ^ i'))
        ↔ valMap (rvMap (d.hom r * b ^ i)) < valMap (rvMap (d.hom r' * b ^ i'))) :
    RamifiedMono F.subtype d.hom (modelValSubring M) (modelValSubring N) a b := by
  intro r r' i i'
  have h1 : ∀ (s : F) (j : ℕ), (modelValSubring M).valuation (F.subtype s)
      * (modelValSubring M).valuation a ^ j
      = (modelValSubring M).valuation ((s : M RVSort.K) * a ^ j) := fun s j => by
    rw [map_mul, map_pow]; rfl
  have h2 : ∀ (s : F) (j : ℕ), (modelValSubring N).valuation (d.hom s)
      * (modelValSubring N).valuation b ^ j
      = (modelValSubring N).valuation (d.hom s * b ^ j) := fun s j => by
    rw [map_mul, map_pow]
  rw [h1, h1, h2, h2, ← valMap_lt_iff_valuation, ← valMap_lt_iff_valuation]
  exact hmono r' r i' i

/-- The ramification hypothesis, read in the recovered valued field. -/
theorem ord_of_model {n : ℕ}
    (hord : ∀ k : ℕ, 0 < k → k < n → ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c)) :
    ∀ k, 0 < k → k < n → (modelValSubring M).valuation a ^ k
      ∉ (modelValSubring M).valuation '' ((F.subtype).fieldRange : Set (M RVSort.K)) := by
  rintro k hk hkn ⟨c, hc, hceq⟩
  obtain ⟨r, rfl⟩ := hc
  refine hord k hk hkn (r : M RVSort.K) r.2 ?_
  rw [valMap_eq_iff_valuation, map_pow]
  exact hceq.symm

/-- **The ramified case of infinite order**, in model terms. -/
theorem ramifiedReflectAll_infinite_of_model (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hmono : ∀ (r r' : F) (i i' : ℕ),
      valMap (rvMap ((r : M RVSort.K) * a ^ i)) < valMap (rvMap ((r' : M RVSort.K) * a ^ i'))
        ↔ valMap (rvMap (d.hom r * b ^ i)) < valMap (rvMap (d.hom r' * b ^ i')))
    (hord : ∀ k : ℕ, 0 < k → ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c)) :
    RamifiedReflectAll F.subtype d.hom (modelValSubring M) (modelValSubring N) a b :=
  ramifiedReflectAll_of_infinite (ramifiedMono_of_model F d hmono) ha0 hb0
    (fun k hk => ord_of_model F (n := k + 1) (fun j hj _ => hord j hj) k hk (Nat.lt_succ_self _))

/-- **The ramified case of finite order**, in model terms: `aⁿ` lies in `F` and `bⁿ` is its
image. No hypothesis on the order of the value of `b` is needed — the domination hypothesis
already transports it. -/
theorem ramifiedReflectAll_finite_of_model (ha0 : a ≠ 0) (hb0 : b ≠ 0) {n : ℕ} (hn : 0 < n)
    (hmono : ∀ (r r' : F) (i i' : ℕ),
      valMap (rvMap ((r : M RVSort.K) * a ^ i)) < valMap (rvMap ((r' : M RVSort.K) * a ^ i'))
        ↔ valMap (rvMap (d.hom r * b ^ i)) < valMap (rvMap (d.hom r' * b ^ i')))
    (hord : ∀ k : ℕ, 0 < k → k < n → ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c))
    {c : F} (hac : a ^ n = (c : M RVSort.K)) (hbc : b ^ n = d.hom c) :
    RamifiedReflectAll F.subtype d.hom (modelValSubring M) (modelValSubring N) a b := by
  refine ramifiedReflectAll_of_modByMonic (ramifiedMono_of_model F d hmono) ha0 hb0 hn
    (ord_of_model F hord)
    (P₀ := X ^ n - C c) (Polynomial.monic_X_pow_sub_C c hn.ne')
    (le_of_eq (Polynomial.natDegree_X_pow_sub_C c)) ?_ ?_
  · simp [hac]
  · simp [hbc]

end Hypotheses

/-! ### The enlargement -/

section Adjoin

variable (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)
  {a : M RVSort.K} {b : N RVSort.K}
  (h : ReflectData F.subtype d.hom (modelValSubring M) (modelValSubring N) a b)

/-- **The homomorphism of `F[a]`.** The kernel condition is all that is needed: `p a ↦ p b` is
then well-defined, and `ReflectData` supplies it. -/
noncomputable def adjoinHom : (evalOn F.subtype a).range →+* N RVSort.K :=
  h.extend

theorem adjoinHom_apply (x : (evalOn F.subtype a).range) {p : F[X]}
    (hp : evalOn F.subtype a p = (x : M RVSort.K)) :
    adjoinHom F d h x = evalOn' d.hom b p :=
  h.extend_apply x hp

/-- **Embedding data on `F[a]`.** Both reflection properties come from the polynomial ones. -/
noncomputable def ringEmbeddingDataAdjoin :
    RingEmbeddingData (evalOn F.subtype a).range N where
  hom := adjoinHom F d h
  rv_iff := by
    intro x y
    obtain ⟨P, hP⟩ := RingHom.mem_range.mp x.2
    obtain ⟨Q, hQ⟩ := RingHom.mem_range.mp y.2
    rw [rvMap_eq_iff_rv_eq, rvMap_eq_iff_rv_eq, adjoinHom_apply F d h x hP,
      adjoinHom_apply F d h y hQ, ← hP, ← hQ]
    exact h.rvEq P Q
  val_iff := by
    intro x y
    obtain ⟨P, hP⟩ := RingHom.mem_range.mp x.2
    obtain ⟨Q, hQ⟩ := RingHom.mem_range.mp y.2
    rw [valMap_le_iff_valuation, valMap_le_iff_valuation, adjoinHom_apply F d h x hP,
      adjoinHom_apply F d h y hQ, ← hP, ← hQ]
    exact h.valLe Q P

theorem adjoinHom_of_mem {x : M RVSort.K} (hx : x ∈ F) :
    adjoinHom F d h ⟨x, mem_evalOn_range_of_mem F a hx⟩ = d.hom ⟨x, hx⟩ := by
  rw [adjoinHom_apply F d h _ (p := C ⟨x, hx⟩) (by simp)]
  simp

theorem adjoinHom_self :
    adjoinHom F d h ⟨a, self_mem_evalOn_range F a⟩ = b := by
  rw [adjoinHom_apply F d h _ (p := X) (by simp)]
  simp

/-- **Every element of `F[a]` has the leading term of a monomial `c · aⁱ` with `c` in `F`**, and
its image has the leading term of `d c · bⁱ`. This is what brings the `Γ` sort under control: the
value of any element of `F[a]` is a value of `F` plus a multiple of the value of `a`, and the same
computation holds on the far side with the value of `b`. -/
theorem exists_monomial_adjoinHom
    (hmon : RamifiedReflectAll F.subtype d.hom (modelValSubring M) (modelValSubring N) a b)
    (x : (evalOn F.subtype a).range) :
    ∃ (c : M RVSort.K) (hc : c ∈ F) (i : ℕ),
      rvMap (x : M RVSort.K) = rvMap (c * a ^ i) ∧
        rvMap (adjoinHom F d hmon.toReflectData x) = rvMap (d.hom ⟨c, hc⟩ * b ^ i) := by
  obtain ⟨P, hP⟩ := RingHom.mem_range.mp x.2
  obtain ⟨c, i, hK, hL⟩ := hmon.monomial P
  refine ⟨(c : M RVSort.K), c.2, i, ?_, ?_⟩
  · rw [rvMap_eq_iff_rv_eq, ← hP, hK]
    rfl
  · rw [rvMap_eq_iff_rv_eq, adjoinHom_apply F d hmon.toReflectData x hP, hL,
      show (⟨(c : M RVSort.K), c.2⟩ : F) = c from Subtype.ext rfl]

include h in
/-- **The field-like enlargement.** The subfield generated by `F` and `a`, with embedding data
extending that of `F` and sending `a` to `b`. Only `ReflectData` is needed, so every case of
`FieldStep` goes through this. -/
theorem exists_fieldEmbeddingData_adjoin :
    ∃ (F' : Subfield (M RVSort.K)) (hFF' : F ≤ F') (haF' : a ∈ F')
      (d' : FieldEmbeddingData F' N),
      (∀ (x : M RVSort.K) (hx : x ∈ F), d'.hom ⟨x, hFF' hx⟩ = d.hom ⟨x, hx⟩) ∧
        d'.hom ⟨a, haF'⟩ = b := by
  set T : Subring (M RVSort.K) := (evalOn F.subtype a).range with hT
  have hFT : ∀ x ∈ F, x ∈ T := fun x hx => mem_evalOn_range_of_mem F a hx
  have hFF' : F ≤ divField T := fun x hx => subset_divField T x (hFT x hx)
  have haF' : a ∈ divField T := subset_divField T a (self_mem_evalOn_range F a)
  refine ⟨divField T, hFF', haF', (ringEmbeddingDataAdjoin F d h).toFieldEmbeddingData,
    fun x hx => ?_, ?_⟩
  · rw [(ringEmbeddingDataAdjoin F d h).toFieldEmbeddingData_hom_of_mem (hFT x hx)]
    exact adjoinHom_of_mem F d h hx
  · rw [(ringEmbeddingDataAdjoin F d h).toFieldEmbeddingData_hom_of_mem
      (self_mem_evalOn_range F a)]
    exact adjoinHom_self F d h

end Adjoin

end ManySorted.Language
