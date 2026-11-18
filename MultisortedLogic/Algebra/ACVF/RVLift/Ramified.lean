/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.RVLift.LiftStep
public import MultisortedLogic.Algebra.ACVF.ValuedField.Lift

/-!
# Lifting a leading term to the field sort: the ramified cases

Two of the four cases of steps `res(K(C)) = k(C)` and `v(K(C)) = Γ(C)` of Rideau-Kikuchi's
Proposition 2.1.10 (the routing step of `RVLift`). A substructure `S` whose field part is a subfield
`F` is enlarged by one element `a` of the field sort, chosen so that no new leading terms appear, so
that `Algebra/ACVF/RVLift/LiftStep.lean` extends the embedding across it.

These are the cases where the **value** of `a` is what is new. If `v a` has order at least `n`
over the value group of `F` then, for `Q` over `F` of degree below `n`, the monomials `c aⁱ` have
pairwise distinct values, so exactly one dominates and

  `rv (Q a) = rv (q_{i₀}) · (rv a)^{i₀}`,

which already lies in the `RV`-part of `S`. That covers every degree when the order is infinite;
when the order is exactly `n` and `aⁿ` lies in `F`, reduction modulo `Xⁿ - aⁿ` brings every
element of `F[a]` into a degree below `n`, so it covers `F[a]` there too.

The far side differs between the two. For infinite order, any element with the matching leading
term will do: the embedding transports the domination
(`ValuationSubring.rv_eval_eq_of_ramified_transfer`). For finite order, the far-side element has
to be an `n`-th root of the image of `aⁿ` *as well as* have the matching leading term, and
`exists_pow_matching` produces one — two `n`-th roots of the same element differ by a root of
unity of the leading-term structure, and those lift to the field
(`ValuationSubring.exists_pow_eq_one_rv_eq`). Neither case needs an elementary extension of the
target.

## Main statements

* `Language.rvMap_eval_mem_RV_of_ramified` : the leading term of one `Q a` is already present.
* `Language.rvMap_mem_RV_of_mem_adjoin_ramified`,
  `Language.rvMap_mem_RV_of_mem_adjoin_ramified_finite` : hence so are all the leading terms of
  `F[a]`, in infinite and in finite order.
* `Language.exists_pow_matching` : the matching `n`-th root on the far side.
* `Language.exists_lift_ramified`, `Language.exists_lift_ramified_finite` : the extension of the
  substructure and of the embedding.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]
variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]

/-! ### No new leading terms -/

variable (S : rvLang.Substructure M)

/-- **The core of the ramified computation.** The leading term of one `Q a`, for `Q` over `F` of
degree below the order of `v a` over the values of `F`: the monomials have pairwise distinct
values, so one dominates, and its leading term is a product of leading terms already in the
`RV`-part. -/
theorem rvMap_eval_mem_RV_of_ramified {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K) {a : M RVSort.K} (ha0 : a ≠ 0)
    (haS : rvMap a ∈ S RVSort.RV) {n : ℕ}
    (hord : ∀ k : ℕ, 0 < k → k < n → ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c))
    (p : F[X]) (hpn : p.natDegree < n) :
    rvMap (evalOn F.subtype a p) ∈ S RVSort.RV := by
  -- the hypothesis, read as a statement about the valuation of the recovered valued field
  have hordM : ∀ k, 0 < k → k < n →
      (modelValSubring M).valuation a ^ k
        ∉ (modelValSubring M).valuation '' (F : Set (M RVSort.K)) := by
    rintro k hk hkn ⟨c, hcF, hceq⟩
    refine hord k hk hkn c hcF ?_
    rw [valMap_eq_iff_valuation, map_pow]
    exact hceq.symm
  have hev : evalOn F.subtype a p = (p.map F.subtype).eval a := (Polynomial.eval_map _ _).symm
  have hQF : ∀ i, (p.map F.subtype).coeff i ∈ F := by
    intro i
    rw [Polynomial.coeff_map]
    exact (p.coeff i).2
  by_cases hQ0 : p.map F.subtype = 0
  · rw [hev, hQ0, Polynomial.eval_zero, model_rv_zero]
    exact zero_mem_RV
  have hQn : (p.map F.subtype).natDegree < n := by rwa [Polynomial.natDegree_map]
  obtain ⟨i₀, -, -, hrv⟩ :=
    rv_eval_eq_of_ramified (A := modelValSubring M) ha0 hordM hQ0 hQF hQn
  have hmul : rvMap ((p.map F.subtype).eval a)
      = rvMap ((p.map F.subtype).coeff i₀ * a ^ i₀) := by
    refine rvMap_eq_iff_rv_eq.mpr ?_
    rw [hrv, map_mul, map_pow]
  rw [hev, hmul, model_rv_mul]
  exact mul_mem_RV (rvMap_mem_RV (hFS _ (hQF i₀))) (rvMap_pow_mem_RV haS i₀)

/-- **The leading terms of `F[a]` are already present**, when `v a` has infinite order over the
values of `F`. -/
theorem rvMap_mem_RV_of_mem_adjoin_ramified {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K) {a : M RVSort.K} (ha0 : a ≠ 0)
    (haS : rvMap a ∈ S RVSort.RV)
    (hord : ∀ k : ℕ, 0 < k → ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c)) :
    ∀ x ∈ (evalOn F.subtype a).range, rvMap x ∈ S RVSort.RV := by
  intro x hx
  obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hx
  exact rvMap_eval_mem_RV_of_ramified S (n := p.natDegree + 1) hFS ha0 haS
    (fun k hk _ => hord k hk) p (Nat.lt_succ_self _)

/-- **The leading terms of `F[a]` are already present**, when `v a` has order exactly `n` over
the values of `F` and `aⁿ` lies in `F`. Reduction modulo `Xⁿ - c` brings every element of `F[a]`
into a degree below `n`, where the monomials again have pairwise distinct values. -/
theorem rvMap_mem_RV_of_mem_adjoin_ramified_finite {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K) {a : M RVSort.K} (ha0 : a ≠ 0)
    (haS : rvMap a ∈ S RVSort.RV) {n : ℕ} (hn : 0 < n) {c : F}
    (hac : a ^ n = (c : M RVSort.K))
    (hord : ∀ k : ℕ, 0 < k → k < n → ∀ d ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap d)) :
    ∀ x ∈ (evalOn F.subtype a).range, rvMap x ∈ S RVSort.RV := by
  have hP : (X ^ n - C c : F[X]).Monic := Polynomial.monic_X_pow_sub_C c hn.ne'
  have hPa : evalOn F.subtype a (X ^ n - C c : F[X]) = 0 := by
    simp [hac]
  intro x hx
  obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hx
  have hred : evalOn F.subtype a p = evalOn F.subtype a (p %ₘ (X ^ n - C c)) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div p (X ^ n - C c)]
    rw [map_add, map_mul, hPa, zero_mul, add_zero]
  rw [hred]
  by_cases hq0 : p %ₘ (X ^ n - C c) = 0
  · rw [hq0, map_zero, model_rv_zero]
    exact zero_mem_RV
  · refine rvMap_eval_mem_RV_of_ramified S hFS ha0 haS hord _ ?_
    have h1 := Polynomial.natDegree_lt_natDegree hq0
      (Polynomial.degree_modByMonic_lt p hP)
    rwa [Polynomial.natDegree_X_pow_sub_C] at h1

/-! ### The extension of the embedding -/

variable (e : (fun s => ↥(S s)) ↪[rvLang] N)

/-- **Step `v(K(C)) = Γ(C)`, the case of infinite order.** Let `S` be a substructure whose field
part is a subfield `F`, and let `a` be an element of the field sort whose leading term is already in
the `RV`-part of `S` and whose value has infinite order over the values of `F`. Then `S` extends to
a substructure containing `a`, with the `RV`- and `Γ`-parts unchanged, and the embedding extends to
it. No elementary extension of the target is needed. -/
theorem exists_lift_ramified {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F) {a : M RVSort.K} (ha0 : a ≠ 0)
    (haS : rvMap a ∈ S RVSort.RV)
    (hord : ∀ k : ℕ, 0 < k → ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c)) :
    LiftStepAt S e a := by
  classical
  -- the subring `F[a]` and the subfield it generates
  have hT := rvMap_mem_RV_of_mem_adjoin_ramified S hFS ha0 haS hord
  -- the subfield generated by `F[a]`, kept opaque: only these two properties of it are used
  obtain ⟨E, hEsub, hE⟩ : ∃ E : Subfield (M RVSort.K),
      (∀ x ∈ (evalOn F.subtype a).range, x ∈ E) ∧
      (∀ x ∈ E, rvMap x ∈ S RVSort.RV) :=
    ⟨Subfield.closure _, fun _ hx => Subfield.subset_closure hx,
      fun _ hx => rvMap_mem_RV_of_mem_subfieldClosure hT hx⟩
  have hFE : F ≤ E := fun _ hx => hEsub _ (mem_evalOn_range_of_mem F a hx)
  have haE : a ∈ E := hEsub _ (self_mem_evalOn_range F a)
  -- the matching element on the far side
  obtain ⟨b, hb⟩ := model_rv_surjective (M := N) (embRV S e (rvMap a))
  -- the leading terms of `a` and `b` correspond
  have hab : liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype) (⟨a, haE⟩ : E))
      = rv (A := modelValSubring N) b := by
    rw [liftRvHom_rv]
    change toRV (embRV S e (rvMap a)) = rv (A := modelValSubring N) b
    rw [← hb, toRV_rvMap]
  -- and so do those of every monomial
  have hmatch : ∀ (r : F) (i : ℕ),
      liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype)
          (Subfield.inclusion hFE r * (⟨a, haE⟩ : E) ^ i))
        = rv (A := modelValSubring N) (subfieldHom S e hFS r * b ^ i) := by
    intro r i
    rw [map_mul, map_pow, map_mul, map_pow, liftRvHom_compat S e hFE hE hFS, hab, ← map_pow,
      ← map_mul]
  -- the order of values transfers, which is the hypothesis `hmono`
  have hmono : ∀ (r r' : F) (i i' : ℕ),
      ((modelValSubring M).comap E.subtype).valuation
          (Subfield.inclusion hFE r * (⟨a, haE⟩ : E) ^ i)
        < ((modelValSubring M).comap E.subtype).valuation
          (Subfield.inclusion hFE r' * (⟨a, haE⟩ : E) ^ i') →
      (modelValSubring N).valuation (subfieldHom S e hFS r * b ^ i)
        < (modelValSubring N).valuation (subfieldHom S e hFS r' * b ^ i') := fun r r' i i' =>
    (liftRvHom_valuation_lt_iff S e hE (hmatch r i) (hmatch r' i')).mp
  -- the order hypothesis, read inside `E`
  have hordE : ∀ k, 0 < k →
      ((modelValSubring M).comap E.subtype).valuation (⟨a, haE⟩ : E) ^ k
        ∉ ((modelValSubring M).comap E.subtype).valuation ''
          ((Subfield.inclusion hFE).fieldRange : Set E) := by
    rintro k hk ⟨c, hc, hceq⟩
    obtain ⟨r, rfl⟩ := hc
    refine hord k hk (r : M RVSort.K) r.2 ?_
    rw [valMap_eq_iff_valuation]
    have h1 : ((modelValSubring M).comap E.subtype).valuation (Subfield.inclusion hFE r)
        = ((modelValSubring M).comap E.subtype).valuation ((⟨a, haE⟩ : E) ^ k) := by
      rw [map_pow]; exact hceq
    rw [valuation_comap_eq_iff] at h1
    change (modelValSubring M).valuation (r : M RVSort.K)
      = (modelValSubring M).valuation ((⟨a, haE⟩ : E) ^ k : E) at h1
    rw [show (((⟨a, haE⟩ : E) ^ k : E) : M RVSort.K) = a ^ k from map_pow E.subtype _ k] at h1
    exact h1.symm
  have ha0E : (⟨a, haE⟩ : E) ≠ 0 := fun hc => ha0 (congrArg Subtype.val hc)
  -- the leading-term type of `a` over `F` is matched by `b`
  have H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS)
      (⟨a, haE⟩ : E) b := fun Q =>
    rv_eval_eq_of_ramified_transfer (n := Q.natDegree + 1) (liftRvHom_compat S e hFE hE hFS)
      hmono hab ha0E (fun k hk _ => hordE k hk) Q (Nat.lt_succ_self _)
  refine ⟨liftAdjoin S hFE hE hSF ⟨a, haE⟩, liftEmbedding S e hFE hE hFS hSF H, ?_,
    self_mem_liftIncl_range hFE ⟨a, haE⟩, rfl, rfl, ?_⟩
  · intro s x hx
    match s with
    | RVSort.K => exact mem_liftIncl_range_of_mem hFE ⟨a, haE⟩ (hSF x hx)
    | RVSort.RV => exact hx
    | RVSort.Γ => exact hx
  · intro s x hx hx'
    match s with
    | RVSort.K => exact liftEmbedding_apply_K_of_mem S e hFE hE hFS hSF H hx hx'
    | RVSort.RV => rfl
    | RVSort.Γ => rfl

/-! ### The ramified case of finite order

Here the far-side element has to be an `n`-th root of the image of `aⁿ` as well as have the
matching leading term. -/

/-- **The matching `n`-th root on the far side.** If `aⁿ` lies in the coefficient field, the
target contains an `n`-th root of its image with the matching leading term: any two `n`-th roots
of the image differ by a root of unity of the leading-term structure, and those are leading terms
of roots of unity of the field. -/
theorem exists_pow_matching {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K) {a : M RVSort.K} (ha0 : a ≠ 0)
    (haS : rvMap a ∈ S RVSort.RV) {n : ℕ} (hn : 0 < n) {c : F}
    (hac : a ^ n = (c : M RVSort.K)) :
    ∃ b : N RVSort.K, b ^ n = subfieldHom S e hFS c ∧ rvMap b = embRV S e (rvMap a) := by
  classical
  have hc0 : (c : M RVSort.K) ≠ 0 := by rw [← hac]; exact pow_ne_zero n ha0
  have hcne : c ≠ 0 := fun h => hc0 (by rw [h]; rfl)
  have hψc : subfieldHom S e hFS c ≠ 0 := fun hcon =>
    hcne ((subfieldHom S e hFS).injective (by rw [hcon, map_zero]))
  set ζ : (modelValSubring N).RV := toRV (embRV S e (rvMap a)) with hζdef
  have hζn : ζ ^ n = rv (A := modelValSubring N) (subfieldHom S e hFS c) := by
    rw [hζdef, ← toRV_embRV_pow S e haS n, hac, embRV_rvMap S e (hFS _ c.2), toRV_rvMap]
    rfl
  -- an `n`-th root of the image with the prescribed leading term
  obtain ⟨b, hbn, hbrv⟩ := exists_pow_eq_rv_eq (A := modelValSubring N) hn hζn
  refine ⟨b, hbn, ?_⟩
  refine toRV_injective ?_
  rw [toRV_rvMap, hbrv]

/-- **Step `v(K(C)) = Γ(C)`, the case of finite order.** Let `S` be a substructure whose field part
is a subfield `F`, and let `a` be an element of the field sort whose leading term is already in the
`RV`-part of `S`, whose value has order at least `n` over the values of `F`, and with `aⁿ ∈ F`. Then
`S` extends to a substructure containing `a`, with the `RV`- and `Γ`-parts unchanged, and the
embedding extends to it. -/
theorem exists_lift_ramified_finite {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F) {a : M RVSort.K} (ha0 : a ≠ 0)
    (haS : rvMap a ∈ S RVSort.RV) {n : ℕ} (hn : 0 < n) {c : F}
    (hac : a ^ n = (c : M RVSort.K))
    (hord : ∀ k : ℕ, 0 < k → k < n → ∀ d ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap d)) :
    LiftStepAt S e a := by
  classical
  have hT := rvMap_mem_RV_of_mem_adjoin_ramified_finite S hFS ha0 haS hn hac hord
  obtain ⟨E, hEsub, hE⟩ : ∃ E : Subfield (M RVSort.K),
      (∀ x ∈ (evalOn F.subtype a).range, x ∈ E) ∧
      (∀ x ∈ E, rvMap x ∈ S RVSort.RV) :=
    ⟨Subfield.closure _, fun _ hx => Subfield.subset_closure hx,
      fun _ hx => rvMap_mem_RV_of_mem_subfieldClosure hT hx⟩
  have hFE : F ≤ E := fun _ hx => hEsub _ (mem_evalOn_range_of_mem F a hx)
  have haE : a ∈ E := hEsub _ (self_mem_evalOn_range F a)
  -- the matching `n`-th root on the far side
  obtain ⟨b, hbn, hb⟩ := exists_pow_matching S e hFS ha0 haS hn hac
  have hab : liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype) (⟨a, haE⟩ : E))
      = rv (A := modelValSubring N) b := by
    rw [liftRvHom_rv]
    change toRV (embRV S e (rvMap a)) = rv (A := modelValSubring N) b
    rw [← hb, toRV_rvMap]
  have hmatch : ∀ (r : F) (i : ℕ),
      liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype)
          (Subfield.inclusion hFE r * (⟨a, haE⟩ : E) ^ i))
        = rv (A := modelValSubring N) (subfieldHom S e hFS r * b ^ i) := by
    intro r i
    rw [map_mul, map_pow, map_mul, map_pow, liftRvHom_compat S e hFE hE hFS, hab, ← map_pow,
      ← map_mul]
  have hmono : ∀ (r r' : F) (i i' : ℕ),
      ((modelValSubring M).comap E.subtype).valuation
          (Subfield.inclusion hFE r * (⟨a, haE⟩ : E) ^ i)
        < ((modelValSubring M).comap E.subtype).valuation
          (Subfield.inclusion hFE r' * (⟨a, haE⟩ : E) ^ i') →
      (modelValSubring N).valuation (subfieldHom S e hFS r * b ^ i)
        < (modelValSubring N).valuation (subfieldHom S e hFS r' * b ^ i') := fun r r' i i' =>
    (liftRvHom_valuation_lt_iff S e hE (hmatch r i) (hmatch r' i')).mp
  have hordE : ∀ k, 0 < k → k < n →
      ((modelValSubring M).comap E.subtype).valuation (⟨a, haE⟩ : E) ^ k
        ∉ ((modelValSubring M).comap E.subtype).valuation ''
          ((Subfield.inclusion hFE).fieldRange : Set E) := by
    rintro k hk hkn ⟨d, hd, hdeq⟩
    obtain ⟨r, rfl⟩ := hd
    refine hord k hk hkn (r : M RVSort.K) r.2 ?_
    rw [valMap_eq_iff_valuation]
    have h1 : ((modelValSubring M).comap E.subtype).valuation (Subfield.inclusion hFE r)
        = ((modelValSubring M).comap E.subtype).valuation ((⟨a, haE⟩ : E) ^ k) := by
      rw [map_pow]; exact hdeq
    rw [valuation_comap_eq_iff] at h1
    change (modelValSubring M).valuation (r : M RVSort.K)
      = (modelValSubring M).valuation ((⟨a, haE⟩ : E) ^ k : E) at h1
    rw [show (((⟨a, haE⟩ : E) ^ k : E) : M RVSort.K) = a ^ k from map_pow E.subtype _ k] at h1
    exact h1.symm
  have ha0E : (⟨a, haE⟩ : E) ≠ 0 := fun hc => ha0 (congrArg Subtype.val hc)
  have hca : (⟨a, haE⟩ : E) ^ n = Subfield.inclusion hFE c := by
    refine Subtype.ext ?_
    rw [show (((⟨a, haE⟩ : E) ^ n : E) : M RVSort.K) = a ^ n from map_pow E.subtype _ n, hac]
    rfl
  have H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS)
      (⟨a, haE⟩ : E) b := by
    refine rvTypeEq_of_ramified hn ?_ ?_ ?_ ha0E ?_ hca hbn
    · exact liftRvHom_compat S e hFE hE hFS
    · exact hmono
    · exact hab
    · exact hordE
  refine ⟨liftAdjoin S hFE hE hSF ⟨a, haE⟩, liftEmbedding S e hFE hE hFS hSF H, ?_,
    self_mem_liftIncl_range hFE ⟨a, haE⟩, rfl, rfl, ?_⟩
  · intro s x hx
    match s with
    | RVSort.K => exact mem_liftIncl_range_of_mem hFE ⟨a, haE⟩ (hSF x hx)
    | RVSort.RV => exact hx
    | RVSort.Γ => exact hx
  · intro s x hx hx'
    match s with
    | RVSort.K => exact liftEmbedding_apply_K_of_mem S e hFE hE hFS hSF H hx hx'
    | RVSort.RV => rfl
    | RVSort.Γ => rfl

end ManySorted.Language
