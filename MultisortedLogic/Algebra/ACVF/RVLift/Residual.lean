/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.RVLift.LiftStep
public import MultisortedLogic.Algebra.ACVF.RVLift.ResidueField
public import MultisortedLogic.Algebra.ACVF.ValuedField.Lift

/-!
# Lifting a leading term to the field sort: the residual case

The second of the four cases of steps `res(K(C)) = k(C)` and `v(K(C)) = Γ(C)` of Rideau-Kikuchi's
Proposition 2.1.10 (the routing step of `RVLift`). Here the element `a` of the field sort is a
**unit** of the valuation ring, and what controls the computation is its residue.

Two things have to be supplied, and both are about residues.

* **No new leading terms.** For `Q` over the coefficient subfield `F`, Rideau-Kikuchi's
  Proposition 2.1.5 (`ValuationSubring.exists_rv_eval_eq_of_residual`) factors `rv (Q a)` as
  `rv (q_{i₀}) · rv (R a)` with `R` over the valuation ring and `R a` a *unit*. Its leading term is
  therefore its residue, and the residue is `(res R)(res a)` — a polynomial in `res a` over the
  residues of `F`. So it is enough that the residues of the `RV`-part of the substructure form a
  **subring** of the residue field: that is `residueSubring`, and it is where the `RV`-sort axioms
  `rvAddRes`, `negRV` and `rvOne` are spent.
* **Non-vanishing.** Proposition 2.1.5 needs that no nonzero reduction of an `F`-polynomial vanishes
  at `res a`; in the transcendental case that holds for every degree, and in the algebraic case for
  every degree below that of the minimal polynomial of `res a`. The hypothesis has to be available
  both in the model and inside the subfield `E` that `Algebra/ACVF/RVLift/LiftStep.lean` works over,
  and `ValuationSubring.eval_map_residue_ne_zero_of_comap` moves it between the two without ever
  comparing the two residue fields.

The two cases differ in one further point. In the transcendental case the far-side element may be
*any* one with the matching leading term. In the algebraic case it has to be a root of the image
of the minimal polynomial as well, and `exists_root_matching` produces one: Proposition 2.1.5(2)
(`ValuationSubring.exists_root_residue_eq`), applied in the target to the image polynomial and to
the image of `res a` under the induced map of residue fields, gives a root with the prescribed
residue, and on units the residue determines the leading term. Neither case needs an elementary
extension of the target.

## Main statements

* `Language.residueSubring` : the residues of the `RV`-part of a substructure.
* `Language.rvMap_eval_mem_RV_of_residual` : the leading term of one `Q a` is already present.
* `Language.rvMap_mem_RV_of_mem_adjoin_residual`,
  `Language.rvMap_mem_RV_of_mem_adjoin_residual_alg` : hence so are all the leading terms of
  `F[a]`, transcendentally and algebraically.
* `Language.exists_root_matching` : the matching root on the far side.
* `Language.exists_lift_residual_transcendental`, `Language.exists_lift_residual_algebraic` : the
  extension of the substructure and of the embedding.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial IsLocalRing

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]
variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]

/-- Evaluating a polynomial whose coefficients lie in a subring at a point of that subring stays
inside it. -/
theorem eval_mem_subring {R : Type*} [CommRing R] (T : Subring R) {p : R[X]}
    (hp : ∀ i, p.coeff i ∈ T) {x : R} (hx : x ∈ T) : p.eval x ∈ T := by
  rw [Polynomial.eval_eq_sum_range]
  exact T.sum_mem fun i _ => T.mul_mem (hp i) (T.pow_mem hx i)

/-- Evaluating over the valuation ring and then including is including and then evaluating. -/
theorem eval_coe_valSubring {K : Type*} [Field K] (A : ValuationSubring K) (p : A[X]) (x : A) :
    ((p.eval x : A) : K) = (p.map A.subtype).eval ((x : A) : K) := by
  rw [Polynomial.eval_map]
  exact (Polynomial.eval₂_at_apply A.subtype x).symm

/-! ### The residues of the `RV`-part of a substructure -/

variable (S : rvLang.Substructure M)

/-- **The residues of the `RV`-part of a substructure form a subring of the residue field.**
The residue field sits inside the `RV` sort as the fiber of `val` over `0` together with `0`
(`Algebra/ACVF/RVLift/ResidueField.lean`), and a substructure's `RV`-part is closed under the
operations that `resEmbed` carries there — `1`, `*`, the residue addition and the negation. -/
def residueSubring : Subring (ResidueField (modelValSubring M)) where
  carrier := {ρ | ofRV (resEmbed (modelValSubring M) ρ) ∈ S RVSort.RV}
  zero_mem' :=
    show ofRV (resEmbed (modelValSubring M) 0) ∈ S RVSort.RV from by
      rw [resEmbed_zero, ofRV_zero]; exact zero_mem_RV
  one_mem' :=
    show ofRV (resEmbed (modelValSubring M) 1) ∈ S RVSort.RV from by
      rw [resEmbed_one, ofRV_one]; exact one_mem_RV
  mul_mem' := fun {ρ σ} hρ hσ =>
    show ofRV (resEmbed (modelValSubring M) (ρ * σ)) ∈ S RVSort.RV from by
      rw [resEmbed_mul, ofRV_mul]; exact mul_mem_RV hρ hσ
  add_mem' := fun {ρ σ} hρ hσ =>
    show ofRV (resEmbed (modelValSubring M) (ρ + σ)) ∈ S RVSort.RV from by
      rw [resEmbed_add, ofRV_add]; exact add_mem_RV hρ hσ
  neg_mem' := fun {ρ} hρ =>
    show ofRV (resEmbed (modelValSubring M) (-ρ)) ∈ S RVSort.RV from by
      rw [resEmbed_neg, ofRV_neg]; exact neg_mem_RV hρ

@[simp]
theorem mem_residueSubring {ρ : ResidueField (modelValSubring M)} :
    ρ ∈ residueSubring S
      ↔ ofRV (resEmbed (modelValSubring M) ρ) ∈ S RVSort.RV := Iff.rfl

variable {S}

/-- An element of the valuation ring whose leading term is in the `RV`-part has its residue in
the residue subring. -/
theorem residue_mem_residueSubring {x : modelValSubring M}
    (hx : rvMap ((x : modelValSubring M) : M RVSort.K) ∈ S RVSort.RV) :
    residue (modelValSubring M) x ∈ residueSubring S := by
  rw [mem_residueSubring]
  by_cases hu : IsUnit x
  · rw [resEmbed_residue hu, ofRV_rv]
    exact hx
  · rw [← residue_ne_zero_iff_isUnit, not_not] at hu
    rw [hu, resEmbed_zero, ofRV_zero]
    exact zero_mem_RV

/-- Conversely, on units the residue determines the leading term. -/
theorem rvMap_mem_RV_of_residue_mem {x : modelValSubring M} (hu : IsUnit x)
    (h : residue (modelValSubring M) x ∈ residueSubring S) :
    rvMap ((x : modelValSubring M) : M RVSort.K) ∈ S RVSort.RV := by
  rw [mem_residueSubring, resEmbed_residue hu, ofRV_rv] at h
  exact h

/-! ### No new leading terms -/

/-- **The core of the residual computation.** The leading term of `Q a`, for one polynomial `Q`
over `F` of degree below the degree of `res a` over the residues of `F`, is already in the
`RV`-part: Rideau-Kikuchi's Proposition 2.1.5 factors it as a coefficient's leading term times the
leading term of a *unit*, and the unit's leading term is its residue, which lies in
`residueSubring S`. -/
theorem rvMap_eval_mem_RV_of_residual {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K) {a : modelValSubring M} {n : ℕ}
    (haS : rvMap ((a : modelValSubring M) : M RVSort.K) ∈ S RVSort.RV)
    (hdeg : ∀ R : (modelValSubring M)[X],
      (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F) → R.natDegree < n →
      R.map (residue (modelValSubring M)) ≠ 0 →
      (R.map (residue (modelValSubring M))).eval (residue (modelValSubring M) a) ≠ 0)
    (p : F[X]) (hpn : p.natDegree < n) :
    rvMap (evalOn F.subtype ((a : modelValSubring M) : M RVSort.K) p)
      ∈ S RVSort.RV := by
  have hev : evalOn F.subtype ((a : modelValSubring M) : M RVSort.K) p
      = (p.map F.subtype).eval ((a : modelValSubring M) : M RVSort.K) :=
    (Polynomial.eval_map _ _).symm
  have hQF : ∀ i, (p.map F.subtype).coeff i ∈ F := by
    intro i
    rw [Polynomial.coeff_map]
    exact (p.coeff i).2
  by_cases hQ0 : p.map F.subtype = 0
  · rw [hev, hQ0, Polynomial.eval_zero, model_rv_zero]
    exact zero_mem_RV
  have hQn : (p.map F.subtype).natDegree < n := by rwa [Polynomial.natDegree_map]
  obtain ⟨i₀, R, hi₀, -, hc, hunit, -, hrv⟩ :=
    exists_rv_eval_eq_of_residual (A := modelValSubring M) (F := F) (n := n) hQ0 hQF hQn hdeg
  -- the residue of `R a` lies in the residue subring, so `R a` has its leading term in `S`
  have hRcoeff : ∀ i, residue (modelValSubring M) (R.coeff i) ∈ residueSubring S := by
    intro i
    refine residue_mem_residueSubring (rvMap_mem_RV (hFS _ ?_))
    rw [hc i]
    exact F.mul_mem (F.inv_mem (hQF i₀)) (hQF i)
  have hevres : residue (modelValSubring M) (R.eval a)
      = (R.map (residue (modelValSubring M))).eval (residue (modelValSubring M) a) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hres : residue (modelValSubring M) (R.eval a) ∈ residueSubring S := by
    rw [hevres]
    refine eval_mem_subring _ (fun i => ?_) (residue_mem_residueSubring haS)
    rw [Polynomial.coeff_map]
    exact hRcoeff i
  have hRunit := rvMap_mem_RV_of_residue_mem hunit hres
  have hmul : rvMap ((p.map F.subtype).eval ((a : modelValSubring M) : M RVSort.K))
      = rvMap ((p.map F.subtype).coeff i₀)
        * rvMap (((R.eval a : modelValSubring M) : M RVSort.K)) := by
    rw [← ofRV_rv, hrv, ofRV_mul, ofRV_rv, ofRV_rv]
  rw [hev, hmul]
  exact mul_mem_RV (rvMap_mem_RV (hFS _ (hQF i₀))) hRunit

/-- **The leading terms of `F[a]` are already present**, when `a` is a unit of the valuation ring
whose residue is transcendental over the residues of `F` — in the strong form that no nonzero
reduction of an `F`-polynomial over the valuation ring vanishes at `res a`. -/
theorem rvMap_mem_RV_of_mem_adjoin_residual {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K) {a : modelValSubring M}
    (haS : rvMap ((a : modelValSubring M) : M RVSort.K) ∈ S RVSort.RV)
    (htr : ∀ R : (modelValSubring M)[X],
      (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F) →
      R.map (residue (modelValSubring M)) ≠ 0 →
      (R.map (residue (modelValSubring M))).eval (residue (modelValSubring M) a) ≠ 0) :
    ∀ x ∈ (evalOn F.subtype ((a : modelValSubring M) : M RVSort.K)).range,
      rvMap x ∈ S RVSort.RV := by
  intro x hx
  obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hx
  exact rvMap_eval_mem_RV_of_residual (n := p.natDegree + 1) hFS haS
    (fun R hRF _ hRne => htr R hRF hRne) p (Nat.lt_succ_self _)

/-- **The leading terms of `F[a]` are already present**, when `a` is a unit of the valuation ring
that is a root of a monic `P` over `F` of degree `n`, and no nonzero reduction of an
`F`-polynomial of degree `< n` vanishes at `res a` — that is, when `res a` is algebraic of degree
`n` over the residues of `F`. Reduction modulo `P` brings every element of `F[a]` into a degree
below `n`, where the residual computation applies. -/
theorem rvMap_mem_RV_of_mem_adjoin_residual_alg {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K) {a : modelValSubring M} {n : ℕ}
    (haS : rvMap ((a : modelValSubring M) : M RVSort.K) ∈ S RVSort.RV)
    {P : F[X]} (hP : P.Monic) (hPn : P.natDegree = n)
    (hPa : evalOn F.subtype ((a : modelValSubring M) : M RVSort.K) P = 0)
    (hdeg : ∀ R : (modelValSubring M)[X],
      (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F) → R.natDegree < n →
      R.map (residue (modelValSubring M)) ≠ 0 →
      (R.map (residue (modelValSubring M))).eval (residue (modelValSubring M) a) ≠ 0) :
    ∀ x ∈ (evalOn F.subtype ((a : modelValSubring M) : M RVSort.K)).range,
      rvMap x ∈ S RVSort.RV := by
  intro x hx
  obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hx
  have hred : evalOn F.subtype ((a : modelValSubring M) : M RVSort.K) p
      = evalOn F.subtype ((a : modelValSubring M) : M RVSort.K) (p %ₘ P) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div p P]
    rw [map_add, map_mul, hPa, zero_mul, add_zero]
  rw [hred]
  by_cases hq0 : p %ₘ P = 0
  · rw [hq0, map_zero, model_rv_zero]
    exact zero_mem_RV
  · exact rvMap_eval_mem_RV_of_residual hFS haS hdeg _
      (hPn ▸ Polynomial.natDegree_lt_natDegree hq0 (Polynomial.degree_modByMonic_lt p hP))

/-! ### The extension of the embedding -/

variable (S)
variable (e : (fun s => ↥(S s)) ↪[rvLang] N)

/-- **Step `res(K(C)) = k(C)`, the transcendental case.** Let `S` be a substructure whose field part
is a subfield `F`, and let `a` be a unit of the valuation ring whose leading term is already in the
`RV`-part of `S` and whose residue is transcendental over the residues of `F`. Then `S` extends to a
substructure containing `a`, with the `RV`- and `Γ`-parts unchanged, and the embedding extends to
it. No elementary extension of the target is needed: the matching element on the far side is any one
with the matching leading term, and the induced map of residue fields carries the computation. -/
theorem exists_lift_residual_transcendental {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F) {a : modelValSubring M} (hav : IsUnit a)
    (haS : rvMap ((a : modelValSubring M) : M RVSort.K) ∈ S RVSort.RV)
    (htr : ∀ R : (modelValSubring M)[X],
      (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F) →
      R.map (residue (modelValSubring M)) ≠ 0 →
      (R.map (residue (modelValSubring M))).eval (residue (modelValSubring M) a) ≠ 0) :
    LiftStepAt S e ((a : modelValSubring M) : M RVSort.K) := by
  classical
  have hav' : (modelValSubring M).valuation ((a : modelValSubring M) : M RVSort.K) = 1 :=
    ((modelValSubring M).valuation_eq_one_iff a).mp hav
  -- the subring `F[a]` and the subfield it generates
  have hT := rvMap_mem_RV_of_mem_adjoin_residual (S := S) hFS (a := a) haS htr
  -- the subfield generated by `F[a]`, kept opaque: only these two properties of it are used
  obtain ⟨E, hEsub, hE⟩ : ∃ E : Subfield (M RVSort.K),
      (∀ x ∈ (evalOn F.subtype ((a : modelValSubring M) : M RVSort.K)).range, x ∈ E) ∧
      (∀ x ∈ E, rvMap x ∈ S RVSort.RV) :=
    ⟨Subfield.closure _, fun _ hx => Subfield.subset_closure hx,
      fun _ hx => rvMap_mem_RV_of_mem_subfieldClosure hT hx⟩
  have hFE : F ≤ E := fun _ hx => hEsub _ (mem_evalOn_range_of_mem F _ hx)
  have haE : ((a : modelValSubring M) : M RVSort.K) ∈ E :=
    hEsub _ (self_mem_evalOn_range F _)
  have haEmem : (⟨((a : modelValSubring M) : M RVSort.K), haE⟩ : E)
      ∈ (modelValSubring M).comap E.subtype := mem_comap.mpr a.2
  have hcomapa : comapHom (modelValSubring M) (f := E.subtype)
      ⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩ = a := Subtype.ext rfl
  -- the matching element on the far side, which is again a unit
  obtain ⟨b, hb⟩ := model_rv_surjective (M := N)
    (embRV S e (rvMap ((a : modelValSubring M) : M RVSort.K)))
  have hbval : valMap (rvMap b) = 0 := by
    rw [hb]
    exact valMap_embRV_eq_zero S e haS (valMap_eq_zero_iff_valuation_eq_one.mpr hav')
  have hbA : b ∈ modelValSubring N :=
    (modelValSubring N).mem_of_valuation_le_one b
      (le_of_eq (valMap_eq_zero_iff_valuation_eq_one.mp hbval))
  have hab : liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype)
        (⟨((a : modelValSubring M) : M RVSort.K), haE⟩ : E))
      = rv (A := modelValSubring N) b := by
    rw [liftRvHom_rv]
    change toRV (embRV S e (rvMap ((a : modelValSubring M) : M RVSort.K)))
      = rv (A := modelValSubring N) b
    rw [← hb, toRV_rvMap]
  -- the induced map of residue fields
  have hmonoG := liftRvHom_rvVal_lt_iff S e hE
  have haddG := liftRvHom_rvAdd S e hE
  -- the non-vanishing hypothesis, read inside `E`
  have hM : ∀ R : (modelValSubring M)[X],
      (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F.toSubring) →
      R.map (residue (modelValSubring M)) ≠ 0 →
      (R.map (residue (modelValSubring M))).eval (residue (modelValSubring M)
        (comapHom (modelValSubring M) (f := E.subtype)
          ⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩)) ≠ 0 := by
    intro R hRT hRz
    rw [hcomapa]
    exact htr R hRT hRz
  have hdegE : ∀ RQ : ((modelValSubring M).comap E.subtype)[X],
      (∀ i, ((RQ.coeff i : (modelValSubring M).comap E.subtype) : E)
        ∈ (Subfield.inclusion hFE).fieldRange) →
      RQ.map (residue ((modelValSubring M).comap E.subtype)) ≠ 0 →
      (RQ.map (residue ((modelValSubring M).comap E.subtype))).eval
        (residue ((modelValSubring M).comap E.subtype)
          ⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩) ≠ 0 := by
    intro RQ hRQ hRne
    refine eval_map_residue_ne_zero_of_comap (modelValSubring M) F.toSubring _
      (n := RQ.natDegree + 1) (fun R hRT _ hRz => hM R hRT hRz) RQ (fun i => ?_)
      (Nat.lt_succ_self _) hRne
    obtain ⟨r, hr⟩ := hRQ i
    exact hr ▸ r.2
  -- the leading-term type of `a` over `F` is matched by `b`
  have H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS)
      (⟨((a : modelValSubring M) : M RVSort.K), haE⟩ : E) b := by
    intro Q
    refine rv_eval_eq_of_residual_transfer
      (a := ⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩) (b := ⟨b, hbA⟩)
      (n := Q.natDegree + 1) (θ := resRingHom (liftRvHom S e hE) hmonoG haddG)
      ?_ ?_ ?_ ?_ ?_ ?_ Q (Nat.lt_succ_self _)
    · exact fun _ _ h => resMap_residue hmonoG h
    · exact fun _ _ hu hv h => rv_eq_of_resMap_residue hmonoG hu hv h
    · exact fun r r' => (liftRvHom_valuation_lt_iff S e hE (liftRvHom_compat S e hFE hE hFS r)
        (liftRvHom_compat S e hFE hE hFS r')).mpr
    · exact liftRvHom_compat S e hFE hE hFS
    · exact hab
    · exact fun RQ hRQ _ hRne => hdegE RQ hRQ hRne
  refine ⟨liftAdjoin S hFE hE hSF ⟨_, haE⟩, liftEmbedding S e hFE hE hFS hSF H, ?_,
    self_mem_liftIncl_range hFE ⟨_, haE⟩, rfl, rfl, ?_⟩
  · intro s x hx
    match s with
    | RVSort.K => exact mem_liftIncl_range_of_mem hFE ⟨_, haE⟩ (hSF x hx)
    | RVSort.RV => exact hx
    | RVSort.Γ => exact hx
  · intro s x hx hx'
    match s with
    | RVSort.K => exact liftEmbedding_apply_K_of_mem S e hFE hE hFS hSF H hx hx'
    | RVSort.RV => rfl
    | RVSort.Γ => rfl

/-! ### The matching root on the far side

The algebraic case needs more of the far-side element than a matching leading term: it has to be
a root of the image of the minimal polynomial. Both are supplied at once by Rideau-Kikuchi's
Proposition 2.1.5(2) (`ValuationSubring.exists_root_residue_eq`) applied in the target, to the image
polynomial and to the image of the residue under the induced map of residue fields. -/

/-- **The matching root.** If `a` is a unit of the valuation ring of `E` and a root of a monic
polynomial `P` over the coefficient field whose coefficients are integral, then the target
contains a root of the image of `P` with the matching leading term. -/
theorem exists_root_matching {F E : Subfield (M RVSort.K)} (hFE : F ≤ E)
    (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    {a : ((modelValSubring M).comap E.subtype)} (hau : IsUnit a)
    {P : F[X]} (hP : P.Monic)
    (hPint : ∀ i, ((P.coeff i : F) : M RVSort.K) ∈ modelValSubring M)
    (hPa : evalOn (Subfield.inclusion hFE)
      ((a : ((modelValSubring M).comap E.subtype)) : E) P = 0) :
    ∃ b : modelValSubring N,
      evalOn' (subfieldHom S e hFS) ((b : modelValSubring N) : N RVSort.K) P = 0 ∧
      liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype)
          ((a : ((modelValSubring M).comap E.subtype)) : E))
        = rv (A := modelValSubring N) ((b : modelValSubring N) : N RVSort.K) := by
  classical
  have hmonoG := liftRvHom_rvVal_lt_iff S e hE
  have haddG := liftRvHom_rvAdd S e hE
  -- the polynomial over the valuation ring of `E`
  have hPEc : (↑(P.map (Subfield.inclusion hFE)).coeffs : Set E)
      ⊆ (((modelValSubring M).comap E.subtype).toSubring : Set E) := by
    intro x hx
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [Polynomial.coeff_map]
    exact mem_comap.mpr (hPint i)
  set PE : (((modelValSubring M).comap E.subtype))[X] :=
    (P.map (Subfield.inclusion hFE)).toSubring _ hPEc with hPEdef
  have hPEmap : PE.map ((modelValSubring M).comap E.subtype).subtype
      = P.map (Subfield.inclusion hFE) := Polynomial.map_toSubring _ _ _
  -- the polynomial over the valuation ring of the target
  have hPNc : (↑(P.map (subfieldHom S e hFS)).coeffs : Set (N RVSort.K))
      ⊆ ((modelValSubring N).toSubring : Set (N RVSort.K)) := by
    intro x hx
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [Polynomial.coeff_map]
    exact (modelValSubring N).mem_of_valuation_le_one _
      (valuation_subHom_le_one S e (hFS _ (P.coeff i).2)
        (((modelValSubring M).valuation_le_one_iff _).mpr (hPint i)))
  set PN : ((modelValSubring N))[X] :=
    (P.map (subfieldHom S e hFS)).toSubring _ hPNc with hPNdef
  have hPNmap : PN.map (modelValSubring N).subtype = P.map (subfieldHom S e hFS) :=
    Polynomial.map_toSubring _ _ _
  have hPNmonic : PN.Monic := (Polynomial.monic_toSubring _ _ _).mpr (hP.map _)
  -- `a` is a root of `PE`
  have hPEa : PE.eval a = 0 := by
    refine Subtype.ext ?_
    rw [ZeroMemClass.coe_zero, eval_coe_valSubring, hPEmap, Polynomial.eval_map]
    exact hPa
  -- the reduction of `PN` vanishes at the image residue
  have hcoefres : ∀ i, resMap (liftRvHom S e hE) (residue _ (PE.coeff i))
      = residue (modelValSubring N) (PN.coeff i) := by
    intro i
    refine resMap_residue hmonoG ?_
    have hc1 : ((PE.coeff i : ((modelValSubring M).comap E.subtype)) : E)
        = Subfield.inclusion hFE (P.coeff i) := by
      rw [hPEdef, Polynomial.coeff_toSubring, Polynomial.coeff_map]
    have hc2 : ((PN.coeff i : modelValSubring N) : N RVSort.K)
        = subfieldHom S e hFS (P.coeff i) := by
      rw [hPNdef, Polynomial.coeff_toSubring, Polynomial.coeff_map]
    rw [hc1, hc2]
    exact liftRvHom_compat S e hFE hE hFS (P.coeff i)
  have hPNres : PN.map (residue (modelValSubring N))
      = (PE.map (residue ((modelValSubring M).comap E.subtype))).map
        (resRingHom (liftRvHom S e hE) hmonoG haddG) := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map]
    exact (hcoefres i).symm
  have hPEres0 : (PE.map (residue ((modelValSubring M).comap E.subtype))).eval
      (residue ((modelValSubring M).comap E.subtype) a) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hPEa, map_zero]
  have hzero : (PN.map (residue (modelValSubring N))).eval
      (resRingHom (liftRvHom S e hE) hmonoG haddG
        (residue ((modelValSubring M).comap E.subtype) a)) = 0 := by
    rw [hPNres, Polynomial.eval_map, Polynomial.eval₂_at_apply, hPEres0, map_zero]
  -- the root
  obtain ⟨b, hbroot, hbres⟩ := exists_root_residue_eq (A := modelValSubring N) hPNmonic
    (by rw [hPNmap]; exact IsAlgClosed.splits _) hzero
  refine ⟨b, ?_, ?_⟩
  · have h1 : ((PN.eval b : modelValSubring N) : N RVSort.K) = 0 := by
      rw [hbroot, ZeroMemClass.coe_zero]
    rw [eval_coe_valSubring, hPNmap, Polynomial.eval_map] at h1
    exact h1
  · refine rv_eq_of_resMap_residue hmonoG hau ?_ hbres.symm
    rw [← residue_ne_zero_iff_isUnit, hbres]
    refine fun hc => (residue_ne_zero_iff_isUnit a).mpr hau ?_
    exact (map_eq_zero_iff _
      (resRingHom (liftRvHom S e hE) hmonoG haddG).injective).mp hc

/-- **Step `res(K(C)) = k(C)`, the algebraic case.** Let `S` be a substructure whose field part is a
subfield `F`, and let `a` be a unit of the valuation ring whose leading term is already in the
`RV`-part of `S` and whose residue is algebraic of degree `n` over the residues of `F`, witnessed by
an integral monic `P` over `F` of degree `n` vanishing at `a`. Then `S` extends to a substructure
containing `a`, with the `RV`- and `Γ`-parts unchanged, and the embedding extends to it. -/
theorem exists_lift_residual_algebraic {F : Subfield (M RVSort.K)}
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F) {a : modelValSubring M} (hav : IsUnit a)
    (haS : rvMap ((a : modelValSubring M) : M RVSort.K) ∈ S RVSort.RV)
    {n : ℕ} {P : F[X]} (hP : P.Monic) (hPn : P.natDegree = n)
    (hPint : ∀ i, ((P.coeff i : F) : M RVSort.K) ∈ modelValSubring M)
    (hPa : evalOn F.subtype ((a : modelValSubring M) : M RVSort.K) P = 0)
    (hdeg : ∀ R : (modelValSubring M)[X],
      (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F) → R.natDegree < n →
      R.map (residue (modelValSubring M)) ≠ 0 →
      (R.map (residue (modelValSubring M))).eval (residue (modelValSubring M) a) ≠ 0) :
    LiftStepAt S e ((a : modelValSubring M) : M RVSort.K) := by
  classical
  -- the subring `F[a]` and the subfield it generates
  have hT := rvMap_mem_RV_of_mem_adjoin_residual_alg (S := S) hFS (a := a) haS hP hPn hPa hdeg
  obtain ⟨E, hEsub, hE⟩ : ∃ E : Subfield (M RVSort.K),
      (∀ x ∈ (evalOn F.subtype ((a : modelValSubring M) : M RVSort.K)).range, x ∈ E) ∧
      (∀ x ∈ E, rvMap x ∈ S RVSort.RV) :=
    ⟨Subfield.closure _, fun _ hx => Subfield.subset_closure hx,
      fun _ hx => rvMap_mem_RV_of_mem_subfieldClosure hT hx⟩
  have hFE : F ≤ E := fun _ hx => hEsub _ (mem_evalOn_range_of_mem F _ hx)
  have haE : ((a : modelValSubring M) : M RVSort.K) ∈ E :=
    hEsub _ (self_mem_evalOn_range F _)
  have haEmem : (⟨((a : modelValSubring M) : M RVSort.K), haE⟩ : E)
      ∈ (modelValSubring M).comap E.subtype := mem_comap.mpr a.2
  have hcomapa : comapHom (modelValSubring M) (f := E.subtype)
      ⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩ = a := Subtype.ext rfl
  have hauE : IsUnit (⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩ :
      ((modelValSubring M).comap E.subtype)) := by
    rw [← isUnit_comapHom_iff (modelValSubring M), hcomapa]
    exact hav
  -- the root `a` read inside `E`
  have hcomp : E.subtype.comp (Subfield.inclusion hFE) = F.subtype := RingHom.ext fun _ => rfl
  have h1 : E.subtype (evalOn (Subfield.inclusion hFE)
      (⟨((a : modelValSubring M) : M RVSort.K), haE⟩ : E) P)
      = evalOn F.subtype ((a : modelValSubring M) : M RVSort.K) P := by
    have h2 := Polynomial.hom_eval₂ P (Subfield.inclusion hFE) E.subtype
      (⟨((a : modelValSubring M) : M RVSort.K), haE⟩ : E)
    rw [hcomp] at h2
    exact h2
  have hPaE : evalOn (Subfield.inclusion hFE)
      ((⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩ :
        ((modelValSubring M).comap E.subtype)) : E) P = 0 := Subtype.ext (h1.trans hPa)
  -- the matching root on the far side
  obtain ⟨b, hPb, hab⟩ := exists_root_matching S e hFE hE hFS hauE hP hPint hPaE
  -- the non-vanishing hypothesis, read inside `E`
  have hM : ∀ R : (modelValSubring M)[X],
      (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F.toSubring) → R.natDegree < n →
      R.map (residue (modelValSubring M)) ≠ 0 →
      (R.map (residue (modelValSubring M))).eval (residue (modelValSubring M)
        (comapHom (modelValSubring M) (f := E.subtype)
          ⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩)) ≠ 0 := by
    intro R hRT hRn hRz
    rw [hcomapa]
    exact hdeg R hRT hRn hRz
  have hdegE : ∀ RQ : ((modelValSubring M).comap E.subtype)[X],
      (∀ i, ((RQ.coeff i : (modelValSubring M).comap E.subtype) : E)
        ∈ (Subfield.inclusion hFE).fieldRange) → RQ.natDegree < n →
      RQ.map (residue ((modelValSubring M).comap E.subtype)) ≠ 0 →
      (RQ.map (residue ((modelValSubring M).comap E.subtype))).eval
        (residue ((modelValSubring M).comap E.subtype)
          ⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩) ≠ 0 := by
    intro RQ hRQ hRn hRne
    refine eval_map_residue_ne_zero_of_comap (modelValSubring M) F.toSubring _ hM RQ
      (fun i => ?_) hRn hRne
    obtain ⟨r, hr⟩ := hRQ i
    exact hr ▸ r.2
  have hmonoG := liftRvHom_rvVal_lt_iff S e hE
  have haddG := liftRvHom_rvAdd S e hE
  have H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS)
      (⟨((a : modelValSubring M) : M RVSort.K), haE⟩ : E)
      ((b : modelValSubring N) : N RVSort.K) := by
    refine rvTypeEq_of_residual
      (a := ⟨⟨((a : modelValSubring M) : M RVSort.K), haE⟩, haEmem⟩) (b := b)
      (P := P) hP hPn hPaE hPb (θ := resRingHom (liftRvHom S e hE) hmonoG haddG)
      ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun _ _ h => resMap_residue hmonoG h
    · exact fun _ _ hu hv h => rv_eq_of_resMap_residue hmonoG hu hv h
    · exact fun r r' => (liftRvHom_valuation_lt_iff S e hE (liftRvHom_compat S e hFE hE hFS r)
        (liftRvHom_compat S e hFE hE hFS r')).mpr
    · exact liftRvHom_compat S e hFE hE hFS
    · exact hab
    · exact hdegE
  refine ⟨liftAdjoin S hFE hE hSF ⟨_, haE⟩, liftEmbedding S e hFE hE hFS hSF H, ?_,
    self_mem_liftIncl_range hFE ⟨_, haE⟩, rfl, rfl, ?_⟩
  · intro s x hx
    match s with
    | RVSort.K => exact mem_liftIncl_range_of_mem hFE ⟨_, haE⟩ (hSF x hx)
    | RVSort.RV => exact hx
    | RVSort.Γ => exact hx
  · intro s x hx hx'
    match s with
    | RVSort.K => exact liftEmbedding_apply_K_of_mem S e hFE hE hFS hSF H hx hx'
    | RVSort.RV => rfl
    | RVSort.Γ => rfl

end ManySorted.Language
