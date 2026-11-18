/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.RVLift.Ramified
public import MultisortedLogic.Algebra.ACVF.RVLift.Residual

/-!
# Lifting a leading term to the field sort: choosing the element

The four cases of `Algebra/ACVF/RVLift/Ramified.lean` and `Algebra/ACVF/RVLift/Residual.lean` take
the element `a` of the field sort as input, together with the hypothesis that puts it in one of the
four positions relative to the coefficient subfield `F`. This file *produces* `a` from a leading
term `ξ` of the `RV`-part that is not yet a leading term of `F`.

For the residual cases that means knowing the residue field of `F` inside the residue field of the
model, and the least degree of a monic equation for `res ξ` over it.

* `fieldValRing F` is the valuation ring of `F`, as a subring of the model's;
* `residueSubfield F` is its residue field, as a subfield of `ResidueField (modelValSubring M)` —
  a *subfield* because `F` is closed under inversion and a residue is nonzero exactly when its
  representative is a unit;
* `ResidueMonicDeg F ρ n` says `ρ` satisfies a monic equation of degree `n` over
  `residueSubfield F`, and at the least such degree `exists_residual_root` produces exactly the
  data the algebraic case asks for: an integral monic `P` over `F` of that degree, a root `a` of
  it with the prescribed residue, and the non-vanishing of everything of smaller degree.

Mathlib's `Polynomial.lifts_and_degree_eq_and_monic` does the lifting of the monic equation from
the residue field back to `F`, so no polynomial has to be assembled coefficient by coefficient.

The routing itself is the order `n` of `val ξ` over the values of `F`. Infinite order is the
ramified case of infinite order. At finite order `n`, either `ξⁿ` is already a leading term of
`F` — and then `ξ` is lifted by an `n`-th root, which `ValuationSubring.exists_pow_eq_rv_eq`
produces with the *leading term* prescribed, not merely the value — or it is not, and then
scaling by a coefficient of the same value lands in the residue fiber, where the residue is
either transcendental or algebraic over the residues of `F`.

## Main definitions

* `Language.fieldValRing`, `Language.residueSubfield`, `Language.ResidueMonicDeg`.
* `Language.LiftStepConclusion` : the conclusion of a routing step.

## Main statements

* `Language.exists_residual_root` : the data the residual algebraic case asks for.
* `Language.exists_lift_residual_of_unit` : the residual routing.
* `Language.exists_lift_of_notMem` : **the routing**, all four cases.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial IsLocalRing

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]

/-! ### The residue field of a subfield of the field sort -/

variable (F : Subfield (M RVSort.K))

/-- The valuation ring of a subfield of the field sort, as a subring of the model's valuation
ring. -/
def fieldValRing : Subring (modelValSubring M) where
  carrier := {x | ((x : modelValSubring M) : M RVSort.K) ∈ F}
  zero_mem' := F.zero_mem
  one_mem' := F.one_mem
  add_mem' hx hy := F.add_mem hx hy
  neg_mem' hx := F.neg_mem hx
  mul_mem' hx hy := F.mul_mem hx hy

@[simp]
theorem mem_fieldValRing {x : modelValSubring M} :
    x ∈ fieldValRing F ↔ ((x : modelValSubring M) : M RVSort.K) ∈ F := Iff.rfl

/-- The valuation ring of `F`, mapped into `F`. -/
def valRingToField : fieldValRing F →+* F where
  toFun x := ⟨(((x : modelValSubring M)) : M RVSort.K), x.2⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_valRingToField (x : fieldValRing F) :
    ((valRingToField F x : F) : M RVSort.K) = ((x : modelValSubring M) : M RVSort.K) := rfl

/-- The residue map of `F`, as a ring homomorphism into the residue field of the model. -/
noncomputable def fieldResidue : fieldValRing F →+* ResidueField (modelValSubring M) :=
  (residue (modelValSubring M)).comp (fieldValRing F).subtype

@[simp]
theorem fieldResidue_apply (x : fieldValRing F) :
    fieldResidue F x = residue (modelValSubring M) (x : modelValSubring M) := rfl

/-- **The residue field of a subfield of the field sort.** It is a subfield and not merely a
subring because `F` is closed under inversion and a residue is nonzero exactly when its
representative is a unit of the valuation ring. -/
noncomputable def residueSubfield : Subfield (ResidueField (modelValSubring M)) :=
  Subring.toSubfield (fieldResidue F).range (by
    rintro ρ ⟨x, rfl⟩
    by_cases h0 : fieldResidue F x = 0
    · rw [h0, inv_zero]
      exact ⟨0, map_zero _⟩
    · have hu : IsUnit ((x : fieldValRing F) : modelValSubring M) :=
        (residue_ne_zero_iff_isUnit _).mp h0
      have hval : (modelValSubring M).valuation
          (((x : fieldValRing F) : modelValSubring M) : M RVSort.K) = 1 :=
        ((modelValSubring M).valuation_eq_one_iff _).mp hu
      have hinv : ((((x : fieldValRing F) : modelValSubring M) : M RVSort.K))⁻¹
          ∈ modelValSubring M := by
        refine (modelValSubring M).mem_of_valuation_le_one _ (le_of_eq ?_)
        rw [map_inv₀, hval, inv_one]
      have hx0 : (((x : fieldValRing F) : modelValSubring M) : M RVSort.K) ≠ 0 := by
        intro hc
        rw [hc, map_zero] at hval
        exact zero_ne_one hval
      have hmul : (⟨_, hinv⟩ : modelValSubring M)
          * ((x : fieldValRing F) : modelValSubring M) = 1 :=
        Subtype.ext (inv_mul_cancel₀ hx0)
      refine ⟨⟨⟨_, hinv⟩, F.inv_mem x.2⟩, eq_inv_of_mul_eq_one_left ?_⟩
      rw [fieldResidue_apply, fieldResidue_apply, ← map_mul, hmul, map_one])

theorem mem_residueSubfield {ρ : ResidueField (modelValSubring M)} :
    ρ ∈ residueSubfield F ↔ ∃ x : fieldValRing F, fieldResidue F x = ρ := Iff.rfl

theorem residue_mem_residueSubfield (x : fieldValRing F) :
    residue (modelValSubring M) (x : modelValSubring M) ∈ residueSubfield F := ⟨x, rfl⟩

/-! ### The degree of a residue over the residues of `F` -/

/-- `ρ` satisfies a monic equation of degree `n` over the residues of `F`. -/
def ResidueMonicDeg (ρ : ResidueField (modelValSubring M)) (n : ℕ) : Prop :=
  ∃ q : (ResidueField (modelValSubring M))[X], q.Monic ∧ q.natDegree = n ∧
    (∀ i, q.coeff i ∈ residueSubfield F) ∧ q.eval ρ = 0

/-- A nonzero reduction of an `F`-polynomial vanishing at `ρ`, normalized to a *monic* equation
over the residues of `F` of the same degree. -/
theorem residueMonicDeg_of_eval_eq_zero {ρ : ResidueField (modelValSubring M)}
    {R : (modelValSubring M)[X]}
    (hRF : ∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F)
    (hRne : R.map (residue (modelValSubring M)) ≠ 0)
    (hRz : (R.map (residue (modelValSubring M))).eval ρ = 0) :
    ResidueMonicDeg F ρ (R.map (residue (modelValSubring M))).natDegree := by
  have hrc : ∀ i, (R.map (residue (modelValSubring M))).coeff i ∈ residueSubfield F := by
    intro i
    rw [Polynomial.coeff_map]
    exact residue_mem_residueSubfield F ⟨R.coeff i, hRF i⟩
  have hlead : (R.map (residue (modelValSubring M))).leadingCoeff ∈ residueSubfield F := hrc _
  refine ⟨R.map (residue (modelValSubring M))
      * C (R.map (residue (modelValSubring M))).leadingCoeff⁻¹,
    Polynomial.monic_mul_leadingCoeff_inv hRne,
    Polynomial.natDegree_mul_leadingCoeff_inv _ hRne, fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_mul_C]
    exact (residueSubfield F).mul_mem (hrc i) ((residueSubfield F).inv_mem hlead)
  · rw [Polynomial.eval_mul, hRz, zero_mul]

/-- **The data the residual algebraic case asks for.** If `ρ` satisfies a monic equation over the
residues of `F` at all, then at the least such degree `n` there are an integral monic `P` over `F`
of degree `n` and a root `a` of it with residue `ρ`, and no nonzero reduction of an
`F`-polynomial of degree `< n` vanishes at `ρ`.

The monic equation is lifted from the residue field back to `F` by
`Polynomial.lifts_and_degree_eq_and_monic`, and the root is produced by Proposition 2.1.5(2). -/
theorem exists_residual_root {ρ : ResidueField (modelValSubring M)}
    (halg : ∃ n, ResidueMonicDeg F ρ n) :
    ∃ (n : ℕ) (P : F[X]) (a : modelValSubring M), P.Monic ∧ P.natDegree = n ∧
      (∀ i, ((P.coeff i : F) : M RVSort.K) ∈ modelValSubring M) ∧
      residue (modelValSubring M) a = ρ ∧
      evalOn F.subtype ((a : modelValSubring M) : M RVSort.K) P = 0 ∧
      (∀ R : (modelValSubring M)[X],
        (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F) → R.natDegree < n →
        R.map (residue (modelValSubring M)) ≠ 0 →
        (R.map (residue (modelValSubring M))).eval ρ ≠ 0) := by
  classical
  obtain ⟨q, hqm, hqd, hqc, hqe⟩ := Nat.find_spec halg
  -- lift the monic equation from the residue field back to the valuation ring of `F`
  have hlifts : q ∈ Polynomial.lifts (fieldResidue F) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun i => (mem_residueSubfield F).mp (hqc i)
  obtain ⟨P₀, hP₀map, hP₀deg, hP₀m⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hqm
  have hP₀d : P₀.natDegree = Nat.find halg := by
    rw [Polynomial.natDegree_eq_of_degree_eq hP₀deg, hqd]
  -- read it over `F` and over the valuation ring of the model
  have hPm : (P₀.map (valRingToField F)).Monic := hP₀m.map _
  have hPAm : (P₀.map (fieldValRing F).subtype).Monic := hP₀m.map _
  have hPAres : (P₀.map (fieldValRing F).subtype).map (residue (modelValSubring M)) = q := by
    rw [Polynomial.map_map]
    exact hP₀map
  -- the root
  obtain ⟨a, hPAroot, hares⟩ := exists_root_residue_eq (A := modelValSubring M) (γ := ρ) hPAm
    (IsAlgClosed.splits _) (by rw [hPAres]; exact hqe)
  -- the two readings of `P₀` agree after including into the field sort
  have hcomp : F.subtype.comp (valRingToField F)
      = (modelValSubring M).subtype.comp (fieldValRing F).subtype := RingHom.ext fun _ => rfl
  have hPmap : (P₀.map (valRingToField F)).map F.subtype
      = (P₀.map (fieldValRing F).subtype).map (modelValSubring M).subtype := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomp]
  refine ⟨Nat.find halg, P₀.map (valRingToField F), a, hPm, ?_, ?_, hares, ?_, ?_⟩
  · rw [hP₀m.natDegree_map, hP₀d]
  · intro i
    rw [Polynomial.coeff_map, coe_valRingToField]
    exact (P₀.coeff i).1.2
  · have h2 : ((((P₀.map (fieldValRing F).subtype).eval a : modelValSubring M))
        : M RVSort.K) = 0 := by
      rw [hPAroot, ZeroMemClass.coe_zero]
    rw [eval_coe_valSubring, ← hPmap, Polynomial.eval_map] at h2
    exact h2
  · -- minimality
    intro R hRF hRn hRne hRz
    exact Nat.find_min halg (m := (R.map (residue (modelValSubring M))).natDegree)
      (lt_of_le_of_lt (Polynomial.natDegree_map_le) hRn)
      (residueMonicDeg_of_eval_eq_zero F hRF hRne hRz)

/-! ### The routing

Given a leading term of the `RV`-part that is not yet a leading term of `F`, produce the element
of the field sort that one of the four cases asks for. -/

theorem rvMap_pow_congr {x y : M RVSort.K} (h : rvMap x = rvMap y) (k : ℕ) :
    rvMap (x ^ k) = rvMap (y ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]
  | succ k ih => rw [pow_succ, pow_succ, model_rv_mul, model_rv_mul, ih, h]

section Routing

variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]
variable (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N)

/-- The conclusion of a routing step: some element outside `F` is adjoined to the field part,
which is `LiftStepAt` at that element. -/
def LiftStepConclusion (F : Subfield (M RVSort.K)) : Prop :=
  ∃ a : M RVSort.K, a ∉ F ∧ LiftStepAt S e a

/-- **The residual routing.** A unit of the valuation ring whose leading term is in the `RV`-part
of `S` but is not a leading term of `F` is lifted to the field sort, transcendentally or
algebraically according to whether its residue satisfies a monic equation over the residues of
`F`. -/
theorem exists_lift_residual_of_unit
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F) {u : modelValSubring M} (hu : IsUnit u)
    (huS : rvMap ((u : modelValSubring M) : M RVSort.K) ∈ S RVSort.RV)
    (huF : ∀ x ∈ F, rvMap x ≠ rvMap ((u : modelValSubring M) : M RVSort.K)) :
    LiftStepConclusion S e F := by
  classical
  by_cases halg : ∃ n, ResidueMonicDeg F (residue (modelValSubring M) u) n
  · obtain ⟨n, P, a, hPm, hPn, hPint, hares, hPa, hdeg⟩ := exists_residual_root F halg
    have hρ0 : residue (modelValSubring M) u ≠ 0 := (residue_ne_zero_iff_isUnit u).mpr hu
    have hau : IsUnit a := by
      rw [← residue_ne_zero_iff_isUnit, hares]
      exact hρ0
    have hrv : rvMap ((a : modelValSubring M) : M RVSort.K)
        = rvMap ((u : modelValSubring M) : M RVSort.K) :=
      rvMap_eq_iff_rv_eq.mpr ((rv_eq_iff_residue_eq hu).mpr hares)
    obtain ⟨S', e', hsub, hmem, hrveq, hgeq, hext⟩ :=
      exists_lift_residual_algebraic S e hFS hSF hau (hrv ▸ huS) hPm hPn hPint hPa
        (fun R hRF hRn hRz => by rw [hares]; exact hdeg R hRF hRn hRz)
    exact ⟨_, (fun hc => huF _ hc hrv), S', e', hsub, hmem, hrveq, hgeq, hext⟩
  · push Not at halg
    have htr : ∀ R : (modelValSubring M)[X],
        (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F) →
        R.map (residue (modelValSubring M)) ≠ 0 →
        (R.map (residue (modelValSubring M))).eval
          (residue (modelValSubring M) u) ≠ 0 := fun R hRF hRne hRz =>
      halg _ (residueMonicDeg_of_eval_eq_zero F hRF hRne hRz)
    obtain ⟨S', e', hsub, hmem, hrveq, hgeq, hext⟩ :=
      exists_lift_residual_transcendental S e hFS hSF hu huS htr
    exact ⟨_, (fun hc => huF _ hc rfl), S', e', hsub, hmem, hrveq, hgeq, hext⟩

/-- **The routing.** A leading term of the `RV`-part of `S` that is not a leading term of `F`
gives an element of the field sort outside `F` in one of the four positions, hence a strictly
larger substructure with the same `RV`- and `Γ`-parts and an extension of the embedding.

The case distinction is the order `n` of `val ξ` over the values of `F`. Infinite order is the
ramified case of infinite order. At finite order `n`, either `ξⁿ` is already a leading term of
`F` — and then `ξ` is lifted by an `n`-th root, which `exists_pow_eq_rv_eq` produces with the
leading term prescribed, not merely the value — or it is not, and then scaling by a coefficient
of the same value lands in the residue fiber and the residual routing takes over. -/
theorem exists_lift_of_notMem
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F) {ξ : M RVSort.RV}
    (hξ : ξ ∈ S RVSort.RV) (hξF : ∀ x ∈ F, rvMap x ≠ ξ) :
    LiftStepConclusion S e F := by
  classical
  obtain ⟨a₀, ha₀⟩ := model_rv_surjective (M := M) ξ
  have ha₀0 : a₀ ≠ 0 := by
    intro h
    refine hξF 0 F.zero_mem ?_
    rw [← ha₀, h]
  have ha₀S : rvMap a₀ ∈ S RVSort.RV := ha₀ ▸ hξ
  have ha₀F : ∀ c ∈ F, rvMap c ≠ rvMap a₀ := fun c hc h => hξF c hc (h.trans ha₀)
  by_cases hord : ∀ k : ℕ, 0 < k → ∀ c ∈ F, valMap (rvMap (a₀ ^ k)) ≠ valMap (rvMap c)
  · -- ramified of infinite order
    obtain ⟨S', e', hsub, hmem, hrveq, hgeq, hext⟩ :=
      exists_lift_ramified S e hFS hSF ha₀0 ha₀S hord
    exact ⟨a₀, (fun hc => ha₀F a₀ hc rfl), S', e', hsub, hmem, hrveq, hgeq, hext⟩
  -- some power of the value lands in the values of `F`; take the least one
  have hex : ∃ k : ℕ, 0 < k ∧ ∃ c ∈ F, valMap (rvMap (a₀ ^ k)) = valMap (rvMap c) := by
    by_contra hc
    exact hord fun k hk c hcF hceq => hc ⟨k, hk, c, hcF, hceq⟩
  obtain ⟨hn, c, hcF, hceq⟩ := Nat.find_spec hex
  have hmin : ∀ k : ℕ, 0 < k → k < Nat.find hex → ∀ d ∈ F,
      valMap (rvMap (a₀ ^ k)) ≠ valMap (rvMap d) := fun k hk hkn d hdF hdeq =>
    Nat.find_min hex hkn ⟨hk, d, hdF, hdeq⟩
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, model_val_zero] at hceq
    exact ha₀0 ((pow_eq_zero_iff hn.ne').mp (model_val_eq_top_iff.mp hceq))
  by_cases hpow : ∃ d ∈ F, rvMap d = rvMap (a₀ ^ Nat.find hex)
  · -- ramified of finite order: replace `a₀` by an `n`-th root of `d` with the same leading term
    obtain ⟨d, hdF, hdeq⟩ := hpow
    have hζ : (rv (A := modelValSubring M) a₀) ^ Nat.find hex
        = rv (A := modelValSubring M) d := by
      rw [← map_pow]
      exact (rvMap_eq_iff_rv_eq.mp hdeq).symm
    obtain ⟨a, hapow, harv⟩ := exists_pow_eq_rv_eq (A := modelValSubring M) hn hζ
    have harvM : rvMap a = rvMap a₀ := rvMap_eq_iff_rv_eq.mpr harv
    have ha0 : a ≠ 0 := by
      intro h
      refine ha₀0 (model_rv_eq_zero_iff.mp ?_)
      rw [← harvM, h, model_rv_zero]
    have hord' : ∀ k : ℕ, 0 < k → k < Nat.find hex → ∀ d' ∈ F,
        valMap (rvMap (a ^ k)) ≠ valMap (rvMap d') := by
      intro k hk hkn d' hd'F
      rw [rvMap_pow_congr harvM k]
      exact hmin k hk hkn d' hd'F
    obtain ⟨S', e', hsub, hmem, hrveq, hgeq, hext⟩ :=
      exists_lift_ramified_finite S e hFS hSF ha0 (harvM ▸ ha₀S) hn (c := ⟨d, hdF⟩) hapow hord'
    exact ⟨a, (fun hcc => ha₀F a hcc harvM), S', e', hsub, hmem, hrveq, hgeq, hext⟩
  · -- residual: scale into the residue fiber by a coefficient of the same value
    push Not at hpow
    have hrvc0 : rv (A := modelValSubring M) c ≠ 0 := by
      rw [ne_eq, rv_eq_zero_iff]
      exact hc0
    have huval : (modelValSubring M).valuation (a₀ ^ Nat.find hex / c) = 1 := by
      rw [map_div₀, (valMap_eq_iff_valuation _ _).mp hceq,
        div_self ((Valuation.ne_zero_iff _).mpr hc0)]
    have huA : a₀ ^ Nat.find hex / c ∈ modelValSubring M :=
      (modelValSubring M).mem_of_valuation_le_one _ (le_of_eq huval)
    have huUnit : IsUnit (⟨a₀ ^ Nat.find hex / c, huA⟩ : modelValSubring M) :=
      ((modelValSubring M).valuation_eq_one_iff _).mpr huval
    have huS : rvMap (a₀ ^ Nat.find hex / c) ∈ S RVSort.RV := by
      rw [div_eq_mul_inv, model_rv_mul, model_rv_inv]
      exact mul_mem_RV (rvMap_pow_mem_RV ha₀S _) (inv_mem_RV (rvMap_mem_RV (hFS c hcF)))
    have huF : ∀ x ∈ F, rvMap x ≠ rvMap (a₀ ^ Nat.find hex / c) := by
      intro x hx hxu
      refine hpow (x * c) (F.mul_mem hx hcF) (rvMap_eq_iff_rv_eq.mpr ?_)
      rw [map_mul, rvMap_eq_iff_rv_eq.mp hxu, map_div₀, div_mul_cancel₀ _ hrvc0]
    exact exists_lift_residual_of_unit F S e hFS hSF huUnit huS huF

end Routing

end ManySorted.Language
