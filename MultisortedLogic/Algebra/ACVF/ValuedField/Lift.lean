/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.ValuedField.Residue
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Lifting residues and values

Rideau-Kikuchi's Propositions 2.1.5(2) and 2.1.3(2): in an algebraically closed valued field, a
prescribed residue and a prescribed value are attained. These are what steps `res(K(C)) = k(C)` and
`v(K(C)) = Γ(C)` of Proposition 2.1.10 apply in order to *find* the elements whose leading-term
types the extension steps then compare.

Neither needs Hensel's lemma. For values it is immediate: `Xⁿ - c` has a root, and its
valuation is forced, powers being strictly monotone in a linearly ordered group with zero. For
residues, a monic polynomial over the valuation ring splits into linear factors *over the
valuation ring* — its roots are integral, and a valuation ring is integrally closed — so its
reduction splits too, and a root of the reduction is the residue of a root.

## Main statements

* `ValuationSubring.mem_of_monic_eval_eq_zero` : roots of a monic polynomial over the valuation
  ring lie in the valuation ring.
* `ValuationSubring.exists_root_residue_eq` : Proposition 2.1.5(2).
* `ValuationSubring.exists_pow_eq_one_rv_eq` : roots of unity of the leading-term structure lift
  to roots of unity of the field.
* `ValuationSubring.exists_pow_eq_rv_eq` : hence a prescribed leading term, and not merely a
  prescribed value, is attained by an `n`-th root.
* `ValuationSubring.exists_pow_eq_of_valuation` : Proposition 2.1.3(2).
-/

@[expose] public section

namespace ValuationSubring

open Polynomial IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K}

/-- **Roots of a monic polynomial over the valuation ring lie in it**, the valuation ring being
integrally closed in its fraction field. -/
theorem mem_of_monic_eval_eq_zero {P : A[X]} (hP : P.Monic) {x : K}
    (hx : (P.map A.subtype).eval x = 0) : x ∈ A := by
  have hint : IsIntegral A x := ⟨P, hP, by rw [← Polynomial.eval_map]; exact hx⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

/-- A monic polynomial over the valuation ring that splits over the field splits over the
valuation ring: the linear factors have their roots there. -/
theorem eq_prod_roots_of_monic {P : A[X]} (hP : P.Monic)
    (hsplit : (P.map A.subtype).Splits) :
    ∃ m : Multiset A, P = (m.map fun a => X - C a).prod := by
  classical
  have hQm : (P.map A.subtype).Monic := hP.map _
  have hmem : ∀ x ∈ (P.map A.subtype).roots, x ∈ A := fun x hx =>
    mem_of_monic_eval_eq_zero hP ((Polynomial.mem_roots hQm.ne_zero).mp hx)
  refine ⟨(P.map A.subtype).roots.pmap (fun x hx => (⟨x, hmem x hx⟩ : A)) fun _ h => h, ?_⟩
  refine Polynomial.map_injective A.subtype Subtype.val_injective ?_
  conv_lhs => rw [hsplit.eq_prod_roots_of_monic hQm]
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_pmap]
  congr 1
  simp [Multiset.pmap_eq_map]

/-- **Proposition 2.1.5(2).** A monic polynomial over the valuation ring whose reduction vanishes at
a residue has a root with that residue. -/
theorem exists_root_residue_eq {P : A[X]} (hP : P.Monic)
    (hsplit : (P.map A.subtype).Splits) {γ : ResidueField A}
    (hγ : (P.map (residue A)).eval γ = 0) :
    ∃ a : A, P.eval a = 0 ∧ residue A a = γ := by
  classical
  obtain ⟨m, hPm⟩ := eq_prod_roots_of_monic hP hsplit
  -- the reduction factors the same way
  have hred : (P.map (residue A)).eval γ = (m.map fun a => γ - residue A a).prod := by
    rw [hPm, Polynomial.map_multiset_prod, Multiset.map_map, Polynomial.eval_multiset_prod,
      Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => by simp)
  rw [hred, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hγ
  obtain ⟨a, ham, hzero⟩ := hγ
  refine ⟨a, ?_, by rwa [sub_eq_zero, eq_comm] at hzero⟩
  rw [hPm, Polynomial.eval_multiset_prod, Multiset.map_map]
  refine Multiset.prod_eq_zero ?_
  rw [Multiset.mem_map]
  exact ⟨a, ham, by simp⟩

/-- **A value strictly between two finite families of values.** The values of an algebraically
closed field with a nontrivial valuation are densely ordered — the geometric mean of two values is
a value, `K` having square roots — and unbounded in both directions, so a finite family of lower
bounds and a finite family of upper bounds, each lower bound below each upper one, are separated
by the value of some element.

This is the finite fragment of realizing a cut in the value group, which is what the ramified case
of infinite order asks of the target. -/
theorem exists_valuation_between [IsAlgClosed K]
    {π : K} (hπ0 : π ≠ 0) (hπ : A.valuation π < 1)
    (Lo Hi : Finset K) (hLo : ∀ l ∈ Lo, l ≠ 0) (hHi : ∀ h ∈ Hi, h ≠ 0)
    (hsep : ∀ l ∈ Lo, ∀ h ∈ Hi, A.valuation l < A.valuation h) :
    ∃ y : K, y ≠ 0 ∧ (∀ l ∈ Lo, A.valuation l < A.valuation y) ∧
      (∀ h ∈ Hi, A.valuation y < A.valuation h) := by
  classical
  -- multiplying by `π` strictly decreases the value, dividing by it strictly increases it
  have hmulπ : ∀ x : K, x ≠ 0 → A.valuation (x * π) < A.valuation x := by
    intro x hx
    rw [map_mul]
    calc A.valuation x * A.valuation π
        < A.valuation x * 1 :=
          (mul_lt_mul_iff_right₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hx))).mpr hπ
      _ = A.valuation x := mul_one _
  have hdivπ : ∀ x : K, x ≠ 0 → A.valuation x < A.valuation (x / π) := by
    intro x hx
    have h := hmulπ (x / π) (div_ne_zero hx hπ0)
    rwa [div_mul_cancel₀ _ hπ0] at h
  by_cases hL : Lo.Nonempty
  · obtain ⟨l₀, hl₀, hl₀max⟩ := Finset.exists_max_image Lo (fun l => A.valuation l) hL
    by_cases hH : Hi.Nonempty
    · -- the geometric mean of the two extreme bounds
      obtain ⟨h₀, hh₀, hh₀min⟩ := Finset.exists_min_image Hi (fun h => A.valuation h) hH
      have hlh : A.valuation l₀ < A.valuation h₀ := hsep l₀ hl₀ h₀ hh₀
      have hl₀v : A.valuation l₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr (hLo l₀ hl₀)
      have hh₀v : A.valuation h₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr (hHi h₀ hh₀)
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (l₀ * h₀) two_pos
      have hy0 : y ≠ 0 := by
        intro h0
        rw [h0, zero_pow two_ne_zero] at hy
        exact mul_ne_zero (hLo l₀ hl₀) (hHi h₀ hh₀) hy.symm
      have hyv : A.valuation y ^ 2 = A.valuation l₀ * A.valuation h₀ := by
        rw [← map_pow, hy, map_mul]
      refine ⟨y, hy0, fun l hl => lt_of_le_of_lt (hl₀max l hl) ?_,
        fun h hh => lt_of_lt_of_le ?_ (hh₀min h hh)⟩
      · rw [← pow_lt_pow_iff_left₀ zero_le zero_le two_ne_zero, hyv, pow_two]
        exact (mul_lt_mul_iff_right₀ (pos_iff_ne_zero.mpr hl₀v)).mpr hlh
      · rw [← pow_lt_pow_iff_left₀ zero_le zero_le two_ne_zero, hyv, pow_two]
        exact (mul_lt_mul_iff_left₀ (pos_iff_ne_zero.mpr hh₀v)).mpr hlh
    · exact ⟨l₀ / π, div_ne_zero (hLo l₀ hl₀) hπ0,
        fun l hl => lt_of_le_of_lt (hl₀max l hl) (hdivπ l₀ (hLo l₀ hl₀)),
        fun h hh => absurd ⟨h, hh⟩ hH⟩
  · by_cases hH : Hi.Nonempty
    · obtain ⟨h₀, hh₀, hh₀min⟩ := Finset.exists_min_image Hi (fun h => A.valuation h) hH
      exact ⟨h₀ * π, mul_ne_zero (hHi h₀ hh₀) hπ0, fun l hl => absurd ⟨l, hl⟩ hL,
        fun h hh => lt_of_lt_of_le (hmulπ h₀ (hHi h₀ hh₀)) (hh₀min h hh)⟩
    · exact ⟨1, one_ne_zero, fun l hl => absurd ⟨l, hl⟩ hL, fun h hh => absurd ⟨h, hh⟩ hH⟩

/-- **A finite cut is realized divisibly.** Given two finite families of values with every member
of the first below every member of the second, some `n`-th power of a value lies strictly between
them: separate them by `exists_valuation_between` and take an `n`-th root.

This is what the ramified case of infinite order asks of the target, with `n` the common
denominator of the exponents in play. -/
theorem exists_pow_valuation_between [IsAlgClosed K]
    (hnt : ∃ π : K, π ≠ 0 ∧ A.valuation π ≠ 1) {n : ℕ} (hn : 0 < n)
    (Lo Hi : Finset K) (hLo : ∀ l ∈ Lo, l ≠ 0) (hHi : ∀ h ∈ Hi, h ≠ 0)
    (hsep : ∀ l ∈ Lo, ∀ h ∈ Hi, A.valuation l < A.valuation h) :
    ∃ b : K, b ≠ 0 ∧ (∀ l ∈ Lo, A.valuation l < A.valuation b ^ n) ∧
      (∀ h ∈ Hi, A.valuation b ^ n < A.valuation h) := by
  -- normalize the nontriviality witness to have value `< 1`
  obtain ⟨π, hπ0, hπlt⟩ : ∃ π : K, π ≠ 0 ∧ A.valuation π < 1 := by
    obtain ⟨x, hx0, hx1⟩ := hnt
    rcases lt_or_gt_of_ne hx1 with h | h
    · exact ⟨x, hx0, h⟩
    · have hv0 : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
      refine ⟨x⁻¹, inv_ne_zero hx0, ?_⟩
      rw [map_inv₀, ← mul_lt_mul_iff_left₀ (pos_iff_ne_zero.mpr hv0), inv_mul_cancel₀ hv0, one_mul]
      exact h
  obtain ⟨y, hy0, hyLo, hyHi⟩ :=
    exists_valuation_between (A := A) hπ0 hπlt Lo Hi hLo hHi hsep
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq y hn
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hb
    exact hy0 hb.symm
  have hbval : A.valuation b ^ n = A.valuation y := by rw [← map_pow, hb]
  exact ⟨b, hb0, by rw [hbval]; exact hyLo, by rw [hbval]; exact hyHi⟩

/-- **The residue field of a valuation subring of an algebraically closed field is algebraically
closed.** A monic polynomial over the residue field lifts to a monic polynomial over the valuation
ring; that one splits *over the valuation ring*, its roots being integral, and reducing the
factorization factors the original. -/
theorem isAlgClosed_residueField [IsAlgClosed K] : IsAlgClosed (ResidueField A) := by
  classical
  refine IsAlgClosed.of_exists_root _ fun p hpm hpirr => ?_
  have hlifts : p ∈ Polynomial.lifts (residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun i => Ideal.Quotient.mk_surjective (p.coeff i)
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hpm
  obtain ⟨m, hPfac⟩ := eq_prod_roots_of_monic hPm (IsAlgClosed.splits _)
  have hpfac : p = (m.map fun a => X - C (residue A a)).prod := by
    rw [← hPmap, hPfac, Polynomial.map_multiset_prod, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => by simp)
  have hm : m ≠ 0 := by
    rintro rfl
    rw [Multiset.map_zero, Multiset.prod_zero] at hpfac
    exact hpirr.not_isUnit (hpfac ▸ isUnit_one)
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hm
  refine ⟨residue A a, ?_⟩
  rw [hpfac, Polynomial.eval_multiset_prod, Multiset.map_map]
  refine Multiset.prod_eq_zero ?_
  rw [Multiset.mem_map]
  exact ⟨a, ha, by simp⟩

/-- **Roots of unity lift to the field.** Every `n`-th root of unity of the leading-term structure
of an algebraically closed valued field is the leading term of an `n`-th root of unity of the
field.

This is what makes a prescribed *leading term* attainable by an `n`-th root of a prescribed
element, and not merely a prescribed value: two `n`-th roots of the same element have leading
terms differing by an `n`-th root of unity of `RV`, and that root of unity is the leading term of
one in the field. No characteristic assumption is needed — the value group is ordered, hence
torsion-free, so a root of unity of `RV` is a residue, and `exists_root_residue_eq` lifts it. -/
theorem exists_pow_eq_one_rv_eq [IsAlgClosed K] {n : ℕ} (hn : 0 < n)
    {μ : A.RV} (hμ : μ ^ n = 1) : ∃ w : K, w ^ n = 1 ∧ rv (A := A) w = μ := by
  obtain ⟨x, rfl⟩ := rv_surjective (A := A) μ
  -- a root of unity of `RV` has value `1`, so it is the leading term of a unit
  have hval : A.valuation x = 1 := by
    refine (pow_eq_one_iff_of_nonneg zero_le hn.ne').mp ?_
    rw [← map_pow, ← rvVal_rv (A := A) (x ^ n), map_pow, hμ, map_one]
  have hxA : x ∈ A := A.mem_of_valuation_le_one x (le_of_eq hval)
  have hux : IsUnit (⟨x, hxA⟩ : A) := (A.valuation_eq_one_iff _).mpr hval
  -- and its residue is an `n`-th root of unity of the residue field
  have hρn : residue A (⟨x, hxA⟩ : A) ^ n = 1 := by
    have hcoe : (((⟨x, hxA⟩ : A) ^ n : A) : K) = x ^ n := by push_cast; ring
    have h1 : residue A ((⟨x, hxA⟩ : A) ^ n) = residue A 1 := by
      refine (rv_eq_iff_residue_eq (A := A) isUnit_one).mp ?_
      rw [hcoe, OneMemClass.coe_one, map_one, map_pow, hμ]
    rwa [map_pow, map_one] at h1
  obtain ⟨w, hwroot, hwres⟩ := exists_root_residue_eq (A := A)
    (γ := residue A (⟨x, hxA⟩ : A))
    (Polynomial.monic_X_pow_sub_C (1 : A) hn.ne') (IsAlgClosed.splits _) (by simp [hρn])
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero] at hwroot
  refine ⟨(w : K), ?_, ?_⟩
  · have := congrArg (fun y : A => (y : K)) hwroot
    push_cast at this
    exact this
  · exact (rv_eq_iff_residue_eq (A := A) hux).mpr hwres

/-- **A prescribed leading term is attained by an `n`-th root.** If `ζⁿ` is the leading term of
`d`, then some `n`-th root of `d` has leading term exactly `ζ` — not merely the right value.
This is Proposition 2.1.3(2) refined from values to leading terms, and it is what the ramified case
of finite order needs on both sides of an embedding. -/
theorem exists_pow_eq_rv_eq [IsAlgClosed K] {n : ℕ} (hn : 0 < n) {d : K}
    {ζ : A.RV} (hζ : ζ ^ n = rv (A := A) d) :
    ∃ a : K, a ^ n = d ∧ rv (A := A) a = ζ := by
  by_cases hd : d = 0
  · subst hd
    rw [rv_zero] at hζ
    exact ⟨0, zero_pow hn.ne', by rw [rv_zero, (pow_eq_zero_iff hn.ne').mp hζ]⟩
  have hrvd : rv (A := A) d ≠ 0 := by rw [ne_eq, rv_eq_zero_iff]; exact hd
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq d hn
  have hb0 : b ≠ 0 := fun h => hd (by rw [← hb, h, zero_pow hn.ne'])
  have hrvb : rv (A := A) b ≠ 0 := by rw [ne_eq, rv_eq_zero_iff]; exact hb0
  -- `b` and `ζ` differ by an `n`-th root of unity, which lifts
  have hμ : (rv (A := A) b * ζ⁻¹) ^ n = 1 := by
    rw [mul_pow, ← map_pow, hb, inv_pow, hζ, mul_inv_cancel₀ hrvd]
  obtain ⟨w, hwn, hwrv⟩ := exists_pow_eq_one_rv_eq hn hμ
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hwn
    exact zero_ne_one hwn
  refine ⟨b / w, by rw [div_pow, hwn, hb, div_one], ?_⟩
  rw [map_div₀, hwrv, div_eq_mul_inv, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hrvb,
    one_mul]

/-- **Proposition 2.1.3(2).** A prescribed value with an `n`-th power in the value group is attained
by an `n`-th root. -/
theorem exists_pow_eq_of_valuation [IsAlgClosed K] {c : K} {n : ℕ} (hn : 0 < n)
    {γ : A.ValueGroup} (hγ : γ ^ n = A.valuation c) :
    ∃ a : K, a ^ n = c ∧ A.valuation a = γ := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  refine ⟨a, ha, ?_⟩
  have hpow : A.valuation a ^ n = γ ^ n := by rw [← map_pow, ha, hγ]
  exact (pow_left_inj₀ zero_le zero_le hn.ne').mp hpow

end ValuationSubring
