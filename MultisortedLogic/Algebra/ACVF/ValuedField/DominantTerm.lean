/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.AlgebraicBackground.RV

/-!
# Sums with a dominant term

In an ultrametric setting a finite sum in which one term strictly dominates has the valuation
and the leading term of that term. This is the computation behind Rideau-Kikuchi's Proposition 2.1.3
(purely ramified 1-types): if `val a` has order `n` over the value group of the coefficients, then
for `Q` of degree `< n` the terms `qᵢ aⁱ` have pairwise distinct valuations, so exactly one of them
dominates and

  `rv (Q a) = rv (q_{i₀} a ^ i₀)`.

Distinctness is what makes the ramified case computable, and it is where the order of `val a`
is used: if `val qᵢ · (val a)^i = val qⱼ · (val a)^j` with `i < j`, then `(val a)^(j-i)` lies in
the value group of the coefficients, contradicting minimality of `n`
(`valuation_mul_pow_ne_of_notMem`).

## Main statements

* `ValuationSubring.rv_add_eq_of_valuation_lt` : a strictly smaller summand does not change the
  leading term.
* `ValuationSubring.rv_sum_eq_of_lt` : a finite sum with a dominant term.
* `ValuationSubring.rv_eval_eq_of_lt` : the polynomial form.
* `ValuationSubring.valuation_mul_pow_ne_of_notMem` : the ramified distinctness criterion.
* `ValuationSubring.rv_eval_eq_of_ramified` : Proposition 2.1.3 itself, over a subfield.
* `mul_pow_lt_mul_pow_iff`, `mul_pow_lt_mul_pow_iff'` : in a linearly ordered commutative group
  with zero, a comparison of two monomials `u * g ^ i` and `u' * g ^ (i + m)` is a comparison of
  the ratio of the coefficients with `g ^ m`.
-/

@[expose] public section

namespace ValuationSubring

open Polynomial

variable {K : Type*} [Field K] {A : ValuationSubring K}

/-- Adding something strictly smaller does not change the leading term. -/
theorem rv_add_eq_of_valuation_lt {x y : K} (h : A.valuation y < A.valuation x) :
    rv (A := A) (x + y) = rv (A := A) x := by
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    exact absurd h (by simp)
  rw [eq_comm, rv_eq_iff_valuation_sub_lt hx0, show x + y - x = y by ring]
  exact h

/-- **A finite sum with a dominant term** has that term's leading term. -/
theorem rv_sum_eq_of_lt {ι : Type*} {s : Finset ι} {f : ι → K} {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hlt : ∀ i ∈ s, i ≠ i₀ → A.valuation (f i) < A.valuation (f i₀)) :
    rv (A := A) (∑ i ∈ s, f i) = rv (A := A) (f i₀) := by
  classical
  rw [← Finset.add_sum_erase _ _ hi₀]
  by_cases h0 : f i₀ = 0
  · -- every other term would be smaller than `0`, which is impossible
    have hempty : ∀ i ∈ s.erase i₀, f i = 0 := by
      intro i hi
      have hlti := hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
      rw [h0, map_zero] at hlti
      exact absurd hlti (by simp)
    rw [Finset.sum_congr rfl hempty, Finset.sum_const_zero, add_zero]
  · refine rv_add_eq_of_valuation_lt (Valuation.map_sum_lt _ ?_ ?_)
    · exact (Valuation.ne_zero_iff _).mpr h0
    · exact fun i hi =>
        hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

/-- The polynomial form: if one term of `Q` dominates at `a`, it carries the leading term. -/
theorem rv_eval_eq_of_lt {Q : K[X]} {a : K} {i₀ : ℕ} (hi₀ : i₀ ∈ Q.support)
    (hlt : ∀ i ∈ Q.support, i ≠ i₀ →
      A.valuation (Q.coeff i * a ^ i) < A.valuation (Q.coeff i₀ * a ^ i₀)) :
    rv (A := A) (Q.eval a) = rv (A := A) (Q.coeff i₀ * a ^ i₀) := by
  rw [eval_eq_sum, Polynomial.sum_def]
  exact rv_sum_eq_of_lt hi₀ hlt

/-- **The ramified distinctness criterion.** If no power `(val a)^k` with `0 < k < n` lies in
the set `G` of values of the coefficients — which is the statement that `val a` has order at
least `n` over `G` — then the terms `qᵢ aⁱ` have pairwise distinct valuations. -/
theorem valuation_mul_pow_ne_of_notMem {G : Set A.ValueGroup}
    (hdiv : ∀ x ∈ G, ∀ y ∈ G, y ≠ 0 → x / y ∈ G)
    {q : ℕ → K} (hq : ∀ i, A.valuation (q i) ∈ G) {a : K} (ha : a ≠ 0) {n : ℕ}
    (hord : ∀ k, 0 < k → k < n → A.valuation a ^ k ∉ G)
    {i j : ℕ} (hj : j < n) (hij : i < j) (hqj : q j ≠ 0) :
    A.valuation (q i) * A.valuation a ^ i ≠ A.valuation (q j) * A.valuation a ^ j := by
  intro heq
  have hva : A.valuation a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hvj : A.valuation (q j) ≠ 0 := (Valuation.ne_zero_iff _).mpr hqj
  refine hord (j - i) (Nat.sub_pos_of_lt hij) (lt_of_le_of_lt (Nat.sub_le _ _) hj) ?_
  have hpow : A.valuation a ^ j = A.valuation a ^ (j - i) * A.valuation a ^ i := by
    rw [← pow_add, Nat.sub_add_cancel (le_of_lt hij)]
  have h3 : A.valuation (q i) = A.valuation (q j) * A.valuation a ^ (j - i) :=
    mul_right_cancel₀ (pow_ne_zero i hva) (by rw [heq, hpow, mul_assoc])
  have h4 : A.valuation a ^ (j - i) = A.valuation (q i) / A.valuation (q j) :=
    (eq_div_iff hvj).mpr (by rw [h3, mul_comm])
  rw [h4]
  exact hdiv _ (hq i) _ (hq j) hvj


/-!
### Proposition 2.1.3, the purely ramified computation

Taking `G` to be the set of values of a subfield `F` makes the distinctness criterion concrete:
if no power `(val a)^k` with `0 < k < n` is the value of an element of `F` — that is, `val a`
has order at least `n` over the value group of `F` — then for `Q` over `F` of degree `< n`
exactly one term of `Q a` dominates, so `rv (Q a)` is determined by the leading terms of the
coefficients together with `rv a`.
-/

/-- **Proposition 2.1.3, the purely ramified computation.** If `val a` has order at least `n` over
the values of the subfield `F`, then a polynomial over `F` of degree `< n` has a unique dominant
term at `a`, and its leading term there is that term's. -/
theorem rv_eval_eq_of_ramified {F : Subfield K} {n : ℕ} {a : K} (ha : a ≠ 0)
    (hord : ∀ k, 0 < k → k < n → A.valuation a ^ k ∉ A.valuation '' (F : Set K))
    {Q : K[X]} (hQ : Q ≠ 0) (hQF : ∀ i, Q.coeff i ∈ F) (hQn : Q.natDegree < n) :
    ∃ i₀ ∈ Q.support,
      (∀ i ∈ Q.support, i ≠ i₀ →
        A.valuation (Q.coeff i) * A.valuation a ^ i
          < A.valuation (Q.coeff i₀) * A.valuation a ^ i₀) ∧
      rv (A := A) (Q.eval a) = rv (A := A) (Q.coeff i₀) * rv (A := A) a ^ i₀ := by
  classical
  -- the values of `F` are closed under division
  have hdiv : ∀ x ∈ A.valuation '' (F : Set K), ∀ y ∈ A.valuation '' (F : Set K), y ≠ 0 →
      x / y ∈ A.valuation '' (F : Set K) := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩ -
    exact ⟨f / g, F.div_mem hf hg, map_div₀ _ _ _⟩
  have hq : ∀ i, A.valuation (Q.coeff i) ∈ A.valuation '' (F : Set K) :=
    fun i => ⟨Q.coeff i, hQF i, rfl⟩
  -- distinct terms have distinct valuations
  have hne : ∀ i ∈ Q.support, ∀ j ∈ Q.support, i ≠ j →
      A.valuation (Q.coeff i) * A.valuation a ^ i
        ≠ A.valuation (Q.coeff j) * A.valuation a ^ j := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact valuation_mul_pow_ne_of_notMem hdiv hq ha hord
        (lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp j hj) hQn) h
        (Polynomial.mem_support_iff.mp hj)
    · exact fun heq => valuation_mul_pow_ne_of_notMem hdiv hq ha hord
        (lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp i hi) hQn) h
        (Polynomial.mem_support_iff.mp hi) heq.symm
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image Q.support
    (fun i => A.valuation (Q.coeff i) * A.valuation a ^ i) (Polynomial.support_nonempty.mpr hQ)
  have hlt : ∀ i ∈ Q.support, i ≠ i₀ →
      A.valuation (Q.coeff i) * A.valuation a ^ i
        < A.valuation (Q.coeff i₀) * A.valuation a ^ i₀ :=
    fun i hi hii => lt_of_le_of_ne (hmax i hi) (hne i hi i₀ hi₀ hii)
  refine ⟨i₀, hi₀, hlt, ?_⟩
  rw [rv_eval_eq_of_lt hi₀ ?_, map_mul, map_pow]
  intro i hi hii
  rw [map_mul, map_mul, map_pow, map_pow]
  exact hlt i hi hii

end ValuationSubring

/-! ### Monomials in a linearly ordered commutative group with zero -/

section GroupWithZero

variable {G : Type*} [LinearOrderedCommGroupWithZero G]

/-- **A comparison of two monomials is a comparison of the ratio of their coefficients with a
power of the value.** This is what turns the ramified domination hypothesis into a cut condition:
all it ever says about `g` is where the powers `g ^ m` sit among the ratios of the coefficients. -/
theorem mul_pow_lt_mul_pow_iff {u u' g : G} (hu' : u' ≠ 0) (hg : g ≠ 0) (i m : ℕ) :
    u * g ^ i < u' * g ^ (i + m) ↔ u / u' < g ^ m := by
  have h1 : u' * g ^ (i + m) = u' * g ^ m * g ^ i := by
    rw [pow_add, mul_comm (g ^ i) (g ^ m), ← mul_assoc]
  rw [h1, mul_lt_mul_iff_left₀ (pos_iff_ne_zero.mpr (pow_ne_zero i hg)),
    div_lt_iff₀' (pos_iff_ne_zero.mpr hu')]

/-- The companion of `mul_pow_lt_mul_pow_iff` with the larger exponent on the left. -/
theorem mul_pow_lt_mul_pow_iff' {u u' g : G} (hu : u ≠ 0) (hg : g ≠ 0) (i m : ℕ) :
    u * g ^ (i + m) < u' * g ^ i ↔ g ^ m < u' / u := by
  have h1 : u * g ^ (i + m) = u * g ^ m * g ^ i := by
    rw [pow_add, mul_comm (g ^ i) (g ^ m), ← mul_assoc]
  rw [h1, mul_lt_mul_iff_left₀ (pos_iff_ne_zero.mpr (pow_ne_zero i hg)),
    lt_div_iff₀' (pos_iff_ne_zero.mpr hu)]

end GroupWithZero
