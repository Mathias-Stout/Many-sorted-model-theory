/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathias Stout
-/

module

public import MultisortedLogic.AlgebraicBackground.Order
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.CountableDenseLinearOrder

/-! # Affine inequalities in ordered abelian groups

The algebraic core of quantifier elimination for divisible ordered abelian groups
(`Algebra/DOAG/QE.lean`): the transfer of the affine inequalities `k • b ⋚ a` along an
order-reflecting additive map defined on a subgroup. Nothing in this file mentions model theory.

## Main results

* `zsmul_le_iff_neg`, `le_zsmul_iff_neg`, `add_zsmul_le_add_zsmul_iff` : rearrangement
  lemmas for affine inequalities `p + k • b ≤ q + l • b` in ordered abelian groups.
* `affine_key_of_zsmul_eq`, `affine_key_of_cut_bounds` : the transfer, in the divisible-hull case
  and in the cut case.
* `exists_affine_cut_bounds` : every finite portion of a cut is realized in a nontrivial
  `ℤ`-divisible group.
-/

public section

section OrderedGroup

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Flipping an affine inequality by negation: `k • b ≤ v` iff `-v ≤ (-k) • b`. -/
theorem zsmul_le_iff_neg (k : ℤ) (b v : G) : k • b ≤ v ↔ -v ≤ (-k) • b := by
  rw [neg_zsmul]
  exact neg_le_neg_iff.symm

/-- Flipping an affine inequality by negation: `v ≤ k • b` iff `(-k) • b ≤ -v`. -/
theorem le_zsmul_iff_neg (k : ℤ) (b v : G) : v ≤ k • b ↔ (-k) • b ≤ -v := by
  rw [neg_zsmul]
  exact neg_le_neg_iff.symm

/-- Rearranging an inequality between affine expressions in `b`:
`p + k₁ • b ≤ q + k₂ • b` iff `(k₁ - k₂) • b ≤ q - p`. -/
theorem add_zsmul_le_add_zsmul_iff (p q b : G) (k₁ k₂ : ℤ) :
    p + k₁ • b ≤ q + k₂ • b ↔ (k₁ - k₂) • b ≤ q - p := by
  rw [sub_zsmul, ← sub_eq_add_neg, sub_le_sub_iff, add_comm (k₁ • b) p]

/-- Extend an affine-inequality transfer principle from positive multipliers to all
integer multipliers, given transfer at `0` and compatibility with a negation operation on
the parameter type. -/
theorem affine_transfer_of_pos {H : Type*}
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    {T : Type*} (vG : T → G) (vH : T → H) (tneg : T → T)
    (hnegG : ∀ u, vG (tneg u) = -vG u) (hnegH : ∀ u, vH (tneg u) = -vH u)
    (b : G) (c : H)
    (h0 : ∀ u, (0 ≤ vG u ↔ 0 ≤ vH u) ∧ (vG u ≤ 0 ↔ vH u ≤ 0))
    (hpos : ∀ k : ℤ, 0 < k → ∀ u,
      (k • b ≤ vG u ↔ k • c ≤ vH u) ∧ (vG u ≤ k • b ↔ vH u ≤ k • c))
    (k : ℤ) (u : T) :
    (k • b ≤ vG u ↔ k • c ≤ vH u) ∧ (vG u ≤ k • b ↔ vH u ≤ k • c) := by
  rcases lt_trichotomy k 0 with hneg | rfl | hk
  · have h := hpos (-k) (by omega) (tneg u)
    rw [hnegG, hnegH] at h
    constructor
    · rw [zsmul_le_iff_neg, zsmul_le_iff_neg]
      exact h.2
    · rw [le_zsmul_iff_neg, le_zsmul_iff_neg]
      exact h.1
  · rw [zero_zsmul, zero_zsmul]
    exact h0 u
  · exact hpos k hk u

end OrderedGroup

/-!
### Affine transfer along an ordered-group morphism on a subgroup

The following three lemmas are the algebraic core of the quantifier elimination proof for
divisible ordered abelian groups:
given an order-reflecting additive morphism `ψ : A →+ H` on a subgroup `A ≤ G` and an
element `b : G`, they transfer the affine inequalities `k • b ⋚ a` (`a ∈ A`) to affine
inequalities `k • c ⋚ ψ a` for a suitable `c`.

* `affine_key_of_zsmul_eq` : the *divisible-hull case* — if `k₀ • b` lies in `A` and `c`
  satisfies the corresponding relation, all affine inequalities transfer.
* `affine_key_of_cut_bounds` : the *cut case* — if no multiple of `b` lies in `A` and `c`
  realizes the strict cut of `b` over `A`, all affine inequalities transfer.
* `exists_affine_cut_bounds` : in a nontrivial `ℤ`-divisible `H`, every finite portion of
  the strict cut of `b` over `A` is realized by some `c₀ : H` (finite satisfiability).
-/

section SubgroupAffine

variable {G H : Type*}
  [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]
  {A : AddSubgroup G} (ψ : A →+ H)

/-- **Divisible-hull case**: if `k₀ • b = a₀ ∈ A` with `k₀ > 0` and `k₀ • c = ψ a₀`, then
all affine inequalities `k • b ⋚ a` (`a ∈ A`) transfer to `k • c ⋚ ψ a`. -/
theorem affine_key_of_zsmul_eq
    (hψ : ∀ a a' : A, ψ a ≤ ψ a' ↔ (a : G) ≤ (a' : G))
    {b : G} {c : H} {k₀ : ℤ} (hk₀ : 0 < k₀) {a₀ : A}
    (hb : k₀ • b = (a₀ : G)) (hc : k₀ • c = ψ a₀)
    (k : ℤ) (a : A) :
    (k • b ≤ (a : G) ↔ k • c ≤ ψ a) ∧ ((a : G) ≤ k • b ↔ ψ a ≤ k • c) := by
  have e1 : k₀ • (k • b) = ((k • a₀ : A) : G) := by
    rw [smul_comm k₀ k b, hb, AddSubgroup.coe_zsmul]
  constructor
  · rw [← zsmul_le_zsmul_iff_right hk₀ (a := k • b), e1, ← AddSubgroup.coe_zsmul,
      ← hψ, map_zsmul, map_zsmul, ← hc, smul_comm k k₀ c, zsmul_le_zsmul_iff_right hk₀]
  · rw [← zsmul_le_zsmul_iff_right hk₀ (b := k • b), e1, ← AddSubgroup.coe_zsmul,
      ← hψ, map_zsmul, map_zsmul, ← hc, smul_comm k k₀ c, zsmul_le_zsmul_iff_right hk₀]

/-- **Cut case**: if no nonzero multiple of `b` lies in `A` and `c` realizes the strict cut
of `b` over `A`, then all affine inequalities `k • b ⋚ a` (`a ∈ A`) transfer to
`k • c ⋚ ψ a`. -/
theorem affine_key_of_cut_bounds
    (hψ : ∀ a a' : A, ψ a ≤ ψ a' ↔ (a : G) ≤ (a' : G))
    {b : G} {c : H}
    (hnd : ∀ (k : ℤ) (a : A), k ≠ 0 → k • b ≠ (a : G))
    (hcut : ∀ (k : ℤ) (a : A), 0 < k →
      (((a : G) < k • b → ψ a < k • c) ∧ (k • b < (a : G) → k • c < ψ a)))
    (k : ℤ) (a : A) :
    (k • b ≤ (a : G) ↔ k • c ≤ ψ a) ∧ ((a : G) ≤ k • b ↔ ψ a ≤ k • c) := by
  have keyPos : ∀ k' : ℤ, 0 < k' → ∀ a' : A,
      (k' • b ≤ (a' : G) ↔ k' • c ≤ ψ a') ∧ ((a' : G) ≤ k' • b ↔ ψ a' ≤ k' • c) := by
    intro k' hk' a'
    rcases lt_trichotomy (k' • b) ((a' : G)) with hlt | heq | hgt
    · have hc' := (hcut k' a' hk').2 hlt
      exact ⟨by simp only [le_of_lt hlt, le_of_lt hc'],
        ⟨fun h => absurd hlt (not_lt.mpr h), fun h => absurd hc' (not_lt.mpr h)⟩⟩
    · exact absurd heq (hnd k' a' (ne_of_gt hk'))
    · have hc' := (hcut k' a' hk').1 hgt
      exact ⟨⟨fun h => absurd hgt (not_lt.mpr h), fun h => absurd hc' (not_lt.mpr h)⟩,
        by simp only [le_of_lt hgt, le_of_lt hc']⟩
  refine affine_transfer_of_pos (fun a : A => (a : G)) (fun a : A => ψ a) (fun a => -a)
    (fun _ => rfl) (fun a => map_neg ψ a) b c (fun a' => ?_) keyPos k a
  constructor
  · have h := hψ 0 a'
    rw [map_zero, AddSubgroup.coe_zero] at h
    exact h.symm
  · have h := hψ a' 0
    rw [map_zero, AddSubgroup.coe_zero] at h
    exact h.symm

/-- **Finite satisfiability of the cut**: in a
nontrivial `ℤ`-divisible ordered abelian group `H`, any finite family of strict cut
conditions of `b` over `A` is realized: scale to a common multiplier `K`, interpolate
between the scaled bounds, and divide by `K`. -/
theorem exists_affine_cut_bounds [DivisibleBy H ℤ] [Nontrivial H]
    (hψ : ∀ a a' : A, ψ a ≤ ψ a' ↔ (a : G) ≤ (a' : G))
    (b : G) (F : Finset (ℤ × A)) (hpos : ∀ q ∈ F, 0 < q.1) :
    ∃ c₀ : H, ∀ q ∈ F,
      (((q.2 : G) < q.1 • b → ψ q.2 < q.1 • c₀) ∧
       (q.1 • b < (q.2 : G) → q.1 • c₀ < ψ q.2)) := by
  classical
  have : DenselyOrdered H := DivisibleBy.denselyOrdered
  have hψlt : ∀ a a' : A, ψ a < ψ a' ↔ (a : G) < (a' : G) := by
    intro a a'
    rw [lt_iff_not_ge, lt_iff_not_ge]
    exact not_congr (hψ a' a)
  set K : ℤ := ∏ q ∈ F, q.1 with hK
  have hKpos : 0 < K := Finset.prod_pos hpos
  have hdvd : ∀ q ∈ F, q.1 ∣ K := fun q hq => Finset.dvd_prod_of_mem _ hq
  have hquot : ∀ q ∈ F, 0 < K / q.1 := fun q hq =>
    Int.ediv_pos_of_pos_of_dvd hKpos (hpos q hq).le (hdvd q hq)
  have hscaleG : ∀ q ∈ F, ∀ z : G, (K / q.1) • (q.1 • z) = K • z := by
    intro q hq z
    rw [← mul_zsmul, Int.ediv_mul_cancel (hdvd q hq)]
  have hscaleH : ∀ q ∈ F, ∀ z : H, (K / q.1) • (q.1 • z) = K • z := by
    intro q hq z
    rw [← mul_zsmul, Int.ediv_mul_cancel (hdvd q hq)]
  set lo : Finset H := (F.filter (fun q => (q.2 : G) < q.1 • b)).image
    (fun q => (K / q.1) • ψ q.2) with hlo
  set hi : Finset H := (F.filter (fun q => q.1 • b < (q.2 : G))).image
    (fun q => (K / q.1) • ψ q.2) with hhi
  have hpair : ∀ u ∈ lo, ∀ v ∈ hi, u < v := by
    intro u hu v hv
    rw [hlo, Finset.mem_image] at hu
    rw [hhi, Finset.mem_image] at hv
    obtain ⟨q₁, hq₁, rfl⟩ := hu
    obtain ⟨q₂, hq₂, rfl⟩ := hv
    have hq₁F := (Finset.mem_filter.mp hq₁).1
    have hq₂F := (Finset.mem_filter.mp hq₂).1
    have hlt₁ := (Finset.mem_filter.mp hq₁).2
    have hlt₂ := (Finset.mem_filter.mp hq₂).2
    -- the corresponding chain in `G`, through `K • b`
    have h₁ : (K / q₁.1) • (q₁.2 : G) < K • b := by
      have := (zsmul_lt_zsmul_iff_right (hquot q₁ hq₁F)).mpr hlt₁
      rwa [hscaleG q₁ hq₁F b] at this
    have h₂ : K • b < (K / q₂.1) • (q₂.2 : G) := by
      have := (zsmul_lt_zsmul_iff_right (hquot q₂ hq₂F)).mpr hlt₂
      rwa [hscaleG q₂ hq₂F b] at this
    have hcoe : (((K / q₁.1) • q₁.2 : A) : G) < (((K / q₂.1) • q₂.2 : A) : G) :=
      h₁.trans h₂
    have := (hψlt ((K / q₁.1) • q₁.2) ((K / q₂.1) • q₂.2)).mpr hcoe
    rwa [map_zsmul, map_zsmul] at this
  obtain ⟨d, hdlo, hdhi⟩ := Order.exists_between_finsets lo hi hpair
  refine ⟨DivisibleBy.div d K, ?_⟩
  have hc₀ : K • DivisibleBy.div d K = d := DivisibleBy.div_cancel d (ne_of_gt hKpos)
  intro q hq
  constructor
  · intro hlt
    have h1 : (K / q.1) • ψ q.2 < K • DivisibleBy.div d K := by
      rw [hc₀]
      exact hdlo _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hq, hlt⟩))
    rw [← hscaleH q hq] at h1
    exact (zsmul_lt_zsmul_iff_right (hquot q hq)).mp h1
  · intro hlt
    have h1 : K • DivisibleBy.div d K < (K / q.1) • ψ q.2 := by
      rw [hc₀]
      exact hdhi _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hq, hlt⟩))
    rw [← hscaleH q hq] at h1
    exact (zsmul_lt_zsmul_iff_right (hquot q hq)).mp h1

end SubgroupAffine
