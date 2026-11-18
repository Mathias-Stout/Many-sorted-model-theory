/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.FieldStep.Compactness
public import MultisortedLogic.Algebra.ACVF.RVLift.Routing
public import MultisortedLogic.Algebra.ACVF.ValuedField.BallTransfer
public import MultisortedLogic.Algebra.ACVF.ValuedField.ImmediateRoot

/-!
# `ValuePatternExt`: Rideau-Kikuchi's routing for step `K(C) = K(M)`

`Algebra/ACVF/FieldStep/Compactness.lean` reduces `FieldStep` to `ValuePatternExt`: for every
`y ∉ F` there is an `a ∉ F` whose whole pattern of value comparisons over `F` is realized in an
elementary extension of the target. In all but one of the sub-cases
below, that pattern comes by compactness (`patternWitness_of_valuePatternAt`) from its finite
fragments in the target itself:

```lean
ValuePatternAt F d a : Prop :=
  ∀ t : Finset F[X], ∃ b : N K, ∀ P ∈ t, ∀ Q ∈ t,
    (val (rv (P a)) ≤ val (rv (Q a)) ↔ val (rv (P b)) ≤ val (rv (Q b)))
```

This file proves `ValuePatternExt` by Rideau-Kikuchi's routing; `Algebra/ACVF/QE.lean` combines it
with `RVLift_holds` into the main theorem. The whole of the work is to produce, from an arbitrary
`y ∉ F`, a suitable `a ∉ F`.

## The routing

The element `y` is translated and scaled until it lands in one of Rideau-Kikuchi's three cases.

* If the extension is **not immediate at `y`**, some `z = y - r` has a leading term that is not a
  leading term of `F` (`exists_rv_ne_of_not_immediateAt`), and the order `n` of its value over the
  values of `F` decides the case, as in the routing of `RVLift` (`exists_lift_of_notMem`). Infinite
  order is the **ramified** case. At finite order, either `zⁿ` has the leading term of some `e ∈ F`,
  and an `n`-th root of `e` with the leading term of `z` is the **ramified** case of finite order,
  or `zⁿ / c`, for a `c ∈ F` of the same value, is a unit with a new residue: the **residual** case
  (`exists_valuePatternAt_of_rv_notMem`). The residual case reuses the residue-field lemmas of
  `Algebra/ACVF/RVLift/Routing.lean`.
* If it **is immediate at `y`**, the ball filter of `y` over `F` is the data, and the element to
  adjoin is `y` itself or a root of the minimal polynomial meeting the filter.

Three of the six sub-cases are **algebraic**: the far-side element is a root of an image
polynomial. In the ramified and residual ones, `N` contains such a root because `N K` is
algebraically closed, so the *whole* `ReflectData` is available at once and no finiteness is used
(`valuePatternAt_of_reflectData`). In the immediate one, the root must also be at prescribed
distances from the whole coefficient field, which no element of `N` need be, so it is found in an
elementary extension of `N`. The other three sub-cases are **generic**, and there the element of
`N` genuinely depends on the finite set of polynomials.

## Main definitions

* `Language.ValuePatternAt` : the finite fragment of the pattern of `a`, in the target.
* `Language.PatternWitness` : what each branch of the routing delivers.

## Main statements

* `Language.valuePatternAt_of_reflectData` : a single `b` that works for every polynomial gives it.
* `Language.exists_valuePatternAt_of_rv_notMem` : the routing, for an element with a new
  leading term.
* `Language.exists_patternWitness` : the routing in full.
* `Language.valuePatternExt_holds` : **`ValuePatternExt`**, hence `FieldStep` by
  `fieldStep_of_valuePatternExt`.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial IsLocalRing

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]
variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]

/-- **The residue field of a model is algebraically closed**, the field sort being. -/
instance instIsAlgClosedResidueField : IsAlgClosed (ResidueField (modelValSubring M)) :=
  isAlgClosed_residueField

/-! ### The statement at a fixed element -/

variable (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)

/-- **The finite fragments of the pattern of `a`, in the target**: every finite set of polynomials
over `F` has its pattern of value comparisons at `a` matched by some element of the target. -/
def ValuePatternAt (a : M RVSort.K) : Prop :=
  ∀ t : Finset (Polynomial F), ∃ b : N RVSort.K, ∀ P ∈ t, ∀ Q ∈ t,
    (valMap (rvMap (evalOn F.subtype a P)) ≤ valMap (rvMap (evalOn F.subtype a Q))
      ↔ valMap (rvMap (evalOn' d.hom b P)) ≤ valMap (rvMap (evalOn' d.hom b Q)))

variable {F d}

/-- **The algebraic sub-cases in one line.** A single element of the target reflecting the order
of the values of *all* polynomials serves every finite set at once. -/
theorem valuePatternAt_of_reflectData {a : M RVSort.K} {b : N RVSort.K}
    (h : ReflectData F.subtype d.hom (modelValSubring M) (modelValSubring N) a b) :
    ValuePatternAt F d a := fun _ => ⟨b, fun P _ Q _ => by
  rw [valMap_le_iff_valuation, valMap_le_iff_valuation]
  exact h.valLe Q P⟩

variable (F d) in
/-- **The order of values on the coefficient field is the same on both sides** — what a
`FieldEmbeddingData` supplies, in the terms `Algebra/ACVF/ValuedField/Extend.lean` states its
cases in. -/
theorem coeffReflect_of_fieldEmbeddingData :
    CoeffReflect F.subtype d.hom (modelValSubring M) (modelValSubring N) := fun r r' => by
  rw [← valMap_le_iff_valuation, ← valMap_le_iff_valuation]
  exact d.val_iff r' r

/-! ### The five cases

Each takes an element of the field sort in one of Rideau-Kikuchi's positions relative to `F` and
returns the pattern. The two algebraic ones return the stronger `ReflectData`, from which
`valuePatternAt_of_reflectData` reads the pattern off. -/

variable (F d)

/-! #### Ramified of infinite order

No power of the value of `a` is a value of `F`, so one monomial dominates every polynomial and
`RamifiedMonoOn` is all that is asked of the far-side element. After
`mul_pow_lt_mul_pow_iff` that hypothesis says nothing but where the powers `w b ^ m` sit among the
values of the ratios of the finitely many coefficients — a *finite* cut — so `b` is built rather
than found: `exists_cut_witness` separates two finite families of values by a geometric mean and
takes a `D!`-th root. -/

/-- The ramification hypothesis, in the valued field the model recovers. -/
theorem valuation_pow_ne_of_ramified {a : M RVSort.K}
    (hord : ∀ k : ℕ, 0 < k → ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c)) :
    ∀ k : ℕ, 0 < k → ∀ c : F,
      (modelValSubring M).valuation a ^ k
        ≠ (modelValSubring M).valuation (F.subtype c) := by
  intro k hk c hc
  refine hord k hk (F.subtype c) c.2 ?_
  rw [valMap_eq_iff_valuation, map_pow]
  exact hc

/-- **The cut is realized in the target.** For a finite set `S` of nonzero elements of `F` and a
bound `D`, some `b` of the target compares to every `w (ψ s)` as `val a` compares to `v (φ s)`, at
every exponent `m < D`.

The construction: `Kn = D!` is a common denominator for the exponents, so each condition at `m`
becomes one at `Kn` on `ψ (s ^ (Kn / m))`; the two finite families so obtained are separated by
`exists_valuation_between`, which takes the geometric mean of the extreme bounds; and `b` is a
`Kn`-th root of the separating element. The ramification hypothesis is what rules out equality on
the near side, and so turns the two one-sided conditions into equivalences. -/
theorem exists_cut_witness {a : M RVSort.K} (ha0 : a ≠ 0)
    (hord : ∀ k : ℕ, 0 < k → ∀ c : F,
      (modelValSubring M).valuation a ^ k ≠ (modelValSubring M).valuation (F.subtype c))
    (S : Finset F) (hSne : ∀ s ∈ S, s ≠ 0) (D : ℕ) :
    ∃ b : N RVSort.K, b ≠ 0 ∧ ∀ m < D, ∀ s ∈ S,
      ((modelValSubring M).valuation (F.subtype s) < (modelValSubring M).valuation a ^ m
        ↔ (modelValSubring N).valuation (d.hom s) < (modelValSubring N).valuation b ^ m) ∧
      ((modelValSubring M).valuation a ^ m < (modelValSubring M).valuation (F.subtype s)
        ↔ (modelValSubring N).valuation b ^ m < (modelValSubring N).valuation (d.hom s)) := by
  classical
  have hcoeff : CoeffReflect F.subtype d.hom (modelValSubring M) (modelValSubring N) :=
    coeffReflect_of_fieldEmbeddingData F d
  have hγ0 : (modelValSubring M).valuation a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
  -- the common denominator of the exponents in play
  set Kn : ℕ := Nat.factorial D with hKndef
  have hKn0 : 0 < Kn := Nat.factorial_pos D
  have hdvd : ∀ m ∈ Finset.Ico 1 D, m ∣ Kn := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    exact Nat.dvd_factorial hm.1 (le_of_lt hm.2)
  have hquot : ∀ m ∈ Finset.Ico 1 D, 0 < Kn / m := fun m hm =>
    Nat.div_pos (Nat.le_of_dvd hKn0 (hdvd m hm)) (Finset.mem_Ico.mp hm).1
  have hpowKnM : ∀ (g : (modelValSubring M).ValueGroup), ∀ m ∈ Finset.Ico 1 D,
      (g ^ m) ^ (Kn / m) = g ^ Kn := fun g m hm => by
    rw [← pow_mul, Nat.mul_div_cancel' (hdvd m hm)]
  have hpowKnN : ∀ (g : (modelValSubring N).ValueGroup), ∀ m ∈ Finset.Ico 1 D,
      (g ^ m) ^ (Kn / m) = g ^ Kn := fun g m hm => by
    rw [← pow_mul, Nat.mul_div_cancel' (hdvd m hm)]
  -- the two finite families of bounds in the target
  set Lo : Finset (N RVSort.K) :=
    (((Finset.Ico 1 D) ×ˢ S).filter fun p => (modelValSubring M).valuation
        (F.subtype p.2) < (modelValSubring M).valuation a ^ p.1).image
      (fun p => d.hom (p.2 ^ (Kn / p.1))) with hLodef
  set Hi : Finset (N RVSort.K) :=
    (((Finset.Ico 1 D) ×ˢ S).filter fun p => (modelValSubring M).valuation a ^ p.1
        < (modelValSubring M).valuation (F.subtype p.2)).image
      (fun p => d.hom (p.2 ^ (Kn / p.1))) with hHidef
  have hne : ∀ (p : ℕ × F), p.2 ∈ S → d.hom (p.2 ^ (Kn / p.1)) ≠ 0 := fun p hp h0 =>
    pow_ne_zero _ (hSne p.2 hp) (d.hom_injective (by rw [h0, map_zero]))
  have hLo : ∀ l ∈ Lo, l ≠ 0 := by
    intro l hl
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
    exact hne p (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  have hHi : ∀ h ∈ Hi, h ≠ 0 := by
    intro h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    exact hne p (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  have hsep : ∀ l ∈ Lo, ∀ h ∈ Hi,
      (modelValSubring N).valuation l < (modelValSubring N).valuation h := by
    intro l hl h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hpidx, hplt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqidx, hqlt⟩ := Finset.mem_filter.mp hq
    have hpm := (Finset.mem_product.mp hpidx).1
    have hqm := (Finset.mem_product.mp hqidx).1
    rw [← hcoeff.lt_iff, map_pow, map_pow, map_pow, map_pow]
    calc (modelValSubring M).valuation (F.subtype p.2) ^ (Kn / p.1)
        < ((modelValSubring M).valuation a ^ p.1) ^ (Kn / p.1) :=
          pow_lt_pow_left₀ hplt zero_le (hquot p.1 hpm).ne'
      _ = (modelValSubring M).valuation a ^ Kn := hpowKnM _ p.1 hpm
      _ = ((modelValSubring M).valuation a ^ q.1) ^ (Kn / q.1) := (hpowKnM _ q.1 hqm).symm
      _ < (modelValSubring M).valuation (F.subtype q.2) ^ (Kn / q.1) :=
          pow_lt_pow_left₀ hqlt zero_le (hquot q.1 hqm).ne'
  -- an element of the target whose `Kn`-th power of value separates the two families
  obtain ⟨b, hb0, hyLo, hyHi⟩ := exists_pow_valuation_between (A := modelValSubring N)
    (modelValSubring_nontrivial (M := N)) hKn0 Lo Hi hLo hHi hsep
  -- the one-sided conditions, straight off the separation
  have cutlo : ∀ m ∈ Finset.Ico 1 D, ∀ s ∈ S,
      (modelValSubring M).valuation (F.subtype s) < (modelValSubring M).valuation a ^ m →
      (modelValSubring N).valuation (d.hom s) < (modelValSubring N).valuation b ^ m := by
    intro m hm s hs hlt
    have h := hyLo _ (Finset.mem_image.mpr
      ⟨(m, s), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm, hs⟩, hlt⟩, rfl⟩)
    rw [map_pow, map_pow, ← hpowKnN ((modelValSubring N).valuation b) m hm] at h
    exact (pow_lt_pow_iff_left₀ zero_le zero_le (hquot m hm).ne').mp h
  have cuthi : ∀ m ∈ Finset.Ico 1 D, ∀ s ∈ S,
      (modelValSubring M).valuation a ^ m < (modelValSubring M).valuation (F.subtype s) →
      (modelValSubring N).valuation b ^ m < (modelValSubring N).valuation (d.hom s) := by
    intro m hm s hs hlt
    have h := hyHi _ (Finset.mem_image.mpr
      ⟨(m, s), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm, hs⟩, hlt⟩, rfl⟩)
    rw [map_pow, map_pow, ← hpowKnN ((modelValSubring N).valuation b) m hm] at h
    exact (pow_lt_pow_iff_left₀ zero_le zero_le (hquot m hm).ne').mp h
  -- and they are equivalences, because the near side admits no equality
  have h1K : (modelValSubring M).valuation (F.subtype (1 : F)) = 1 := by rw [map_one, map_one]
  have h1L : (modelValSubring N).valuation (d.hom (1 : F)) = 1 := by rw [map_one, map_one]
  refine ⟨b, hb0, fun m hm s hs => ⟨?_, ?_⟩⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero, pow_zero, ← h1K, ← h1L]
      exact hcoeff.lt_iff s 1
    · refine ⟨cutlo m (Finset.mem_Ico.mpr ⟨hm0, hm⟩) s hs, fun h => ?_⟩
      by_contra hcon
      push Not at hcon
      exact absurd (cuthi m (Finset.mem_Ico.mpr ⟨hm0, hm⟩) s hs
        (lt_of_le_of_ne hcon (hord m hm0 s))) (not_lt.mpr (le_of_lt h))
  · rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero, pow_zero, ← h1K, ← h1L]
      exact hcoeff.lt_iff 1 s
    · refine ⟨cuthi m (Finset.mem_Ico.mpr ⟨hm0, hm⟩) s hs, fun h => ?_⟩
      by_contra hcon
      push Not at hcon
      exact absurd (cutlo m (Finset.mem_Ico.mpr ⟨hm0, hm⟩) s hs
        (lt_of_le_of_ne hcon (Ne.symm (hord m hm0 s)))) (not_lt.mpr (le_of_lt h))

/-- **The bounded domination hypothesis from the cut.** A comparison of two monomials is, by
`mul_pow_lt_mul_pow_iff`, a comparison of the ratio of their coefficients with a power of the
value; so the cut conditions are exactly what `RamifiedMonoOn` asks for. -/
theorem ramifiedMonoOn_of_cut {a : M RVSort.K} {b : N RVSort.K} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (C S : Finset F) (D : ℕ)
    (hmemS : ∀ r ∈ C, ∀ r' ∈ C, r / r' ≠ 0 → r / r' ∈ S)
    (hcut : ∀ m < D, ∀ s ∈ S,
      ((modelValSubring M).valuation (F.subtype s) < (modelValSubring M).valuation a ^ m
        ↔ (modelValSubring N).valuation (d.hom s) < (modelValSubring N).valuation b ^ m) ∧
      ((modelValSubring M).valuation a ^ m < (modelValSubring M).valuation (F.subtype s)
        ↔ (modelValSubring N).valuation b ^ m < (modelValSubring N).valuation (d.hom s))) :
    RamifiedMonoOn (C : Set F) D F.subtype d.hom
      (modelValSubring M) (modelValSubring N) a b := by
  have hγ0 : (modelValSubring M).valuation a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
  have hδ0 : (modelValSubring N).valuation b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0
  have hzeroK : ∀ (x : F) (j : ℕ),
      (modelValSubring M).valuation (F.subtype x)
        * (modelValSubring M).valuation a ^ j = 0 ↔ x = 0 := by
    intro x j
    rw [mul_eq_zero, or_iff_left (pow_ne_zero j hγ0), Valuation.zero_iff]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  have hzeroL : ∀ (x : F) (j : ℕ),
      (modelValSubring N).valuation (d.hom x)
        * (modelValSubring N).valuation b ^ j = 0 ↔ x = 0 := by
    intro x j
    rw [mul_eq_zero, or_iff_left (pow_ne_zero j hδ0), Valuation.zero_iff]
    exact ⟨fun h => d.hom_injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  intro r hr r' hr' i hi i' hi'
  by_cases hr0 : r = 0
  · subst hr0
    rw [(hzeroK 0 i).mpr rfl, (hzeroL 0 i).mpr rfl, pos_iff_ne_zero, pos_iff_ne_zero, ne_eq, ne_eq,
      hzeroK, hzeroL]
  by_cases hr'0 : r' = 0
  · subst hr'0
    rw [(hzeroK 0 i').mpr rfl, (hzeroL 0 i').mpr rfl]
    exact ⟨fun h => absurd h (not_lt_of_ge zero_le), fun h => absurd h (not_lt_of_ge zero_le)⟩
  have hvrK : (modelValSubring M).valuation (F.subtype r) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact fun h => hr0 (Subtype.ext h)
  have hvr'K : (modelValSubring M).valuation (F.subtype r') ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact fun h => hr'0 (Subtype.ext h)
  have hvrL : (modelValSubring N).valuation (d.hom r) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact fun h => hr0 (d.hom_injective (by rw [h, map_zero]))
  have hvr'L : (modelValSubring N).valuation (d.hom r') ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact fun h => hr'0 (d.hom_injective (by rw [h, map_zero]))
  rcases Nat.lt_or_ge i' i with hii | hii
  · obtain ⟨m, rfl⟩ : ∃ m, i = i' + m := ⟨i - i', by omega⟩
    rw [mul_pow_lt_mul_pow_iff' hvrK hγ0 i' m, mul_pow_lt_mul_pow_iff' hvrL hδ0 i' m,
      ← map_div₀ (modelValSubring M).valuation, ← map_div₀ F.subtype,
      ← map_div₀ (modelValSubring N).valuation, ← map_div₀ d.hom]
    exact (hcut m (by omega) _ (hmemS r' hr' r hr (div_ne_zero hr'0 hr0))).2
  · obtain ⟨m, rfl⟩ : ∃ m, i' = i + m := ⟨i' - i, by omega⟩
    rw [mul_pow_lt_mul_pow_iff hvr'K hγ0 i m, mul_pow_lt_mul_pow_iff hvr'L hδ0 i m,
      ← map_div₀ (modelValSubring M).valuation, ← map_div₀ F.subtype,
      ← map_div₀ (modelValSubring N).valuation, ← map_div₀ d.hom]
    exact (hcut m (by omega) _ (hmemS r hr r' hr' (div_ne_zero hr0 hr'0))).1

/-- **Ramified, infinite order** — generic. -/
theorem valuePatternAt_ramified_infinite {a : M RVSort.K} (ha0 : a ≠ 0)
    (hord : ∀ k : ℕ, 0 < k → ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c)) :
    ValuePatternAt F d a := by
  classical
  intro t
  set D : ℕ := (t.sup fun P => P.natDegree) + 1 with hDdef
  set C : Finset F := insert 0 (t.biUnion fun P => P.coeffs) with hCdef
  have hcoeffC : ∀ P ∈ t, ∀ i, P.coeff i ∈ C := by
    intro P hP i
    by_cases h : P.coeff i = 0
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨P, hP, P.coeff_mem_coeffs h⟩)
  set S : Finset F := ((C ×ˢ C).image fun p => p.1 / p.2).erase 0 with hSdef
  have hmemS : ∀ r ∈ C, ∀ r' ∈ C, r / r' ≠ 0 → r / r' ∈ S := fun r hr r' hr' h0 =>
    Finset.mem_erase.mpr ⟨h0,
      Finset.mem_image.mpr ⟨(r, r'), Finset.mem_product.mpr ⟨hr, hr'⟩, rfl⟩⟩
  obtain ⟨b, hb0, hcut⟩ := exists_cut_witness F d ha0
    (valuation_pow_ne_of_ramified F hord) S (fun s hs => (Finset.mem_erase.mp hs).1) D
  refine ⟨b, fun P hP Q hQ => ?_⟩
  rw [valMap_le_iff_valuation, valMap_le_iff_valuation]
  exact valuation_le_iff_of_ramified (ramifiedMonoOn_of_cut F d ha0 hb0 C S D hmemS hcut) ha0 hb0
    (ord_of_model F (n := D) (fun k hk _ => hord k hk))
    (Nat.lt_succ_of_le (Finset.le_sup hQ)) (Nat.lt_succ_of_le (Finset.le_sup hP))
    (fun i => hcoeffC Q hQ i) (fun i => hcoeffC P hP i)

/-- **Ramified, finite order `n`** — algebraic: `aⁿ` lies in `F`, so the far-side element is an
`n`-th root of its image and the whole `ReflectData` is available. -/
theorem exists_reflectData_ramified_finite {a : M RVSort.K} (ha0 : a ≠ 0) {n : ℕ} (hn : 0 < n)
    (hord : ∀ k : ℕ, 0 < k → k < n → ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c))
    {c : F} (hac : a ^ n = (c : M RVSort.K)) :
    ∃ b : N RVSort.K,
      ReflectData F.subtype d.hom (modelValSubring M) (modelValSubring N) a b := by
  classical
  have hc0 : (c : M RVSort.K) ≠ 0 := by rw [← hac]; exact pow_ne_zero n ha0
  have hcne : c ≠ 0 := fun h => hc0 (by rw [h]; rfl)
  have hdc0 : d.hom c ≠ 0 := fun h => hcne (d.hom_injective (by rw [h, map_zero]))
  obtain ⟨b, hbc⟩ := IsAlgClosed.exists_pow_nat_eq (d.hom c) hn
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hbc
    exact hdc0 hbc.symm
  refine ⟨b, (ramifiedReflectAll_finite_of_model F d ha0 hb0 hn ?_ hord hac hbc).toReflectData⟩
  -- the monomials are ordered alike: raise to the `n`-th power and compare inside `F`
  have keyM : ∀ (s : F) (j : ℕ),
      (modelValSubring M).valuation ((s : M RVSort.K) * a ^ j) ^ n
        = (modelValSubring M).valuation (((s ^ n * c ^ j : F) : M RVSort.K)) := by
    intro s j
    have hcast : (((s ^ n * c ^ j : F)) : M RVSort.K)
        = (s : M RVSort.K) ^ n * (c : M RVSort.K) ^ j := by push_cast; ring
    rw [hcast]
    simp only [map_mul, map_pow, mul_pow]
    rw [← hac, map_pow, ← pow_mul, ← pow_mul, mul_comm j n]
  have keyN : ∀ (s : F) (j : ℕ),
      (modelValSubring N).valuation (d.hom s * b ^ j) ^ n
        = (modelValSubring N).valuation (d.hom (s ^ n * c ^ j)) := by
    intro s j
    simp only [map_mul, map_pow, mul_pow]
    rw [← hbc, map_pow, ← pow_mul, ← pow_mul, mul_comm j n]
  have hstrict : ∀ x y : F, (modelValSubring M).valuation (x : M RVSort.K)
      < (modelValSubring M).valuation (y : M RVSort.K)
      ↔ (modelValSubring N).valuation (d.hom x) < (modelValSubring N).valuation (d.hom y) := by
    intro x y
    rw [← not_le, ← not_le, not_iff_not]
    exact coeffReflect_of_fieldEmbeddingData F d y x
  have main : ∀ (s s' : F) (j j' : ℕ),
      (modelValSubring M).valuation ((s : M RVSort.K) * a ^ j)
        < (modelValSubring M).valuation ((s' : M RVSort.K) * a ^ j')
      ↔ (modelValSubring N).valuation (d.hom s * b ^ j)
        < (modelValSubring N).valuation (d.hom s' * b ^ j') := by
    intro s s' j j'
    refine (pow_lt_pow_iff_left₀ zero_le zero_le hn.ne').symm.trans
      (Iff.trans ?_ (pow_lt_pow_iff_left₀ zero_le zero_le hn.ne'))
    rw [keyM, keyM, keyN, keyN]
    exact hstrict _ _
  intro r r' i i'
  rw [valMap_lt_iff_valuation, valMap_lt_iff_valuation]
  exact main r' r i' i

/-- **Residual, transcendental** — generic. The value of a polynomial at `a` is the largest value
among its coefficients (Proposition 2.1.5), so the far-side element is a unit whose residue avoids
the finitely many algebraic conditions the given polynomials impose. -/
theorem valuePatternAt_residual_transcendental {a : modelValSubring M}
    (htr : ∀ R : (modelValSubring M)[X],
      (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F) →
      R.map (residue (modelValSubring M)) ≠ 0 →
      (R.map (residue (modelValSubring M))).eval (residue (modelValSubring M) a) ≠ 0) :
    ValuePatternAt F d ((a : modelValSubring M) : M RVSort.K) := by
  classical
  intro t
  -- the degree bound and the finite set of coefficient ratios the given polynomials form
  set n : ℕ := (t.sup fun P => P.natDegree) + 1 with hndef
  set E : Finset F := insert 0 (t.biUnion fun P => P.coeffs) with hEdef
  set D : Finset F := (E ×ˢ E).image fun p => p.2⁻¹ * p.1 with hDdef
  have hcoeffE : ∀ P ∈ t, ∀ i, P.coeff i ∈ E := by
    intro P hP i
    by_cases h : P.coeff i = 0
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨P, hP, P.coeff_mem_coeffs h⟩)
  have hmemD : ∀ P ∈ t, ∀ i j : ℕ, (P.coeff j)⁻¹ * P.coeff i ∈ (D : Set F) := by
    intro P hP i j
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨(P.coeff i, P.coeff j), Finset.mem_product.mpr ⟨hcoeffE P hP i, hcoeffE P hP j⟩, rfl⟩)
  -- the near side: full transcendence is more than enough
  have hdegK : ResidualDegOn (F.subtype '' (D : Set F)) (modelValSubring M) a n := by
    intro RQ hRQ _ hne
    exact htr RQ (fun i => by obtain ⟨r, -, hr⟩ := hRQ i; rw [← hr]; exact r.2) hne
  -- the far side: a residue avoiding the finitely many polynomials the `D` produce
  set resOf : F → ResidueField (modelValSubring N) := fun r =>
    if h : d.hom r ∈ modelValSubring N then residue (modelValSubring N) ⟨d.hom r, h⟩ else 0
    with hresOf
  set E' : Finset (ResidueField (modelValSubring N)) :=
    insert 0 (insert 1 (D.image resOf)) with hE'
  obtain ⟨ρ, hρ⟩ := exists_forall_eval_ne_zero_of_coeffs_mem E' (max n 2)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ρ
  have hdegL : ResidualDegOn (d.hom '' (D : Set F)) (modelValSubring N) b n := by
    intro RQ hRQ hRQn hne
    have hb' : residue (modelValSubring N) b = ρ := hb
    rw [hb']
    refine hρ (RQ.map (residue (modelValSubring N))) hne
      (lt_of_le_of_lt Polynomial.natDegree_map_le (lt_of_lt_of_le hRQn (le_max_left _ _)))
      fun i => ?_
    obtain ⟨r, hrD, hr⟩ := hRQ i
    have hmem : d.hom r ∈ modelValSubring N := by rw [hr]; exact (RQ.coeff i).2
    have heq : (RQ.coeff i : modelValSubring N) = ⟨d.hom r, hmem⟩ := Subtype.ext hr.symm
    rw [Polynomial.coeff_map, heq]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, ?_, ?_⟩))
    · exact Finset.mem_coe.mp hrD
    · exact dite_eq_left hmem
  refine ⟨((b : modelValSubring N) : N RVSort.K), fun P hP Q hQ => ?_⟩
  rw [valMap_le_iff_valuation, valMap_le_iff_valuation]
  exact valuation_le_iff_of_residual_on (coeffReflect_of_fieldEmbeddingData F d) hdegK hdegL
    (Nat.lt_succ_of_le (Finset.le_sup hQ)) (Nat.lt_succ_of_le (Finset.le_sup hP))
    (hmemD Q hQ) (hmemD P hP)

/-- **Residual, algebraic of degree `n`** — algebraic: the far-side element is a root of the image
of the monic polynomial `a` satisfies, and its non-degeneracy in degree `n` comes from `d` being
an isomorphism of `F` onto its image. -/
theorem exists_reflectData_residual_algebraic {a : modelValSubring M} {n : ℕ} (hn : 0 < n)
    {P : F[X]} (hPm : P.Monic) (hPn : P.natDegree = n)
    (hPint : ∀ i, ((P.coeff i : F) : M RVSort.K) ∈ modelValSubring M)
    (hPa : evalOn F.subtype ((a : modelValSubring M) : M RVSort.K) P = 0)
    (hdeg : ResidualDeg F.subtype (modelValSubring M) a n) :
    ∃ b : N RVSort.K,
      ReflectData F.subtype d.hom (modelValSubring M) (modelValSubring N)
        ((a : modelValSubring M) : M RVSort.K) b := by
  classical
  have hcoeff : CoeffReflect F.subtype d.hom (modelValSubring M) (modelValSubring N) :=
    coeffReflect_of_fieldEmbeddingData F d
  -- lift `P` to the valuation ring of `F`
  have hlifts : P ∈ Polynomial.lifts
      (coeffValRing (modelValSubring M) F.subtype).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun i => ⟨⟨P.coeff i, hPint i⟩, rfl⟩
  obtain ⟨P₀, hP₀map, hP₀deg, hP₀m⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hPm
  have hP₀n : P₀.natDegree = n := by rw [Polynomial.natDegree_eq_of_degree_eq hP₀deg, hPn]
  -- the two readings of `P₀` in the field sort
  have hcompK : (modelValSubring M).subtype.comp
        (coeffValRingHomK (modelValSubring M) F.subtype)
      = F.subtype.comp (coeffValRing (modelValSubring M) F.subtype).subtype :=
    RingHom.ext fun _ => rfl
  have hcompL : (modelValSubring N).subtype.comp (coeffValRingHomL hcoeff)
      = d.hom.comp (coeffValRing (modelValSubring M) F.subtype).subtype :=
    RingHom.ext fun _ => rfl
  have hmapK : (P₀.map (coeffValRingHomK (modelValSubring M) F.subtype)).map
      (modelValSubring M).subtype = P.map F.subtype := by
    rw [Polynomial.map_map, hcompK, ← Polynomial.map_map, hP₀map]
  have hmapL : (P₀.map (coeffValRingHomL hcoeff)).map (modelValSubring N).subtype
      = P.map d.hom := by
    rw [Polynomial.map_map, hcompL, ← Polynomial.map_map, hP₀map]
  -- `a` is a root of the near-side reading
  have hPa' : (P₀.map (coeffValRingHomK (modelValSubring M) F.subtype)).eval a = 0 := by
    have h : (((P₀.map (coeffValRingHomK (modelValSubring M) F.subtype)).eval a
        : modelValSubring M) : M RVSort.K) = 0 := by
      rw [eval_coe_valSubring, hmapK, Polynomial.eval_map]
      exact hPa
    exact ZeroMemClass.coe_eq_zero.mp h
  -- and the far-side reading has a root, its field being algebraically closed
  have hmonL : (P₀.map (coeffValRingHomL hcoeff)).Monic := hP₀m.map _
  have hdeg0 : ((P₀.map (coeffValRingHomL hcoeff)).map
      (modelValSubring N).subtype).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hmonL.map _).ne_zero, hmonL.natDegree_map,
      hP₀m.natDegree_map, hP₀n]
    exact_mod_cast hn.ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg0
  have hyB : y ∈ modelValSubring N := mem_of_monic_eval_eq_zero hmonL hy
  have hPb' : (P₀.map (coeffValRingHomL hcoeff)).eval ⟨y, hyB⟩ = 0 := by
    refine ZeroMemClass.coe_eq_zero.mp ?_
    rw [eval_coe_valSubring]
    exact hy
  -- the degree of the residue transfers, which is the one thing the far side has to satisfy
  have hdegL : ResidualDeg d.hom (modelValSubring N) ⟨y, hyB⟩ n :=
    residualDeg_transfer hcoeff hP₀m hP₀n hPa' hPb' hdeg
  refine ⟨y, reflectData_of_residual_modByMonic hn hcoeff hdeg hdegL hPm (le_of_eq hPn) hPa ?_⟩
  have h : ((( P₀.map (coeffValRingHomL hcoeff)).eval ⟨y, hyB⟩ : modelValSubring N)
      : N RVSort.K) = 0 := by rw [hPb', ZeroMemClass.coe_zero]
  rw [eval_coe_valSubring, hmapL, Polynomial.eval_map] at h
  exact h

/-! ### The routing -/

/-- **The residual routing.** A unit of the valuation ring whose leading term is not a leading term
of `F` is transcendental or algebraic over the residues of `F`. -/
theorem exists_valuePatternAt_residual_of_unit {u : modelValSubring M} (hu : IsUnit u)
    (huF : ∀ x ∈ F, rvMap x ≠ rvMap ((u : modelValSubring M) : M RVSort.K)) :
    ∃ a : M RVSort.K, a ∉ F ∧ ValuePatternAt F d a := by
  classical
  by_cases halg : ∃ n, ResidueMonicDeg F (residue (modelValSubring M) u) n
  · obtain ⟨n, P, a, hPm, hPn, hPint, hares, hPa, hmin⟩ := exists_residual_root F halg
    have hρ0 : residue (modelValSubring M) u ≠ 0 := (residue_ne_zero_iff_isUnit u).mpr hu
    have hau : IsUnit a := by
      rw [← residue_ne_zero_iff_isUnit, hares]
      exact hρ0
    have hrv : rvMap ((a : modelValSubring M) : M RVSort.K)
        = rvMap ((u : modelValSubring M) : M RVSort.K) :=
      rvMap_eq_iff_rv_eq.mpr ((rv_eq_iff_residue_eq hu).mpr hares)
    have haF : ((a : modelValSubring M) : M RVSort.K) ∉ F := fun hc => huF _ hc hrv
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact absurd (hPm.natDegree_eq_zero.mp hPn) (by
          intro h1
          rw [h1] at hPa
          simp at hPa)
      · exact hn
    have hdeg : ResidualDeg F.subtype (modelValSubring M) a n := by
      intro R hRF hRn hRne
      have hRF' : ∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F := by
        intro i
        obtain ⟨x, hx⟩ := hRF i
        exact hx ▸ x.2
      rw [hares]
      exact hmin R hRF' hRn hRne
    obtain ⟨b, hb⟩ :=
      exists_reflectData_residual_algebraic F d hn hPm hPn hPint hPa hdeg
    exact ⟨_, haF, valuePatternAt_of_reflectData hb⟩
  · push Not at halg
    have htr : ∀ R : (modelValSubring M)[X],
        (∀ i, ((R.coeff i : modelValSubring M) : M RVSort.K) ∈ F) →
        R.map (residue (modelValSubring M)) ≠ 0 →
        (R.map (residue (modelValSubring M))).eval
          (residue (modelValSubring M) u) ≠ 0 := fun R hRF hRne hRz =>
      halg _ (residueMonicDeg_of_eval_eq_zero F hRF hRne hRz)
    exact ⟨_, fun hc => huF _ hc rfl, valuePatternAt_residual_transcendental F d htr⟩

/-- **The routing, for an element whose leading term is not a leading term of `F`.** The case
distinction is the order of its value over the values of `F`, exactly as in
`exists_lift_of_notMem`. -/
theorem exists_valuePatternAt_of_rv_notMem {z : M RVSort.K} (hz0 : z ≠ 0)
    (hzF : ∀ x ∈ F, rvMap x ≠ rvMap z) :
    ∃ a : M RVSort.K, a ∉ F ∧ ValuePatternAt F d a := by
  classical
  by_cases hord : ∀ k : ℕ, 0 < k → ∀ c ∈ F, valMap (rvMap (z ^ k)) ≠ valMap (rvMap c)
  · exact ⟨z, fun hc => hzF z hc rfl, valuePatternAt_ramified_infinite F d hz0 hord⟩
  have hex : ∃ k : ℕ, 0 < k ∧ ∃ c ∈ F, valMap (rvMap (z ^ k)) = valMap (rvMap c) := by
    by_contra hc
    exact hord fun k hk c hcF hceq => hc ⟨k, hk, c, hcF, hceq⟩
  obtain ⟨hn, c, hcF, hceq⟩ := Nat.find_spec hex
  have hmin : ∀ k : ℕ, 0 < k → k < Nat.find hex → ∀ e ∈ F,
      valMap (rvMap (z ^ k)) ≠ valMap (rvMap e) := fun k hk hkn e heF hdeq =>
    Nat.find_min hex hkn ⟨hk, e, heF, hdeq⟩
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, model_val_zero] at hceq
    exact hz0 ((pow_eq_zero_iff hn.ne').mp (model_val_eq_top_iff.mp hceq))
  by_cases hpow : ∃ e ∈ F, rvMap e = rvMap (z ^ Nat.find hex)
  · -- ramified of finite order: replace `z` by an `n`-th root of `e` with the same leading term
    obtain ⟨e, heF, hdeq⟩ := hpow
    have hζ : (rv (A := modelValSubring M) z) ^ Nat.find hex
        = rv (A := modelValSubring M) e := by
      have h := (rvMap_eq_iff_rv_eq.mp hdeq).symm
      rw [map_pow] at h
      exact h
    obtain ⟨a, hapow, harv⟩ := exists_pow_eq_rv_eq (A := modelValSubring M) hn hζ
    have harvM : rvMap a = rvMap z := rvMap_eq_iff_rv_eq.mpr harv
    have ha0 : a ≠ 0 := by
      intro h
      refine hz0 (model_rv_eq_zero_iff.mp ?_)
      rw [← harvM, h, model_rv_zero]
    have hord' : ∀ k : ℕ, 0 < k → k < Nat.find hex → ∀ e' ∈ F,
        valMap (rvMap (a ^ k)) ≠ valMap (rvMap e') := by
      intro k hk hkn e' he'F
      rw [rvMap_pow_congr harvM k]
      exact hmin k hk hkn e' he'F
    obtain ⟨b, hb⟩ := exists_reflectData_ramified_finite F d ha0 hn hord'
      (c := ⟨e, heF⟩) hapow
    exact ⟨a, fun hcc => hzF a hcc harvM, valuePatternAt_of_reflectData hb⟩
  · -- residual: scale into the residue fiber by a coefficient of the same value
    push Not at hpow
    have hrvc0 : rv (A := modelValSubring M) c ≠ 0 := by
      rw [ne_eq, rv_eq_zero_iff]
      exact hc0
    have huval : (modelValSubring M).valuation (z ^ Nat.find hex / c) = 1 := by
      rw [map_div₀, (valMap_eq_iff_valuation _ _).mp hceq,
        div_self ((Valuation.ne_zero_iff _).mpr hc0)]
    have huA : z ^ Nat.find hex / c ∈ modelValSubring M :=
      (modelValSubring M).mem_of_valuation_le_one _ (le_of_eq huval)
    have huUnit : IsUnit (⟨z ^ Nat.find hex / c, huA⟩ : modelValSubring M) :=
      ((modelValSubring M).valuation_eq_one_iff _).mpr huval
    have huF : ∀ x ∈ F, rvMap x ≠ rvMap (z ^ Nat.find hex / c) := by
      intro x hx hxu
      refine hpow (x * c) (F.mul_mem hx hcF) (rvMap_eq_iff_rv_eq.mpr ?_)
      rw [map_mul, rvMap_eq_iff_rv_eq.mp hxu, map_div₀, div_mul_cancel₀ _ hrvc0]
    exact exists_valuePatternAt_residual_of_unit F d huUnit huF

/-! ### Reading the two kinds of comparison

The conditions the immediate case puts on the far-side element are comparisons of values of
*linear* polynomials, together with one comparison against the zero polynomial. Both are read off
here, so that they can be fed to the restricted value-comparison type. -/

/-- The comparison against the zero polynomial says exactly that `b` is a root. -/
theorem valLe_zero_iff {T : RVSort → Type w} [rvLang.Structure T] [T ⊨ ACVFTheory]
    {F : Subfield (M RVSort.K)} (χ : F →+* T RVSort.K) (b : T RVSort.K) (P : Polynomial F) :
    (valMap (rvMap (evalOn' χ b (0 : Polynomial F))) ≤ valMap (rvMap (evalOn' χ b P)))
      ↔ (P.map χ).eval b = 0 := by
  rw [map_zero, show evalOn' χ b P = (P.map χ).eval b from (Polynomial.eval_map _ _).symm,
    valMap_le_iff_valuation, map_zero]
  exact ⟨fun h => (Valuation.zero_iff _).mp (le_antisymm h zero_le),
    fun h => by rw [h, map_zero]⟩

/-- The comparison of the two linear polynomials says exactly that `b` is at leading-term
distance `rv (χ u)` from `χ r`. -/
theorem valLe_linear_iff {T : RVSort → Type w} [rvLang.Structure T] [T ⊨ ACVFTheory]
    {F : Subfield (M RVSort.K)} (χ : F →+* T RVSort.K) (b : T RVSort.K) {u : F} (r : F)
    (hu : χ u ≠ 0) :
    (¬ (valMap (rvMap (evalOn' χ b (Polynomial.C (u + r) - Polynomial.X)))
        ≤ valMap (rvMap (evalOn' χ b (Polynomial.X - Polynomial.C r)))))
      ↔ rv (A := modelValSubring T) (b - χ r) = rv (A := modelValSubring T) (χ u) := by
  rw [show evalOn' χ b (Polynomial.C (u + r) - Polynomial.X) = χ (u + r) - b by simp,
    show evalOn' χ b (Polynomial.X - Polynomial.C r) = b - χ r by simp,
    valMap_le_iff_valuation, not_le,
    show χ (u + r) - b = χ u - (b - χ r) by rw [map_add]; ring]
  by_cases h0 : b - χ r = 0
  · rw [h0, map_zero, sub_zero, rv_zero]
    exact ⟨fun hc => absurd hc (not_lt.mpr zero_le),
      fun hc => absurd (rv_eq_zero_iff.mp hc.symm) hu⟩
  · exact (rv_eq_iff_valuation_sub_lt h0).symm

/-! ### The routing in full

`FieldStep` lets the target grow, so what the routing has to deliver is an `a ∉ F` whose pattern
is realized in an elementary extension of `N`. The four cases above deliver the *finite* fragment
in `N` itself, and `exists_reflectData_ext_of_finsat` turns that into the whole pattern by
compactness; the immediate algebraic case delivers the extension directly, because there the
far-side element must be a root of an image polynomial **and** at prescribed distances from the
whole coefficient field, which no element of `N` need satisfy. -/

section Routing

variable {M N : RVSort → Type 0} [rvLang.Structure M] [rvLang.Structure N]
  [∀ s, Nonempty (M s)] [∀ s, Nonempty (N s)] [M ⊨ ACVFTheory] [N ⊨ ACVFTheory]
variable (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)

/-- The conclusion each branch of the routing delivers: an element outside `F` whose whole
pattern of value comparisons is realized in an elementary extension of the target. -/
def PatternWitness : Prop := ∃ a : M RVSort.K, a ∉ F ∧ ReflectDataExt F d a

omit [∀ (s : RVSort), Nonempty (M s)] in
/-- The finite fragment gives it, by compactness. -/
theorem patternWitness_of_valuePatternAt {a : M RVSort.K} (haF : a ∉ F)
    (h : ValuePatternAt F d a) : PatternWitness F d :=
  ⟨a, haF, exists_reflectData_ext_of_finsat F d a h⟩

omit [∀ (s : RVSort), Nonempty (M s)] [∀ (s : RVSort), Nonempty (N s)] in
/-- **The immediate case, no polynomial meeting the filter.** Every polynomial then has its
leading term at `y` already achieved at a point of `F`, and directedness gives *one* such point
for a whole finite family. So the pattern of `y` over `F` is, on any finite family, the pattern
of an element of `F` — and `d` of that element realizes it. -/
theorem valuePatternAt_immediate_of_not_meets {y : M RVSort.K}
    (hne : (distBalls (modelValSubring M) F.subtype y).Nonempty)
    (hnomeet : ∀ Q : Polynomial F, Q ≠ 0 →
      ¬ (distFilter (modelValSubring M) F.subtype y hne).Meets (Q.map F.subtype)) :
    ValuePatternAt F d y := by
  classical
  intro t
  set B := distFilter (modelValSubring M) F.subtype y hne with hBdef
  have hcentered : B.CenteredIn (F : Set (M RVSort.K)) := by
    rintro s ⟨r, r', -, rfl⟩
    exact ⟨(r : M RVSort.K), r.2, _, rfl⟩
  have hylim : y ∈ B.limit :=
    B.mem_limit.mpr fun s hs => mem_of_mem_distBalls hs
  set T : Finset (Polynomial (M RVSort.K)) :=
    (t.image fun Q => Q.map F.subtype).erase 0 with hTdef
  obtain ⟨c, hcF, hc⟩ := BallFilter.exists_center_rv_eval_eq_finset hcentered T
    (fun P _ => IsAlgClosed.splits P) (fun P hP => (Finset.mem_erase.mp hP).1)
    (fun P hP => by
      obtain ⟨Q, hQt, hQ⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hP).2
      subst hQ
      exact hnomeet Q fun h0 =>
        (Finset.mem_erase.mp hP).1 (by rw [h0, Polynomial.map_zero]))
    hylim
  have hval : ∀ Q ∈ t, valMap (rvMap (evalOn F.subtype y Q))
      = valMap (rvMap (evalOn F.subtype c Q)) := by
    intro Q hQ
    by_cases hQ0 : Q = 0
    · rw [hQ0, map_zero, map_zero]
    · have hmapne : Q.map F.subtype ≠ 0 := Polynomial.map_ne_zero hQ0
      have h := hc _ (Finset.mem_erase.mpr ⟨hmapne, Finset.mem_image_of_mem _ hQ⟩)
      have he : ∀ x : M RVSort.K, evalOn F.subtype x Q = (Q.map F.subtype).eval x :=
        fun x => (Polynomial.eval_map _ _).symm
      rw [he, he]
      exact congrArg valMap (rvMap_eq_iff_rv_eq.mpr h)
  refine ⟨d.hom ⟨c, hcF⟩, fun P hP Q hQ => ?_⟩
  rw [hval P hP, hval Q hQ]
  exact exists_valuePattern_of_mem F d hcF P Q

/-! #### The immediate case, algebraic

Some polynomial over `F` meets the ball filter of `y`. At the minimal degree its root `a` in the
limit is the element to adjoin, and the far-side element must be a root of the image polynomial
*and* a generic of the far-side filter. No element of `N` need be both, so it is produced in
an elementary extension; the type is finitely satisfiable in `N` itself, which is
`exists_root_at_distances`. -/

omit [∀ (s : RVSort), Nonempty (M s)] in
/-- **A monic polynomial of least degree meeting the filter.** Normalizing by the leading
coefficient does not change the roots, and the degree is positive because a constant polynomial
has none. -/
theorem exists_monic_meets_min_degree {y : M RVSort.K}
    (hne : (distBalls (modelValSubring M) F.subtype y).Nonempty)
    (hmeet : ∃ Q : Polynomial F, Q ≠ 0 ∧
      (distFilter (modelValSubring M) F.subtype y hne).Meets (Q.map F.subtype)) :
    ∃ P : Polynomial F, P.Monic ∧ 0 < P.natDegree ∧
      (distFilter (modelValSubring M) F.subtype y hne).Meets (P.map F.subtype) ∧
      ∀ Q : Polynomial F, Q ≠ 0 → Q.natDegree < P.natDegree →
        ¬ (distFilter (modelValSubring M) F.subtype y hne).Meets (Q.map F.subtype) := by
  classical
  set B := distFilter (modelValSubring M) F.subtype y hne with hBdef
  have hex : ∃ n, ∃ Q : Polynomial F, Q ≠ 0 ∧ B.Meets (Q.map F.subtype) ∧ Q.natDegree = n := by
    obtain ⟨Q, hQ0, hQm⟩ := hmeet
    exact ⟨Q.natDegree, Q, hQ0, hQm, rfl⟩
  obtain ⟨P₀, hP₀0, hP₀m, hP₀d⟩ := Nat.find_spec hex
  have hmin0 : ∀ Q : Polynomial F, Q ≠ 0 → B.Meets (Q.map F.subtype) →
      Nat.find hex ≤ Q.natDegree := fun Q hQ0 hQm => Nat.find_le ⟨Q, hQ0, hQm, rfl⟩
  have hP₀pos : 0 < P₀.natDegree := by
    rcases Nat.eq_zero_or_pos P₀.natDegree with h0 | h; swap
    · exact h
    obtain ⟨e, -, hroot⟩ := hP₀m
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.map_C, Polynomial.IsRoot,
      Polynomial.eval_C] at hroot
    exact absurd (Polynomial.eq_C_of_natDegree_eq_zero h0) (by
      rw [(map_eq_zero_iff F.subtype F.subtype.injective).mp hroot, map_zero]
      exact hP₀0)
  refine ⟨P₀ * Polynomial.C P₀.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hP₀0, ?_,
    ?_, ?_⟩
  · rw [Polynomial.natDegree_mul_leadingCoeff_inv _ hP₀0]; exact hP₀pos
  · obtain ⟨e, heL, hroot⟩ := hP₀m
    refine ⟨e, heL, ?_⟩
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.IsRoot, Polynomial.eval_mul]
    rw [Polynomial.IsRoot] at hroot
    rw [hroot, zero_mul]
  · intro Q hQ0 hQd hQm
    have hle := hmin0 Q hQ0 hQm
    rw [Polynomial.natDegree_mul_leadingCoeff_inv _ hP₀0, hP₀d] at hQd
    omega

omit [∀ (s : RVSort), Nonempty (M s)] in
/-- **A generic of the filter has the same distances to `F` as `y` does.** Both lie in every ball,
and by immediacy the balls have radius every distance from `y` to `F`, so `a - φ r` and `y - φ r`
differ by strictly less than either. -/
theorem rv_sub_eq_of_mem_limit {y a : M RVSort.K} (hyF : y ∉ F)
    (himm : ImmediateAt (modelValSubring M) F.subtype y)
    (hne : (distBalls (modelValSubring M) F.subtype y).Nonempty)
    (haL : a ∈ (distFilter (modelValSubring M) F.subtype y hne).limit) (r : F) :
    rv (A := modelValSubring M) (a - F.subtype r)
      = rv (A := modelValSubring M) (y - F.subtype r) := by
  have haK : ∀ r : F, y ≠ F.subtype r := fun r hc => hyF (by rw [hc]; exact r.2)
  obtain ⟨dd, hidx, -⟩ := exists_dist_lt_of_immediateAt haK himm r
  have hball : (modelValSubring M).ball (F.subtype (r + dd))
      ((modelValSubring M).valuation (y - F.subtype r))
        ∈ (distFilter (modelValSubring M) F.subtype y hne).carrier := ⟨r + dd, r, hidx, rfl⟩
  have hy' := mem_of_mem_distBalls hball
  have ha' := (distFilter (modelValSubring M) F.subtype y hne).mem_limit.mp haL _ hball
  rw [mem_ball] at hy' ha'
  have hay : (modelValSubring M).valuation (a - y)
      < (modelValSubring M).valuation (y - F.subtype r) :=
    calc (modelValSubring M).valuation (a - y)
        = (modelValSubring M).valuation
            ((a - F.subtype (r + dd)) - (y - F.subtype (r + dd))) := by congr 1; ring
      _ ≤ max ((modelValSubring M).valuation (a - F.subtype (r + dd)))
            ((modelValSubring M).valuation (y - F.subtype (r + dd))) := Valuation.map_sub _ _ _
      _ < (modelValSubring M).valuation (y - F.subtype r) := max_lt ha' hy'
  refine ((rv_eq_iff_valuation_sub_lt (sub_ne_zero_of_ne (haK r))).mpr ?_).symm
  rw [show a - F.subtype r - (y - F.subtype r) = a - y by ring]
  exact hay

omit [∀ (s : RVSort), Nonempty (M s)] in
/-- **Both hypotheses of the ball transfer, from the distances alone.** Under immediacy every
distance from `a` to `F` is the value of an element of `F`; if the far-side element has the images
of those distances, the two hypotheses become comparisons inside `F`, which the embedding
reflects. -/
theorem distReflect_of_distances {N' : RVSort → Type 0} [rvLang.Structure N'] [N' ⊨ ACVFTheory]
    (d' : FieldEmbeddingData F N') {a : M RVSort.K} {b : N' RVSort.K} {sf : F → F}
    (hva : ∀ r : F, (modelValSubring M).valuation (a - F.subtype r)
      = (modelValSubring M).valuation (F.subtype (sf r)))
    (hvb : ∀ r : F, (modelValSubring N').valuation (b - d'.hom r)
      = (modelValSubring N').valuation (d'.hom (sf r))) :
    DistReflect F.subtype d'.hom (modelValSubring M) (modelValSubring N') a b ∧
      DistCoeffReflect F.subtype d'.hom (modelValSubring M) (modelValSubring N') a b := by
  have hcoeff' : CoeffReflect F.subtype d'.hom (modelValSubring M) (modelValSubring N') :=
    coeffReflect_of_fieldEmbeddingData F d'
  constructor
  · intro r r'
    rw [hva, hva, hvb, hvb]
    exact hcoeff'.lt_iff (sf r) (sf r')
  · intro u r
    rw [hva, hvb]
    exact hcoeff'.lt_iff u (sf r)

omit [∀ (s : RVSort), Nonempty (M s)] [∀ (s : RVSort), Nonempty (N s)] in
/-- **Finite satisfiability of the type in the target itself.** For a finite set `E` of points of
`F`, some root of the image of `P` lies at the prescribed leading-term distance from each `ψ r`.

Only the closest point `c` of `E` to `a` has to be arranged, and `exists_root_rv_sub_eq` does
that. The others follow: at a closest point the decomposition `a - φ r = (a - φ c) + φ (c - r)`
does not cancel, non-cancellation is a comparison inside `F` and so transfers
(`CoeffReflect.max_congr`), and then `rv_add_congr'` moves the distance across. -/
theorem exists_root_at_distances {a : M RVSort.K} {P : Polynomial F} (hP0 : P ≠ 0)
    (hPa : (P.map F.subtype).eval a = 0) {sf : F → F}
    (hsf : ∀ r : F, rv (A := modelValSubring M) (a - F.subtype r)
      = rv (A := modelValSubring M) (F.subtype (sf r)))
    (hsf0 : ∀ r : F, sf r ≠ 0) (E : Finset F) :
    ∃ b : N RVSort.K, (P.map d.hom).eval b = 0 ∧ ∀ r ∈ E,
      rv (A := modelValSubring N) (b - d.hom r)
        = rv (A := modelValSubring N) (d.hom (sf r)) := by
  classical
  have hcoeff : CoeffReflect F.subtype d.hom (modelValSubring M) (modelValSubring N) :=
    coeffReflect_of_fieldEmbeddingData F d
  obtain ⟨c, hcE, hcmin⟩ := Finset.exists_min_image (insert (0 : F) E)
    (fun r => (modelValSubring M).valuation (a - F.subtype r))
    ⟨0, Finset.mem_insert_self _ _⟩
  obtain ⟨b, hbroot, hbrv⟩ := exists_root_rv_sub_eq (A := modelValSubring M)
    (AL := modelValSubring N) hcoeff hP0 hPa (hsf0 c) (hsf c)
  refine ⟨b, hbroot, fun r hr => ?_⟩
  have hmaxK : (modelValSubring M).valuation (a - F.subtype r)
      = max ((modelValSubring M).valuation (a - F.subtype c))
        ((modelValSubring M).valuation (F.subtype c - F.subtype r)) :=
    valuation_sub_eq_max_of_isClosest (hcmin r (Finset.mem_insert_of_mem hr))
  have hK : rv (A := modelValSubring M) (a - F.subtype r)
      = rv (A := modelValSubring M) (F.subtype (sf c + c - r)) := by
    rw [show a - F.subtype r = (a - F.subtype c) + (F.subtype c - F.subtype r) by ring,
      rv_add_congr (hsf c) (by
        rw [show (a - F.subtype c) + (F.subtype c - F.subtype r) = a - F.subtype r by ring]
        exact hmaxK)]
    congr 1
    rw [map_sub, map_add]
    ring
  have hvsc : (modelValSubring M).valuation (a - F.subtype c)
      = (modelValSubring M).valuation (F.subtype (sf c)) := by
    rw [← rvVal_rv (A := modelValSubring M), hsf c, rvVal_rv]
  have hmaxK' : (modelValSubring M).valuation (F.subtype (sf c + c - r))
      = max ((modelValSubring M).valuation (F.subtype (sf c)))
        ((modelValSubring M).valuation (F.subtype (c - r))) := by
    rw [← rvVal_rv (A := modelValSubring M), ← hK, rvVal_rv, hmaxK, hvsc,
      ← map_sub F.subtype c r]
  have hL : rv (A := modelValSubring N) (b - d.hom r)
      = rv (A := modelValSubring N) (d.hom (sf c + c - r)) := by
    rw [show b - d.hom r = (b - d.hom c) + (d.hom c - d.hom r) by ring,
      rv_add_congr' hbrv (by
        rw [show d.hom (sf c) + (d.hom c - d.hom r) = d.hom (sf c + c - r) by
          rw [map_sub, map_add]; ring, show d.hom c - d.hom r = d.hom (c - r) from
          (map_sub _ _ _).symm]
        exact hcoeff.max_congr hmaxK')]
    congr 1
    rw [map_sub, map_add]
    ring
  have hsameK : rv (A := modelValSubring M) (F.subtype (sf r))
      = rv (A := modelValSubring M) (F.subtype (sf c + c - r)) := by
    rw [← hsf r]; exact hK
  have hsame : rv (A := modelValSubring N) (d.hom (sf r))
      = rv (A := modelValSubring N) (d.hom (sf c + c - r)) := by
    rw [← rvMap_eq_iff_rv_eq, ← d.rv_iff, rvMap_eq_iff_rv_eq]
    exact hsameK
  rw [hL, hsame]

omit [∀ (s : RVSort), Nonempty (M s)] in
/-- **The immediate case, algebraic.** -/
theorem patternWitness_immediate_of_meets {y : M RVSort.K} (hyF : y ∉ F)
    (himm : ImmediateAt (modelValSubring M) F.subtype y)
    (hne : (distBalls (modelValSubring M) F.subtype y).Nonempty)
    (hmeet : ∃ Q : Polynomial F, Q ≠ 0 ∧
      (distFilter (modelValSubring M) F.subtype y hne).Meets (Q.map F.subtype)) :
    PatternWitness F d := by
  classical
  have haK : ∀ r : F, y ≠ F.subtype r := fun r hc => hyF (by rw [hc]; exact r.2)
  obtain ⟨P, hPmonic, hPpos, hPmeets, hminP0⟩ := exists_monic_meets_min_degree F hne hmeet
  obtain ⟨a, haL, hPa⟩ := hPmeets
  have haF : a ∉ F := fun hc => notMem_limit_distFilter (hne := hne) haK himm ⟨a, hc⟩ haL
  have haK' : ∀ r : F, a ≠ F.subtype r := fun r hc => haF (by rw [hc]; exact r.2)
  -- the distances from `a` are the distances from `y`, so the two filters are the same
  have hrvay := rv_sub_eq_of_mem_limit F hyF himm hne haL
  have hvay : ∀ r : F, (modelValSubring M).valuation (a - F.subtype r)
      = (modelValSubring M).valuation (y - F.subtype r) := fun r => by
    rw [← rvVal_rv (A := modelValSubring M), hrvay r, rvVal_rv]
  have hballs : distBalls (modelValSubring M) F.subtype a
      = distBalls (modelValSubring M) F.subtype y := by
    ext s
    simp only [mem_distBalls_iff, DistIdx, hvay]
  have hneA : (distBalls (modelValSubring M) F.subtype a).Nonempty := by rw [hballs]; exact hne
  have hlim : (distFilter (modelValSubring M) F.subtype a hneA).limit
      = (distFilter (modelValSubring M) F.subtype y hne).limit := by
    change ⋂ s ∈ distBalls (modelValSubring M) F.subtype a, s
      = ⋂ s ∈ distBalls (modelValSubring M) F.subtype y, s
    rw [hballs]
  have hmeetsA : ∀ Q : Polynomial (M RVSort.K),
      (distFilter (modelValSubring M) F.subtype a hneA).Meets Q
        ↔ (distFilter (modelValSubring M) F.subtype y hne).Meets Q := by
    intro Q
    change (∃ e ∈ (distFilter (modelValSubring M) F.subtype a hneA).limit, Q.IsRoot e)
      ↔ ∃ e ∈ (distFilter (modelValSubring M) F.subtype y hne).limit, Q.IsRoot e
    rw [hlim]
  -- the distance function, and immediacy at `a`
  have hsex : ∀ r : F, ∃ u : F, rv (A := modelValSubring M) (a - F.subtype r)
      = rv (A := modelValSubring M) (F.subtype u) := fun r => by
    obtain ⟨u, hu⟩ := himm r
    exact ⟨u, by rw [hrvay r]; exact hu⟩
  choose sf hsf using hsex
  have hsf0 : ∀ r : F, sf r ≠ 0 := by
    intro r h0
    have h1 : rv (A := modelValSubring M) (a - F.subtype r) = 0 := by
      rw [hsf r, h0, map_zero, rv_zero]
    rw [rv_eq_zero_iff, sub_eq_zero] at h1
    exact haF (by rw [h1]; exact r.2)
  have himma : ImmediateAt (modelValSubring M) F.subtype a := fun r => ⟨sf r, hsf r⟩
  have hva : ∀ r : F, (modelValSubring M).valuation (a - F.subtype r)
      = (modelValSubring M).valuation (F.subtype (sf r)) := fun r => by
    rw [← rvVal_rv (A := modelValSubring M), hsf r, rvVal_rv]
  -- the restricted type: a root of `P`, at the prescribed distances
  set Dp : F → Polynomial F × Polynomial F :=
    fun r => (Polynomial.C (sf r + r) - Polynomial.X, Polynomial.X - Polynomial.C r) with hDp
  set S : Set (Polynomial F × Polynomial F) := insert ((0 : Polynomial F), P) (Set.range Dp)
    with hSdef
  have hFsub0 : ∀ r : F, F.subtype (sf r) ≠ 0 := fun r h =>
    hsf0 r ((map_eq_zero_iff F.subtype F.subtype.injective).mp h)
  have hnearD : ∀ r : F, ¬ (valMap (rvMap (evalOn F.subtype a (Dp r).1))
      ≤ valMap (rvMap (evalOn F.subtype a (Dp r).2))) := fun r =>
    (valLe_linear_iff (T := M) F.subtype a r (hFsub0 r)).mpr (hsf r)
  have hnearP : valMap (rvMap (evalOn F.subtype a (0 : Polynomial F)))
      ≤ valMap (rvMap (evalOn F.subtype a P)) :=
    (valLe_zero_iff (T := M) F.subtype a P).mpr hPa
  -- finite satisfiability, from `exists_root_at_distances`
  have hfin : ∀ t : Finset (Polynomial F × Polynomial F), (↑t : Set _) ⊆ S →
      ∃ b : N RVSort.K, ∀ p ∈ t,
        (valMap (rvMap (evalOn F.subtype a p.1)) ≤ valMap (rvMap (evalOn F.subtype a p.2))
          ↔ valMap (rvMap (evalOn' d.hom b p.1)) ≤ valMap (rvMap (evalOn' d.hom b p.2))) := by
    intro t hts
    obtain ⟨b, hbroot, hball⟩ := exists_root_at_distances F d hPmonic.ne_zero hPa hsf hsf0
      (t.image fun p => -(p.2.coeff 0))
    refine ⟨b, fun p hp => ?_⟩
    rcases hts (Finset.mem_coe.mpr hp) with rfl | ⟨r, hr⟩
    · exact iff_of_true hnearP ((valLe_zero_iff (T := N) d.hom b P).mpr hbroot)
    · have hrE : r ∈ t.image fun p => -(p.2.coeff 0) := by
        refine Finset.mem_image.mpr ⟨p, hp, ?_⟩
        rw [← hr, hDp]
        simp
      subst hr
      refine iff_of_false (hnearD r) ?_
      refine (valLe_linear_iff (T := N) d.hom b r ?_).mpr (hball r hrE)
      exact fun h => hsf0 r (d.hom_injective (by rw [h, map_zero]))
  -- compactness, and the transfer
  obtain ⟨Nstar, _, _, j, hbex⟩ := exists_realize_ext_of_finsat_on F d a S hfin
  have : Nstar ⊨ ACVFTheory := j.theory_model
  obtain ⟨b, hb⟩ := hbex
  set ψ' := (d.comp j.toEmbedding).hom with hψ'def
  have hψ'0 : ∀ r : F, r ≠ 0 → ψ' r ≠ 0 := fun r hr h =>
    hr ((d.comp j.toEmbedding).hom_injective (by rw [h, map_zero]))
  have hrootb : (P.map ψ').eval b = 0 :=
    (valLe_zero_iff (T := Nstar) ψ' b P).mp ((hb _ (Set.mem_insert _ _)).mp hnearP)
  have hballb : ∀ r : F, rv (A := modelValSubring Nstar) (b - ψ' r)
      = rv (A := modelValSubring Nstar) (ψ' (sf r)) := fun r =>
    (valLe_linear_iff (T := Nstar) ψ' b r (hψ'0 _ (hsf0 r))).mp
      fun hc => hnearD r ((hb (Dp r) (Set.mem_insert_of_mem _ ⟨r, rfl⟩)).mpr hc)
  have hvb : ∀ r : F, (modelValSubring Nstar).valuation (b - ψ' r)
      = (modelValSubring Nstar).valuation (ψ' (sf r)) := fun r => by
    rw [← rvVal_rv (A := modelValSubring Nstar), hballb r, rvVal_rv]
  obtain ⟨hdist, hmix⟩ :=
    distReflect_of_distances F (d.comp j.toEmbedding) (sf := sf) hva hvb
  have hbL : ∀ r : F, b ≠ ψ' r := by
    intro r hcon
    have h0 : rv (A := modelValSubring Nstar) (ψ' (sf r)) = 0 := by
      rw [← hballb r, hcon, sub_self, rv_zero]
    exact hψ'0 _ (hsf0 r) (rv_eq_zero_iff.mp h0)
  exact ⟨a, haF, Nstar, inferInstance, inferInstance, j, b,
    reflectData_of_immediate_root hdist hmix
    (coeffReflect_of_fieldEmbeddingData F (d.comp j.toEmbedding)) haK' hbL himma
    (hneK := hneA) (hneL := distBalls_nonempty_transfer hdist hneA)
    hPmonic hPpos hPa hrootb
    (fun Q hQ0 hQd => fun hQm => hminP0 Q hQ0 hQd ((hmeetsA _).mp hQm))⟩

omit [∀ (s : RVSort), Nonempty (M s)] in
/-- **The immediate case.** -/
theorem patternWitness_immediate {y : M RVSort.K} (hyF : y ∉ F)
    (himm : ImmediateAt (modelValSubring M) F.subtype y) : PatternWitness F d := by
  classical
  have haK : ∀ r : F, y ≠ F.subtype r := fun r hc => hyF (by rw [hc]; exact r.2)
  have hne : (distBalls (modelValSubring M) F.subtype y).Nonempty :=
    distBalls_nonempty haK himm
  by_cases hmeet : ∃ Q : Polynomial F, Q ≠ 0 ∧
      (distFilter (modelValSubring M) F.subtype y hne).Meets (Q.map F.subtype)
  · exact patternWitness_immediate_of_meets F d hyF himm hne hmeet
  · push Not at hmeet
    exact patternWitness_of_valuePatternAt F d hyF
      (valuePatternAt_immediate_of_not_meets F d hne fun Q hQ0 => hmeet Q hQ0)

omit [∀ (s : RVSort), Nonempty (M s)] in
/-- **The routing, in full.** Either the extension is immediate at `y`, or some `y - r` has a new
leading term. -/
theorem exists_patternWitness {y : M RVSort.K} (hyF : y ∉ F) : PatternWitness F d := by
  classical
  by_cases himm : ImmediateAt (modelValSubring M) F.subtype y
  · exact patternWitness_immediate F d hyF himm
  obtain ⟨r, hr⟩ := exists_rv_ne_of_not_immediateAt himm
  have hz0 : y - (r : M RVSort.K) ≠ 0 := by
    intro h
    exact hyF (by rw [sub_eq_zero] at h; rw [h]; exact r.2)
  have hzF : ∀ x ∈ F, rvMap x ≠ rvMap (y - (r : M RVSort.K)) := by
    intro x hx hxz
    exact hr ⟨x, hx⟩ (rvMap_eq_iff_rv_eq.mp hxz).symm
  obtain ⟨a, haF, h⟩ := exists_valuePatternAt_of_rv_notMem F d hz0 hzF
  exact patternWitness_of_valuePatternAt F d haF h

end Routing

/-- **`ValuePatternExt` holds**, by Rideau-Kikuchi's routing. Through
`fieldStep_of_valuePatternExt`, this is `FieldStep`. -/
theorem valuePatternExt_holds : ValuePatternExt := by
  intro M N _ _ _ _ _ _ F d y hyF
  exact exists_patternWitness F d hyF

end ManySorted.Language
