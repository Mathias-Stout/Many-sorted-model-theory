/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.AlgebraicBackground.RV

/-!
# Balls, ball filters, and leading terms

This follows the pseudo-Cauchy filters of Rideau-Kikuchi's *Model theory of valued fields*
(Definition 1.2.11). By Definition 2.2.1 and Proposition 2.2.2, a `1`-type over a subfield is
determined by **which balls contain the element**, so the data to carry around is a
downward-directed family of balls.

The computational heart is `rv_sub_eq_of_notMem_ball`: the leading term of the distance to a
point *outside* a ball is constant *on* the ball. A ball is too small to distinguish points
outside it, so a polynomial all of whose roots avoid the ball has constant leading term on it
(`rv_eval_eq_of_roots_notMem_ball`). That is the first bullet of the notes' Lemma 2.1.7: the
leading term is constant on some ball of the filter.

Valuations are multiplicative, as in Mathlib, so a *smaller* valuation means *closer* and
`ball c γ` is the set of points at distance strictly less than `γ` from `c`.

## Main definitions

* `ValuationSubring.ball` : the open ball.
* `ValuationSubring.BallFilter` : a nonempty downward-directed family of balls.
* `ValuationSubring.BallFilter.limit` : the points lying in every ball of the family — the
  generics of Definition 2.2.1.

## Main statements

* `ValuationSubring.valuation_sub_eq_max_of_isClosest` : no cancellation at a closest point.
* `ValuationSubring.rv_sub_eq_of_notMem_ball` : distances to an outside point have constant
  leading term on a ball.
* `ValuationSubring.rv_eval_eq_of_roots_notMem_ball` : so does `P` itself, if its roots avoid
  the ball.
* `ValuationSubring.BallFilter.exists_forall_notMem` : finitely many points off the limit set
  are excluded by a single ball of the filter.
* `ValuationSubring.BallFilter.exists_rv_eval_eq` : if every root of `P` is off the limit set,
  the leading term of `P` is constant on some ball of the filter.
* `ValuationSubring.BallFilter.exists_center_rv_eval_eq_finset` : Proposition 2.1.8(1) — for
  finitely many polynomials not meeting a filter centered in `S`, their leading terms at a generic
  are attained at a single point of `S`.
* `ValuationSubring.BallFilter.valuation_eval_lt_of_meets` : Lemma 2.1.7, second bullet — if a
  root is a generic, the valuation of `P` strictly decreases as the balls shrink.
-/

@[expose] public section

namespace ValuationSubring

open Polynomial

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- The open ball of radius `γ` around `c`. -/
def ball (c : K) (γ : A.ValueGroup) : Set K := {x | A.valuation (x - c) < γ}

variable {A}

@[simp]
theorem mem_ball {c x : K} {γ : A.ValueGroup} : x ∈ A.ball c γ ↔ A.valuation (x - c) < γ :=
  Iff.rfl

/-- Two points of a ball are closer to each other than its radius. -/
theorem valuation_sub_lt_of_mem_ball {c x y : K} {γ : A.ValueGroup}
    (hx : x ∈ A.ball c γ) (hy : y ∈ A.ball c γ) : A.valuation (x - y) < γ := by
  rw [show x - y = (x - c) + -(y - c) by ring]
  refine lt_of_le_of_lt (map_add_le_max A.valuation _ _) ?_
  rw [Valuation.map_neg]
  exact max_lt hx hy

/-- Two balls containing a common point are nested, the smaller radius inside the larger. -/
theorem ball_subset_ball_of_mem {e₁ e₂ a : K} {γ₁ γ₂ : A.ValueGroup}
    (h₁ : a ∈ A.ball e₁ γ₁) (h₂ : a ∈ A.ball e₂ γ₂) (hγ : γ₁ ≤ γ₂) :
    A.ball e₁ γ₁ ⊆ A.ball e₂ γ₂ := by
  intro x hx
  rw [mem_ball] at hx h₁ h₂ ⊢
  rw [show x - e₂ = (x - e₁) + ((e₁ - a) + (a - e₂)) by ring]
  refine lt_of_le_of_lt (map_add_le_max A.valuation _ _) (max_lt (lt_of_lt_of_le hx hγ) ?_)
  refine lt_of_le_of_lt (map_add_le_max A.valuation _ _) (max_lt ?_ h₂)
  rw [show e₁ - a = -(a - e₁) by ring, Valuation.map_neg]
  exact lt_of_lt_of_le h₁ hγ

/-- **No cancellation at a closest point.** If `x` is at least as close to `a` as `y` is, then
`a - y = (a - x) + (x - y)` has the expected valuation: cancellation would make `y` strictly
closer to `a` than `x`. This is the "`rv` is isosceles" lemma of Rideau-Kikuchi's notes. -/
theorem valuation_sub_eq_max_of_isClosest {a x y : K}
    (h : A.valuation (a - x) ≤ A.valuation (a - y)) :
    A.valuation (a - y) = max (A.valuation (a - x)) (A.valuation (x - y)) := by
  have hsum : a - y = (a - x) + (x - y) := by ring
  rcases eq_or_ne (A.valuation (a - x)) (A.valuation (x - y)) with heq | hne
  · -- Equal valuations: the sum can only be smaller, but `x` is closest, so it is not.
    have hle : A.valuation (a - y) ≤ max (A.valuation (a - x)) (A.valuation (x - y)) := by
      rw [hsum]
      exact A.valuation.map_add_le_max' _ _
    rw [← heq, max_self] at hle ⊢
    exact le_antisymm hle h
  · rw [hsum, A.valuation.map_add_of_distinct_val hne]

/-- The distance from a point of a ball to a point outside it is the distance from the center
to that outside point: the ball is too small to matter. -/
theorem valuation_sub_eq_of_notMem_ball {c e x : K} {γ : A.ValueGroup}
    (he : e ∉ A.ball c γ) (hx : x ∈ A.ball c γ) :
    A.valuation (x - e) = A.valuation (e - c) := by
  have hce : γ ≤ A.valuation (e - c) := not_lt.mp he
  have hne : A.valuation (x - c) ≠ A.valuation (-(e - c)) := by
    rw [Valuation.map_neg]
    exact ne_of_lt (lt_of_lt_of_le hx hce)
  rw [show x - e = (x - c) + -(e - c) by ring, A.valuation.map_add_of_distinct_val hne,
    Valuation.map_neg]
  exact max_eq_right (le_of_lt (lt_of_lt_of_le hx hce))

/-- **Leading terms of distances to an outside point are constant on a ball.** This is what
makes a ball filter enough data: inside the ball, nothing about `e` is still being resolved. -/
theorem rv_sub_eq_of_notMem_ball {c e x y : K} {γ : A.ValueGroup}
    (he : e ∉ A.ball c γ) (hx : x ∈ A.ball c γ) (hy : y ∈ A.ball c γ) :
    rv (A := A) (x - e) = rv (A := A) (y - e) := by
  have hce : γ ≤ A.valuation (e - c) := not_lt.mp he
  have hxe : A.valuation (x - e) = A.valuation (e - c) := valuation_sub_eq_of_notMem_ball he hx
  have hx0 : x - e ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hxe
    rw [← hxe] at hce
    exact absurd (lt_of_lt_of_le hx hce) (by simp)
  rw [rv_eq_iff_valuation_sub_lt hx0, show y - e - (x - e) = y - x by ring, hxe]
  exact lt_of_lt_of_le (valuation_sub_lt_of_mem_ball hy hx) hce

/-- **A polynomial whose roots avoid a ball has constant leading term on it.** This is the
first bullet of Rideau-Kikuchi's Lemma 2.1.7. -/
theorem rv_eval_eq_of_roots_notMem_ball {P : K[X]} (hP : P.Splits) {c : K} {γ : A.ValueGroup}
    (hroots : ∀ r ∈ P.roots, r ∉ A.ball c γ) {x y : K}
    (hx : x ∈ A.ball c γ) (hy : y ∈ A.ball c γ) :
    rv (A := A) (P.eval x) = rv (A := A) (P.eval y) := by
  rw [rv_eval_eq_leadingCoeff_mul_prod hP, rv_eval_eq_leadingCoeff_mul_prod hP]
  congr 1
  exact congrArg Multiset.prod
    (Multiset.map_congr rfl fun r hr => rv_sub_eq_of_notMem_ball (hroots r hr) hx hy)

variable (A) in
/-- A **ball filter**: a nonempty family of balls, directed downward by inclusion. This is the
generating family of a pseudo-Cauchy filter in the sense of Rideau-Kikuchi's Definition 1.2.11,
a filter generated by balls. -/
structure BallFilter where
  /-- The balls of the filter, as subsets of the field. -/
  carrier : Set (Set K)
  /-- Each member really is a ball. -/
  isBall : ∀ s ∈ carrier, ∃ (c : K) (γ : A.ValueGroup), s = A.ball c γ
  /-- The family is nonempty. -/
  nonempty' : carrier.Nonempty
  /-- The family is directed downward. -/
  directed' : ∀ s ∈ carrier, ∀ t ∈ carrier, ∃ u ∈ carrier, u ⊆ s ∩ t

namespace BallFilter

variable (B : BallFilter A)

/-- The generics of the filter: the points lying in every one of its balls. -/
def limit : Set K := ⋂ s ∈ B.carrier, s

theorem mem_limit {a : K} : a ∈ B.limit ↔ ∀ s ∈ B.carrier, a ∈ s := by
  simp [limit, Set.mem_iInter]

/-- A point off the limit set is excluded by one of the balls. -/
theorem exists_notMem {e : K} (he : e ∉ B.limit) : ∃ s ∈ B.carrier, e ∉ s := by
  by_contra h
  push Not at h
  exact he (B.mem_limit.mpr h)

/-- Finitely many points off the limit set are excluded by a *single* ball: this is where
directedness is used. -/
theorem exists_forall_notMem (E : Finset K) (hE : ∀ e ∈ E, e ∉ B.limit) :
    ∃ s ∈ B.carrier, ∀ e ∈ E, e ∉ s := by
  classical
  induction E using Finset.induction with
  | empty => obtain ⟨s, hs⟩ := B.nonempty'; exact ⟨s, hs, by simp⟩
  | insert e E _ ih =>
    obtain ⟨s, hs, hsE⟩ := ih fun x hx => hE x (Finset.mem_insert_of_mem hx)
    obtain ⟨t, ht, hte⟩ := B.exists_notMem (hE e (Finset.mem_insert_self e E))
    obtain ⟨u, hu, hust⟩ := B.directed' s hs t ht
    refine ⟨u, hu, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact fun hxu => hte (hust hxu).2
    · exact fun hxu => hsE x hx (hust hxu).1

/-- **The leading term of `P` is eventually constant.** If no root of `P` is a generic of the
filter, then `P` has constant leading term on one of its balls. Together with
`rv_eval_eq_of_roots_notMem_ball` this is the first bullet of Rideau-Kikuchi's Lemma 2.1.7. -/
theorem exists_rv_eval_eq {P : K[X]} (hP : P.Splits)
    (hroots : ∀ r ∈ P.roots, r ∉ B.limit) :
    ∃ s ∈ B.carrier, ∀ x ∈ s, ∀ y ∈ s,
      rv (A := A) (P.eval x) = rv (A := A) (P.eval y) := by
  classical
  obtain ⟨s, hs, hsroots⟩ := B.exists_forall_notMem P.roots.toFinset
    (fun e he => hroots e (Multiset.mem_toFinset.mp he))
  obtain ⟨c, γ, rfl⟩ := B.isBall s hs
  exact ⟨A.ball c γ, hs, fun x hx y hy =>
    rv_eval_eq_of_roots_notMem_ball hP
      (fun r hr => hsroots r (Multiset.mem_toFinset.mpr hr)) hx hy⟩

/-- `P` **meets** the filter if one of its roots is a generic. In the notes' language, `P` has a
root in the pseudo-Cauchy filter (Lemma 2.1.7). -/
def Meets (P : K[X]) : Prop := ∃ e ∈ B.limit, P.IsRoot e

variable {B}

/-- If `P` does not meet the filter, its leading term is constant on one of the balls. This is
`exists_rv_eval_eq` phrased through `Meets`. -/
theorem exists_rv_eval_eq_of_not_meets {P : K[X]} (hP : P.Splits) (hP0 : P ≠ 0)
    (h : ¬ B.Meets P) :
    ∃ s ∈ B.carrier, ∀ x ∈ s, ∀ y ∈ s,
      rv (A := A) (P.eval x) = rv (A := A) (P.eval y) := by
  refine B.exists_rv_eval_eq hP fun r hr hrL => h ⟨r, hrL, ?_⟩
  exact (Polynomial.mem_roots hP0).mp hr

variable (B)

/-- A filter is **centered in `S`** if each of its balls can be given a center lying in `S` —
in the intended application, `S` is the subfield the embedding is already defined on. -/
def CenteredIn (S : Set K) : Prop :=
  ∀ s ∈ B.carrier, ∃ c ∈ S, ∃ γ : A.ValueGroup, s = A.ball c γ

variable {B}

/-- **One ball for finitely many polynomials at once.** If no polynomial of `T` meets the filter,
they all have constant leading term on a single ball of it: `exists_rv_eval_eq_of_not_meets` for
each, combined by directedness. -/
theorem exists_rv_eval_eq_finset (T : Finset K[X]) (hT : ∀ P ∈ T, P.Splits)
    (hT0 : ∀ P ∈ T, P ≠ 0) (hmeets : ∀ P ∈ T, ¬ B.Meets P) :
    ∃ s ∈ B.carrier, ∀ P ∈ T, ∀ x ∈ s, ∀ y ∈ s,
      rv (A := A) (P.eval x) = rv (A := A) (P.eval y) := by
  classical
  induction T using Finset.induction with
  | empty => obtain ⟨s, hs⟩ := B.nonempty'; exact ⟨s, hs, by simp⟩
  | insert P T _ ih =>
    obtain ⟨s, hs, hsT⟩ := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
      (fun Q hQ => hT0 Q (Finset.mem_insert_of_mem hQ))
      (fun Q hQ => hmeets Q (Finset.mem_insert_of_mem hQ))
    obtain ⟨u, hu, huconst⟩ :=
      exists_rv_eval_eq_of_not_meets (hT P (Finset.mem_insert_self _ _))
        (hT0 P (Finset.mem_insert_self _ _)) (hmeets P (Finset.mem_insert_self _ _))
    obtain ⟨w, hw, hwsub⟩ := B.directed' s hs u hu
    refine ⟨w, hw, fun Q hQ x hx y hy => ?_⟩
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · exact huconst x (hwsub hx).2 y (hwsub hy).2
    · exact hsT Q hQ x (hwsub hx).1 y (hwsub hy).1

/-- **One center for finitely many polynomials at once**, Rideau-Kikuchi's
Proposition 2.1.8(1). Directedness turns the per-polynomial constancy balls into a single one, and
its center lies in `S`. This is what the *finite* fragment of the value-comparison type needs: a
single point of the coefficient field at which all the values at a generic are already achieved. -/
theorem exists_center_rv_eval_eq_finset {S : Set K} (hcentered : B.CenteredIn S)
    (T : Finset K[X]) (hT : ∀ P ∈ T, P.Splits) (hT0 : ∀ P ∈ T, P ≠ 0)
    (hmeets : ∀ P ∈ T, ¬ B.Meets P) {a : K} (ha : a ∈ B.limit) :
    ∃ c ∈ S, ∀ P ∈ T, rv (A := A) (P.eval a) = rv (A := A) (P.eval c) := by
  obtain ⟨s, hs, hconst⟩ := exists_rv_eval_eq_finset T hT hT0 hmeets
  obtain ⟨c, hcS, γ, rfl⟩ := hcentered s hs
  have has : a ∈ A.ball c γ := B.mem_limit.mp ha _ hs
  have hγ : 0 < γ := lt_of_le_of_lt zero_le has
  have hcs : c ∈ A.ball c γ := by simpa [mem_ball] using hγ
  exact ⟨c, hcS, fun P hP => hconst P hP a has c hcs⟩

end BallFilter

/-! ### Lemma 2.1.7, second bullet

The second bullet says that when one of the roots of `P` *is* a generic, `P` does not settle
down: its valuation strictly decreases as the balls shrink. In the notes' notation,
`0 ∈ P⋆B`.

It is needed for the transfer: to know that a polynomial does not meet the filter *on the far side
of an embedding*, one argues that if it did, its valuations would strictly decrease there, hence —
the centers being images of centers, and valuations of coefficient-field elements transferring —
they would strictly decrease on the near side too, so it would meet the near filter, contradicting
minimality.
-/

/-- A strict comparison of multiset products: all factors at least as large, one strictly
larger, and the larger side without zero factors. -/
private theorem prod_lt_prod_of_lt {ι : Type*} {m : Multiset ι} {f g : ι → A.ValueGroup}
    (hle : ∀ i ∈ m, f i ≤ g i) (hne : ∀ i ∈ m, g i ≠ 0)
    {i₀ : ι} (hi₀ : i₀ ∈ m) (hlt : f i₀ < g i₀) :
    (m.map f).prod < (m.map g).prod := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = i₀ ::ₘ m' := ⟨m.erase i₀, (Multiset.cons_erase hi₀).symm⟩
  rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
  have hsub : ∀ i ∈ m', i ∈ i₀ ::ₘ m' := fun i hi => Multiset.mem_cons_of_mem hi
  have hB : (m'.map g).prod ≠ 0 := by
    refine Multiset.prod_ne_zero ?_
    rw [Multiset.mem_map]
    rintro ⟨i, hi, hgi⟩
    exact hne i (hsub i hi) hgi
  calc f i₀ * (m'.map f).prod
      ≤ f i₀ * (m'.map g).prod := by
        gcongr
        exact Multiset.prod_map_le_prod_map f g fun i hi => hle i (hsub i hi)
    _ < g i₀ * (m'.map g).prod := mul_lt_mul_of_pos_right hlt (pos_iff_ne_zero.mpr hB)

/-- The valuation form of the split-polynomial identity. -/
theorem valuation_eval_eq_prod {P : K[X]} (hP : P.Splits) (x : K) :
    A.valuation (P.eval x)
      = A.valuation P.leadingCoeff * (P.roots.map fun r => A.valuation (x - r)).prod := by
  have h := congrArg (rvVal (A := A)) (rv_eval_eq_leadingCoeff_mul_prod (A := A) hP x)
  rw [rvVal_rv, map_mul, rvVal_rv, map_multiset_prod, Multiset.map_map] at h
  simpa [Function.comp_def] using h

namespace BallFilter

variable {B : BallFilter A}

/-- **Lemma 2.1.7, second bullet.** Let `s` be a ball of the filter avoiding every non-generic
root of `P`, and `t ⊆ s` a smaller ball of the filter. If some root of `P` is a generic, then
`P` is strictly smaller at a point of `t` than at a point of `s` outside `t`. -/
theorem valuation_eval_lt_of_meets {P : K[X]} (hP : P.Splits)
    {s t : Set K} (hs : s ∈ B.carrier) (ht : t ∈ B.carrier) (hts : t ⊆ s)
    (hout : ∀ r ∈ P.roots, r ∉ B.limit → r ∉ s)
    {x y : K} (hx : x ∈ t) (hy : y ∈ s) (hy' : y ∉ t)
    {e : K} (he : e ∈ P.roots) (heB : e ∈ B.limit) (hy0 : P.eval y ≠ 0) :
    A.valuation (P.eval x) < A.valuation (P.eval y) := by
  obtain ⟨cs, γs, rfl⟩ := B.isBall s hs
  obtain ⟨ct, γt, rfl⟩ := B.isBall t ht
  -- every root is at least as far from `y` as from `x`, strictly so for a generic root
  have key : ∀ r ∈ P.roots, A.valuation (x - r) ≤ A.valuation (y - r) := by
    intro r hr
    by_cases hrB : r ∈ B.limit
    · -- a generic root lies in the small ball, which `y` is outside of
      have hrt : r ∈ A.ball ct γt := B.mem_limit.mp hrB _ ht
      have h1 : A.valuation (x - r) < γt := valuation_sub_lt_of_mem_ball hx hrt
      have h2 : A.valuation (r - y) = A.valuation (y - ct) :=
        valuation_sub_eq_of_notMem_ball hy' hrt
      have h3 : γt ≤ A.valuation (y - ct) := not_lt.mp hy'
      rw [show y - r = -(r - y) by ring, Valuation.map_neg, h2]
      exact le_of_lt (lt_of_lt_of_le h1 h3)
    · -- a non-generic root is outside the big ball, so equidistant from `x` and `y`
      have hrs : r ∉ A.ball cs γs := hout r hr hrB
      rw [valuation_sub_eq_of_notMem_ball hrs (hts hx),
        valuation_sub_eq_of_notMem_ball hrs hy]
  have hstrict : A.valuation (x - e) < A.valuation (y - e) := by
    have hrt : e ∈ A.ball ct γt := B.mem_limit.mp heB _ ht
    have h1 : A.valuation (x - e) < γt := valuation_sub_lt_of_mem_ball hx hrt
    have h2 : A.valuation (e - y) = A.valuation (y - ct) :=
      valuation_sub_eq_of_notMem_ball hy' hrt
    have h3 : γt ≤ A.valuation (y - ct) := not_lt.mp hy'
    rw [show y - e = -(e - y) by ring, Valuation.map_neg, h2]
    exact lt_of_lt_of_le h1 h3
  -- no root coincides with `y`, since `P` does not vanish there
  have hyne : ∀ r ∈ P.roots, A.valuation (y - r) ≠ 0 := by
    intro r hr h0
    rw [Valuation.zero_iff, sub_eq_zero] at h0
    exact hy0 (h0 ▸ (Polynomial.isRoot_of_mem_roots hr))
  have hlc : A.valuation P.leadingCoeff ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff, Polynomial.leadingCoeff_eq_zero]
    exact fun h => hy0 (by rw [h, Polynomial.eval_zero])
  rw [valuation_eval_eq_prod hP, valuation_eval_eq_prod hP]
  exact mul_lt_mul_of_pos_left (prod_lt_prod_of_lt key hyne he hstrict) (pos_iff_ne_zero.mpr hlc)

end BallFilter

end ValuationSubring
