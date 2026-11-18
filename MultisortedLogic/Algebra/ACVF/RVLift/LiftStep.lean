/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Substructure.FieldLike
public import MultisortedLogic.Algebra.ACVF.Theory.Recovery
public import MultisortedLogic.Algebra.ACVF.ValuedField.Comap
public import MultisortedLogic.Algebra.ACVF.ValuedField.Extend

/-!
# Lifting a leading term to the field sort: the transfer data

This is the shared half of steps `res(K(C)) = k(C)` and `v(K(C)) = Γ(C)` of Rideau-Kikuchi's
Proposition 2.1.10 (the routing step of `RVLift`). Those claims lift an element of the `RV`-part of
a substructure to the field sort, and they differ only in *which* element of the field sort is
chosen and why it creates no new leading terms. Everything else — the map of leading-term structures
that the extension lemmas of `Algebra/ACVF/ValuedField/Extend.lean` are stated with, the order
transfer, and the assembly of the extended embedding — is the same in all four cases and is proved
here once.

## The map of leading-term structures

`ValuationSubring.RvTypeEq` names a *total* map `fRV : AK.RV →*₀ AL.RV`, while an embedding of a
substructure `S` supplies only a partial one, defined on the `RV`-part of `S`. The resolution is to
instantiate the extension lemmas not at the model but at a **subfield** `E` of the field sort all of
whose leading terms lie in that `RV`-part: then `Algebra/ACVF/ValuedField/Comap.lean` identifies
`((modelValSubring M).comap E.subtype).RV` with the leading terms of `E`, on which the partial map
*is* total. `liftRvHom` is that map, and `liftRvHom_injective`, `liftRvHom_valuation_lt_iff` and
`liftRvHom_compat` are the three hypotheses the extension lemmas ask of it.

## The assembly

Given the resulting `RvTypeEq`, `ValuationSubring.extend` produces a ring homomorphism on
`F[a]` — inside `E`, so it has to be transported back to the field sort by `rangeLift` — and
`adjoinSubstructure` together with `adjoinEmbedding` turns that into an `L_RV`-embedding of a
substructure whose `RV`- and `Γ`-parts are untouched. That is `liftEmbedding`.

## Main definitions

* `Language.ofRV` : the `RV` sort of a model, read back from its valuation subring.
* `Language.embRV` : the `RV`-part of an embedding of a substructure, as a total map.
* `Language.liftRvHom` : the map of leading-term structures of a subfield.
* `Language.liftAdjoin`, `Language.liftEmbedding` : the enlarged substructure and the extended
  embedding.

## Main statements

* `Language.liftRvHom_injective`, `Language.liftRvHom_compat`,
  `Language.liftRvHom_valuation_lt_iff` : the hypotheses of the extension lemmas.
* `Language.liftEmbedding_apply_K_of_mem` : the extended embedding extends the given one.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]

/-! ### The `RV` sort of a model, read in its valuation subring

`toRV` is a bijection (`toRV_bijective`), so it may be inverted. The inverse is a homomorphism
of monoids with zero, which is what lets the leading terms of a subfield be pushed into the `RV`
sort of the model. -/

/-- The inverse of `toRV`: a leading term of `modelValSubring M`, read in the `RV` sort of `M`. -/
noncomputable def ofRV (ζ : (modelValSubring M).RV) : M RVSort.RV :=
  Function.surjInv toRV_surjective ζ

@[simp]
theorem toRV_ofRV (ζ : (modelValSubring M).RV) : toRV (ofRV ζ) = ζ :=
  Function.surjInv_eq _ _

@[simp]
theorem ofRV_toRV (ξ : M RVSort.RV) : ofRV (toRV ξ) = ξ :=
  toRV_injective (toRV_ofRV (toRV ξ))

@[simp]
theorem ofRV_rv (x : M RVSort.K) : ofRV (rv (A := modelValSubring M) x) = rvMap x := by
  rw [← toRV_rvMap, ofRV_toRV]

theorem ofRV_injective : Function.Injective (ofRV (M := M)) := fun ζ η h => by
  rw [← toRV_ofRV ζ, ← toRV_ofRV η, h]

@[simp]
theorem ofRV_zero : ofRV (0 : (modelValSubring M).RV) = 0 := by
  rw [← toRV_zero (M := M), ofRV_toRV]

@[simp]
theorem ofRV_one : ofRV (1 : (modelValSubring M).RV) = 1 := by
  rw [← toRV_one (M := M), ofRV_toRV]

theorem ofRV_mul (ζ η : (modelValSubring M).RV) : ofRV (ζ * η) = ofRV ζ * ofRV η := by
  refine toRV_injective ?_
  rw [toRV_ofRV, toRV_mul, toRV_ofRV, toRV_ofRV]

theorem ofRV_add (ζ η : (modelValSubring M).RV) :
    ofRV (rvAdd (modelValSubring M) ζ η) = ofRV ζ + ofRV η := by
  refine toRV_injective ?_
  rw [toRV_ofRV, toRV_add, toRV_ofRV, toRV_ofRV]

theorem ofRV_neg (ζ : (modelValSubring M).RV) :
    ofRV (rvNeg (modelValSubring M) ζ) = -ofRV ζ := by
  refine toRV_injective ?_
  rw [toRV_ofRV, toRV_neg, toRV_ofRV]

@[simp]
theorem ofRV_inv (ζ : (modelValSubring M).RV) : ofRV ζ⁻¹ = (ofRV ζ)⁻¹ := by
  refine toRV_injective ?_
  rw [toRV_ofRV, toRV_inv, toRV_ofRV]

/-! ### The leading terms of a subfield of the field sort

The `RV` sort of a model is not a monoid with zero in Mathlib's sense — its addition is not
associative, so the theory carries no ring structure on it and the operations are only raw
symbols. So the composite below is a bare function with `map_mul`-style lemmas attached rather
than a bundled homomorphism; it is bundled once, in `liftRvHom`, where the target *is* a monoid
with zero. -/

/-- The leading terms of a subfield of the field sort, read in the `RV` sort of the model. -/
noncomputable def rvOfSubfield (E : Subfield (M RVSort.K))
    (ζ : ((modelValSubring M).comap E.subtype).RV) : M RVSort.RV :=
  ofRV (rvComap (modelValSubring M) (f := E.subtype) ζ)

@[simp]
theorem rvOfSubfield_rv (E : Subfield (M RVSort.K)) (x : E) :
    rvOfSubfield E (rv (A := (modelValSubring M).comap E.subtype) x)
      = rvMap (x : M RVSort.K) := by
  simp only [rvOfSubfield, rvComap_rv]
  exact ofRV_rv _

@[simp]
theorem rvOfSubfield_zero (E : Subfield (M RVSort.K)) : rvOfSubfield E 0 = 0 := by
  simp only [rvOfSubfield, map_zero, ofRV_zero]

@[simp]
theorem rvOfSubfield_one (E : Subfield (M RVSort.K)) : rvOfSubfield E 1 = 1 := by
  simp only [rvOfSubfield, map_one, ofRV_one]

theorem rvOfSubfield_mul (E : Subfield (M RVSort.K))
    (ζ η : ((modelValSubring M).comap E.subtype).RV) :
    rvOfSubfield E (ζ * η) = rvOfSubfield E ζ * rvOfSubfield E η := by
  simp only [rvOfSubfield, map_mul, ofRV_mul]

theorem rvOfSubfield_injective (E : Subfield (M RVSort.K)) :
    Function.Injective (rvOfSubfield E) :=
  ofRV_injective.comp (rvComap_injective _)

/-- Being in the residue field is the same computed in a subfield or in the model. -/
theorem isResidue_comap_iff (E : Subfield (M RVSort.K)) (u : E) :
    IsResidue ((modelValSubring M).comap E.subtype)
        (rv (A := (modelValSubring M).comap E.subtype) u)
      ↔ IsResidue (modelValSubring M) (rv (A := modelValSubring M) (u : M RVSort.K)) := by
  rw [isResidue_rv_iff, isResidue_rv_iff, valuation_comap_eq_one_iff]
  exact or_congr Iff.rfl ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩

/-- **The residue addition passes to a subfield.** The `RV`-sort addition computed in the
leading-term structure of a subfield of the field sort agrees with the one computed in the
model. Both are `0` outside the residue field, and inside it both are computed on
representatives. -/
theorem rvOfSubfield_rvAdd (E : Subfield (M RVSort.K))
    (ζ η : ((modelValSubring M).comap E.subtype).RV) :
    rvOfSubfield E (rvAdd ((modelValSubring M).comap E.subtype) ζ η)
      = rvOfSubfield E ζ + rvOfSubfield E η := by
  obtain ⟨u, rfl⟩ := rv_surjective (A := (modelValSubring M).comap E.subtype) ζ
  obtain ⟨v, rfl⟩ := rv_surjective (A := (modelValSubring M).comap E.subtype) η
  have hcoe : ((u + v : E) : M RVSort.K) = (u : M RVSort.K) + (v : M RVSort.K) := rfl
  have hsum : ((modelValSubring M).comap E.subtype).valuation (u + v) = 1
      ↔ (modelValSubring M).valuation ((u : M RVSort.K) + (v : M RVSort.K)) = 1 := by
    rw [valuation_comap_eq_one_iff]
    exact Iff.rfl
  rw [rvOfSubfield_rv, rvOfSubfield_rv]
  by_cases hg : IsResidue (modelValSubring M) (rv (A := modelValSubring M) (u : M RVSort.K)) ∧
      IsResidue (modelValSubring M) (rv (A := modelValSubring M) (v : M RVSort.K)) ∧
      (modelValSubring M).valuation ((u : M RVSort.K) + (v : M RVSort.K)) = 1
  · obtain ⟨h1, h2, h3⟩ := hg
    rw [rvAdd_rv_rv_of_isResidue _ ((isResidue_comap_iff E u).mpr h1)
      ((isResidue_comap_iff E v).mpr h2) (hsum.mpr h3), rvOfSubfield_rv, hcoe]
    exact (model_add_res (isResidue_rv_iff_valMap.mp h1) (isResidue_rv_iff_valMap.mp h2)
      (valMap_eq_zero_iff_valuation_eq_one.mpr h3)).symm
  · rw [rvAdd_eq_zero_of_not_isResidue _ (fun hc => hg ⟨(isResidue_comap_iff E u).mp hc.1,
      (isResidue_comap_iff E v).mp hc.2.1, hsum.mp hc.2.2⟩), rvOfSubfield_zero]
    by_cases h1 : IsResidue (modelValSubring M) (rv (A := modelValSubring M) (u : M RVSort.K))
    · by_cases h2 : IsResidue (modelValSubring M) (rv (A := modelValSubring M) (v : M RVSort.K))
      · have h3 : valMap (rvMap ((u : M RVSort.K) + (v : M RVSort.K))) ≠ 0 := fun hc =>
          hg ⟨h1, h2, valMap_eq_zero_iff_valuation_eq_one.mp hc⟩
        exact (model_add_zero_sum h3).symm
      · rw [isResidue_rv_iff_valMap, not_or] at h2
        exact (model_add_zero_right _ h2.1 h2.2).symm
    · rw [isResidue_rv_iff_valMap, not_or] at h1
      exact (model_add_zero_left _ h1.1 h1.2).symm

/-! ### The `RV`-part of an embedding, as a total map -/

section LiftOne

variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]
variable (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N)

/-- **The conclusion of one lift step.** The field part of the substructure grows to contain `a`,
the `RV`- and `Γ`-parts do not change at all, and the embedding extends. Each of the four cases of
the routing delivers exactly this, and keeping the other two sorts fixed is what makes them cheap:
the map on the new leading terms is forced, because there are no new leading terms. -/
def LiftStepAt (a : M RVSort.K) : Prop :=
  ∃ (S' : rvLang.Substructure M) (e' : (fun s => ↥(S' s)) ↪[rvLang] N),
    S ≤ S' ∧ a ∈ S' RVSort.K ∧
    S' RVSort.RV = S RVSort.RV ∧
    S' RVSort.Γ = S RVSort.Γ ∧
    ∀ (s : RVSort) (x : M s) (hx : x ∈ S s) (hx' : x ∈ S' s),
      e' s ⟨x, hx'⟩ = e s ⟨x, hx⟩

open scoped Classical in
/-- The `RV`-part of an embedding of a substructure, extended by `0` off its domain. This is
only ever used inside the domain; it is total so that it can be composed with homomorphisms. -/
noncomputable def embRV (ξ : M RVSort.RV) : N RVSort.RV :=
  if h : ξ ∈ S RVSort.RV then e RVSort.RV ⟨ξ, h⟩ else 0

omit [M ⊨ ACVFTheory] in
theorem embRV_apply {ξ : M RVSort.RV} (h : ξ ∈ S RVSort.RV) :
    embRV S e ξ = e RVSort.RV ⟨ξ, h⟩ := dite_eq_left h

theorem embRV_rvMap {x : M RVSort.K} (hx : x ∈ S RVSort.K) :
    embRV S e (rvMap x) = rvMap (subHom S e ⟨x, hx⟩) := by
  rw [embRV_apply S e (rvMap_mem_RV hx)]
  exact e_rvMap S e hx (rvMap_mem_RV hx)

@[simp]
theorem embRV_zero : embRV S e 0 = 0 := by
  have h0 : (0 : M RVSort.K) ∈ S RVSort.K := (subringOfSubstructure S).zero_mem
  have h1 : subHom S e ⟨(0 : M RVSort.K), h0⟩ = 0 := map_zero (subHom S e)
  rw [← model_rv_zero (M := M), embRV_rvMap S e h0, h1, model_rv_zero]

@[simp]
theorem embRV_one : embRV S e 1 = 1 := by
  have h0 : (1 : M RVSort.K) ∈ S RVSort.K := (subringOfSubstructure S).one_mem
  have h1 : subHom S e ⟨(1 : M RVSort.K), h0⟩ = 1 := map_one (subHom S e)
  rw [← model_rv_one (M := M), embRV_rvMap S e h0, h1, model_rv_one]

theorem embRV_mul {ξ η : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (hη : η ∈ S RVSort.RV) :
    embRV S e (ξ * η) = embRV S e ξ * embRV S e η := by
  rw [embRV_apply S e (mul_mem_RV hξ hη), embRV_apply S e hξ, embRV_apply S e hη]
  exact e_mulRV S e hξ hη (mul_mem_RV hξ hη)

theorem embRV_add {ξ η : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (hη : η ∈ S RVSort.RV) :
    embRV S e (ξ + η) = embRV S e ξ + embRV S e η := by
  rw [embRV_apply S e (add_mem_RV hξ hη), embRV_apply S e hξ, embRV_apply S e hη]
  exact e.map_fun' RVFunc.addRV
    ((⟨ξ, hξ⟩, ⟨η, hη⟩) : (fun s => ↥(S s)) [^] (⦃RVSort.RV⦄ ⨯ ⦃RVSort.RV⦄))

omit [M ⊨ ACVFTheory] in
theorem embRV_inj {ξ η : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (hη : η ∈ S RVSort.RV) (h : embRV S e ξ = embRV S e η) : ξ = η := by
  rw [embRV_apply S e hξ, embRV_apply S e hη] at h
  exact congrArg Subtype.val (e.injective RVSort.RV h)

omit [M ⊨ ACVFTheory] in
/-- The embedding commutes with `val` on its domain. -/
theorem valMap_embRV {ξ : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV) :
    valMap (embRV S e ξ) = e RVSort.Γ ⟨valMap ξ, valMap_mem_Gamma hξ⟩ := by
  rw [embRV_apply S e hξ]
  exact (e.map_fun' RVFunc.val (⟨ξ, hξ⟩ : ↥(S RVSort.RV))).symm

/-- The embedding's action on the leading term of a power, read in the valuation subring of the
target where powers are available. -/
theorem toRV_embRV_pow {x : M RVSort.K} (hx : rvMap x ∈ S RVSort.RV) (k : ℕ) :
    toRV (embRV S e (rvMap (x ^ k))) = (toRV (embRV S e (rvMap x))) ^ k := by
  induction k with
  | zero => rw [pow_zero, model_rv_one, embRV_one, toRV_one, pow_zero]
  | succ k ih =>
    rw [pow_succ, model_rv_mul, embRV_mul S e (rvMap_pow_mem_RV hx k) hx, toRV_mul, ih, pow_succ]

/-- The embedding carries units to units. -/
theorem valMap_embRV_eq_zero {ξ : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (h : valMap ξ = 0) : valMap (embRV S e ξ) = 0 := by
  have h0 : (⟨valMap ξ, valMap_mem_Gamma hξ⟩ : ↥(S RVSort.Γ))
      = ⟨0, zero_mem_Gamma⟩ := Subtype.ext h
  rw [valMap_embRV S e hξ, h0]
  exact e.map_fun' RVFunc.zeroΓ default

/-- The embedding reflects the order of values. -/
theorem valMap_embRV_le_iff {ξ η : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (hη : η ∈ S RVSort.RV) :
    valMap (embRV S e ξ) ≤ valMap (embRV S e η) ↔ valMap ξ ≤ valMap η := by
  rw [valMap_embRV S e hξ, valMap_embRV S e hη]
  exact e.map_rel' RVRel.leΓ ((⟨valMap ξ, valMap_mem_Gamma hξ⟩,
    ⟨valMap η, valMap_mem_Gamma hη⟩) : (fun s => ↥(S s)) [^] (⦃RVSort.Γ⦄ ⨯ ⦃RVSort.Γ⦄))

/-- **The embedding carries the valuation ring into the valuation ring.** Monotonicity for `val`
against `1` is all that is needed, and that is the order relation of the `Γ` sort. -/
theorem valuation_subHom_le_one {x : M RVSort.K} (hx : x ∈ S RVSort.K)
    (h : (modelValSubring M).valuation x ≤ 1) :
    (modelValSubring N).valuation (subHom S e ⟨x, hx⟩) ≤ 1 := by
  have h1M : (1 : M RVSort.K) ∈ S RVSort.K := (subringOfSubstructure S).one_mem
  have hiff := valMap_embRV_le_iff S e (rvMap_mem_RV h1M) (rvMap_mem_RV hx)
  rw [embRV_rvMap S e h1M, embRV_rvMap S e hx, valMap_le_iff_valuation,
    valMap_le_iff_valuation, show subHom S e ⟨(1 : M RVSort.K), h1M⟩ = 1 from map_one _,
    map_one, map_one] at hiff
  exact hiff.mpr h

/-! ### The map of leading-term structures of a subfield -/

variable {E F : Subfield (M RVSort.K)}

theorem rvOfSubfield_mem (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (ζ : ((modelValSubring M).comap E.subtype).RV) :
    rvOfSubfield E ζ ∈ S RVSort.RV := by
  obtain ⟨x, rfl⟩ := rv_surjective (A := (modelValSubring M).comap E.subtype) ζ
  rw [rvOfSubfield_rv]
  exact hE _ x.2

/-- **The leading-term map of a subfield, carried by an embedding.** If every leading term of the
subfield `E` lies in the `RV`-part of `S`, then the `RV`-part of `e` is total on the leading-term
structure of `E`, and this is the map the extension lemmas of
`Algebra/ACVF/ValuedField/Extend.lean` ask for. -/
noncomputable def liftRvHom (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV) :
    ((modelValSubring M).comap E.subtype).RV →*₀ (modelValSubring N).RV where
  toFun ζ := toRV (embRV S e (rvOfSubfield E ζ))
  map_zero' := by rw [rvOfSubfield_zero, embRV_zero, toRV_zero]
  map_one' := by rw [rvOfSubfield_one, embRV_one, toRV_one]
  map_mul' ζ η := by
    rw [rvOfSubfield_mul,
      embRV_mul S e (rvOfSubfield_mem S hE ζ) (rvOfSubfield_mem S hE η), toRV_mul]

theorem liftRvHom_apply (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (ζ : ((modelValSubring M).comap E.subtype).RV) :
    liftRvHom S e hE ζ = toRV (embRV S e (rvOfSubfield E ζ)) := rfl

@[simp]
theorem liftRvHom_rv (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV) (x : E) :
    liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype) x)
      = toRV (embRV S e (rvMap (x : M RVSort.K))) :=
  congrArg (fun ξ => toRV (embRV S e ξ)) (rvOfSubfield_rv E x)

theorem liftRvHom_injective (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV) :
    Function.Injective (liftRvHom S e hE) := by
  intro ζ η h
  exact rvOfSubfield_injective E (embRV_inj S e (rvOfSubfield_mem S hE ζ)
    (rvOfSubfield_mem S hE η) (toRV_injective h))

/-- **The order of values transfers between matched pairs.** This is the hypothesis `hmono` of
the extension lemmas, and it holds because an `L_RV`-embedding preserves both `val` and the order
of the `Γ` sort. -/
theorem liftRvHom_valuation_lt_iff (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    {u v : E} {u' v' : N RVSort.K}
    (hu : liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype) u)
      = rv (A := modelValSubring N) u')
    (hv : liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype) v)
      = rv (A := modelValSubring N) v') :
    ((modelValSubring M).comap E.subtype).valuation u
        < ((modelValSubring M).comap E.subtype).valuation v
      ↔ (modelValSubring N).valuation u' < (modelValSubring N).valuation v' := by
  rw [liftRvHom_rv, ← toRV_rvMap] at hu hv
  have hu' : embRV S e (rvMap (u : M RVSort.K)) = rvMap u' := toRV_injective hu
  have hv' : embRV S e (rvMap (v : M RVSort.K)) = rvMap v' := toRV_injective hv
  rw [valuation_comap_lt_iff]
  change (modelValSubring M).valuation (u : M RVSort.K)
      < (modelValSubring M).valuation (v : M RVSort.K) ↔ _
  rw [← not_le, ← not_le, ← valMap_le_iff_valuation (u : M RVSort.K) (v : M RVSort.K),
    ← valMap_le_iff_valuation u' v',
    ← valMap_embRV_le_iff S e (hE _ u.2) (hE _ v.2), hu', hv']

/-- **The residue addition transfers.** Together with `liftRvHom_rvVal_lt_iff` this is what
`Language.resRingHom` needs in order to induce a homomorphism of residue fields. -/
theorem liftRvHom_rvAdd (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (ζ η : ((modelValSubring M).comap E.subtype).RV) :
    liftRvHom S e hE (rvAdd ((modelValSubring M).comap E.subtype) ζ η)
      = rvAdd (modelValSubring N) (liftRvHom S e hE ζ) (liftRvHom S e hE η) := by
  rw [liftRvHom_apply, liftRvHom_apply, liftRvHom_apply, rvOfSubfield_rvAdd,
    embRV_add S e (rvOfSubfield_mem S hE ζ) (rvOfSubfield_mem S hE η), toRV_add]

/-- **The order of values transfers, everywhere on the leading terms of the subfield.** This is
the hypothesis `hmono` of `Language.resRingHom`, and it follows from the matched-pair form
because every leading term of `E` has a match: `rv` is onto in the target. -/
theorem liftRvHom_rvVal_lt_iff (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (ζ η : ((modelValSubring M).comap E.subtype).RV) :
    rvVal ζ < rvVal η ↔ rvVal (liftRvHom S e hE ζ) < rvVal (liftRvHom S e hE η) := by
  obtain ⟨u, rfl⟩ := rv_surjective (A := (modelValSubring M).comap E.subtype) ζ
  obtain ⟨v, rfl⟩ := rv_surjective (A := (modelValSubring M).comap E.subtype) η
  obtain ⟨u', hu'⟩ := model_rv_surjective (M := N) (embRV S e (rvMap (u : M RVSort.K)))
  obtain ⟨v', hv'⟩ := model_rv_surjective (M := N) (embRV S e (rvMap (v : M RVSort.K)))
  have hu : liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype) u)
      = rv (A := modelValSubring N) u' := by rw [liftRvHom_rv, ← hu', toRV_rvMap]
  have hv : liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype) v)
      = rv (A := modelValSubring N) v' := by rw [liftRvHom_rv, ← hv', toRV_rvMap]
  rw [hu, hv, rvVal_rv, rvVal_rv, rvVal_rv, rvVal_rv]
  exact liftRvHom_valuation_lt_iff S e hE hu hv

/-! ### The coefficient field -/

/-- The ring homomorphism on a subfield of the field sort carried by an embedding of a
substructure containing it. -/
def subfieldHom (hFS : ∀ x ∈ F, x ∈ S RVSort.K) : F →+* N RVSort.K where
  toFun x := e RVSort.K ⟨x.1, hFS x.1 x.2⟩
  map_one' := e.map_fun' RVFunc.oneK default
  map_zero' := e.map_fun' RVFunc.zeroK default
  map_add' x y := e.map_fun' RVFunc.addK
    ((⟨x.1, hFS x.1 x.2⟩, ⟨y.1, hFS y.1 y.2⟩) :
      (fun s => ↥(S s)) [^] (⦃RVSort.K⦄ ⨯ ⦃RVSort.K⦄))
  map_mul' x y := e.map_fun' RVFunc.mulK
    ((⟨x.1, hFS x.1 x.2⟩, ⟨y.1, hFS y.1 y.2⟩) :
      (fun s => ↥(S s)) [^] (⦃RVSort.K⦄ ⨯ ⦃RVSort.K⦄))

@[simp]
theorem subfieldHom_apply (hFS : ∀ x ∈ F, x ∈ S RVSort.K) (x : F) :
    subfieldHom S e hFS x = e RVSort.K ⟨x.1, hFS x.1 x.2⟩ := rfl

/-- **Compatibility with the coefficient field.** This is the hypothesis `hcompat` of the
extension lemmas. -/
theorem liftRvHom_compat (hFE : F ≤ E) (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K) (r : F) :
    liftRvHom S e hE (rv (A := (modelValSubring M).comap E.subtype)
        (Subfield.inclusion hFE r))
      = rv (A := modelValSubring N) (subfieldHom S e hFS r) := by
  rw [liftRvHom_rv]
  have h : ((Subfield.inclusion hFE r : E) : M RVSort.K) = (r : M RVSort.K) := rfl
  rw [h, embRV_rvMap S e (hFS r.1 r.2), toRV_rvMap]
  rfl

/-! ### Assembly: adjoining the element to the field sort -/

/-- The inclusion of `F[a]` into the field sort, for `a` in a subfield `E` containing `F`. -/
noncomputable def liftIncl (hFE : F ≤ E) (a : E) :
    (evalOn (Subfield.inclusion hFE) a).range →+* M RVSort.K :=
  E.subtype.comp (evalOn (Subfield.inclusion hFE) a).range.subtype

theorem liftIncl_injective (hFE : F ≤ E) (a : E) :
    Function.Injective (liftIncl hFE a) := by
  intro x y h
  have h' : ((x : E) : M RVSort.K) = ((y : E) : M RVSort.K) := h
  exact Subtype.ext (Subtype.ext h')

theorem mem_liftIncl_range_of_mem (hFE : F ≤ E) (a : E) {x : M RVSort.K} (hx : x ∈ F) :
    x ∈ (liftIncl hFE a).range :=
  RingHom.mem_range.mpr
    ⟨⟨Subfield.inclusion hFE ⟨x, hx⟩, RingHom.mem_range.mpr ⟨C ⟨x, hx⟩, by simp⟩⟩, rfl⟩

theorem self_mem_liftIncl_range (hFE : F ≤ E) (a : E) :
    ((a : E) : M RVSort.K) ∈ (liftIncl hFE a).range :=
  RingHom.mem_range.mpr ⟨⟨a, RingHom.mem_range.mpr ⟨X, by simp⟩⟩, rfl⟩

theorem liftIncl_range_le (hFE : F ≤ E) (a : E) :
    ∀ x ∈ (liftIncl hFE a).range, x ∈ E := by
  intro x hx
  obtain ⟨y, rfl⟩ := RingHom.mem_range.mp hx
  exact (y : E).2

/-- **The substructure obtained by adjoining one element to the field sort.** Its field part is
`F[a]`; its `RV`- and `Γ`-parts are those of `S`, unchanged. -/
noncomputable def liftAdjoin (hFE : F ≤ E)
    (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F) (a : E) : rvLang.Substructure M :=
  adjoinSubstructure S (liftIncl hFE a).range
    (fun _ hx => mem_liftIncl_range_of_mem hFE a (hSF _ hx))
    (fun _ hx => hE _ (liftIncl_range_le hFE a _ hx))

variable {a : E} {b : N RVSort.K}

/-- The ring homomorphism on `F[a]`, obtained from `ValuationSubring.extend` inside `E` and
transported back to the field sort. -/
noncomputable def liftHom (hFE : F ≤ E)
    (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS) a b) :
    (liftIncl hFE a).range →+* N RVSort.K :=
  rangeLift (liftIncl_injective hFE a) (extend (liftRvHom_injective S e hE) H)

theorem liftHom_eq (hFE : F ≤ E) (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS) a b)
    {x : (liftIncl hFE a).range} {y : (evalOn (Subfield.inclusion hFE) a).range}
    (h : liftIncl hFE a y = x.1) :
    liftHom S e hFE hE hFS H x = extend (liftRvHom_injective S e hE) H y :=
  rangeLift_eq _ _ h

theorem liftHom_injective (hFE : F ≤ E)
    (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS) a b) :
    Function.Injective (liftHom S e hFE hE hFS H) :=
  rangeLift_injective _ _ (extend_injective (liftRvHom_injective S e hE) H)

/-- The new homomorphism commutes with `rv`, which is what `adjoinEmbedding` asks for. -/
theorem liftHom_rv (hFE : F ≤ E) (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS) a b)
    (x : (liftIncl hFE a).range) :
    e RVSort.RV ⟨rvMap (x : M RVSort.K), hE _ (liftIncl_range_le hFE a _ x.2)⟩
      = rvMap (liftHom S e hFE hE hFS H x) := by
  obtain ⟨y, hy⟩ := RingHom.mem_range.mp x.2
  have hrv := rv_extend (liftRvHom_injective S e hE) H y
  rw [liftRvHom_rv] at hrv
  have hxy : ((y : E) : M RVSort.K) = (x : M RVSort.K) := hy
  rw [hxy] at hrv
  rw [liftHom_eq S e hFE hE hFS H hy]
  refine (toRV_injective ?_).symm
  rw [toRV_rvMap, ← hrv, embRV_apply S e (hE _ (liftIncl_range_le hFE a _ x.2))]

/-- **The extended embedding.** An embedding of `S` together with the leading-term data extends
to an embedding of the substructure whose field part is `F[a]`, with the `RV`- and `Γ`-parts
unchanged. -/
noncomputable def liftEmbedding (hFE : F ≤ E)
    (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F)
    (H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS) a b) :
    (fun s => ↥(liftAdjoin S hFE hE hSF a s)) ↪[rvLang] N :=
  adjoinEmbedding S (fun _ hx => mem_liftIncl_range_of_mem hFE a (hSF _ hx))
    (fun _ hx => hE _ (liftIncl_range_le hFE a _ hx)) e
    (liftHom S e hFE hE hFS H) (liftHom_injective S e hFE hE hFS H)
    (liftHom_rv S e hFE hE hFS H)

@[simp]
theorem liftEmbedding_apply_K (hFE : F ≤ E)
    (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F)
    (H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS) a b)
    (m : ↥(liftAdjoin S hFE hE hSF a RVSort.K)) :
    liftEmbedding S e hFE hE hFS hSF H RVSort.K m = liftHom S e hFE hE hFS H ⟨m.1, m.2⟩ := rfl

/-- The extended embedding really extends the given one. -/
theorem liftEmbedding_apply_K_of_mem (hFE : F ≤ E)
    (hE : ∀ x ∈ E, rvMap x ∈ S RVSort.RV)
    (hFS : ∀ x ∈ F, x ∈ S RVSort.K)
    (hSF : ∀ x ∈ S RVSort.K, x ∈ F)
    (H : RvTypeEq (liftRvHom S e hE) (Subfield.inclusion hFE) (subfieldHom S e hFS) a b)
    {x : M RVSort.K} (hx : x ∈ S RVSort.K)
    (hx' : x ∈ (liftAdjoin S hFE hE hSF a) RVSort.K) :
    liftEmbedding S e hFE hE hFS hSF H RVSort.K ⟨x, hx'⟩ = e RVSort.K ⟨x, hx⟩ := by
  set y : (evalOn (Subfield.inclusion hFE) a).range :=
    ⟨Subfield.inclusion hFE ⟨x, hSF x hx⟩,
      RingHom.mem_range.mpr ⟨C ⟨x, hSF x hx⟩, by simp⟩⟩ with hy
  have hC : y = (evalOn (Subfield.inclusion hFE) a).rangeRestrict (C ⟨x, hSF x hx⟩) :=
    Subtype.ext (by simp [hy])
  have heval : evalOn' (subfieldHom S e hFS) b (C (⟨x, hSF x hx⟩ : F))
      = subfieldHom S e hFS ⟨x, hSF x hx⟩ := by simp
  rw [liftEmbedding_apply_K, liftHom_eq S e hFE hE hFS H (y := y) rfl, hC, extend_eval, heval]
  rfl

end LiftOne

end ManySorted.Language
