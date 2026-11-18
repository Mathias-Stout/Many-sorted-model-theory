/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.Substructure.AdjoinElement
public import MultisortedLogic.Algebra.ACVF.RVLift.RVPart
public import MultisortedLogic.Algebra.ACVF.Reduction

/-!
# The `Γ`-part step of `RVLift`: bringing the `Γ`-part down to the values of the `RV`-part

A substructure is a triple `(R, V, G)` in which `G` is only required to be a subgroup of the `Γ`
sort *containing* `val V`; it may be strictly larger, and the embedding test hands over arbitrary
substructures. But `RVLift` asks for `S ≤ fieldSubstructure M F`, whose `Γ`-part is exactly
`val (rv F)`. So every `γ ∈ G` has to be realized as the value of a leading term of `F`.

The move is to grow the **subfield**, not the substructure: adjoin an `a` of the field sort with
`val (rv a) = γ`. Since `γ ∉ val (rv F)` by assumption, that is the *ramified* situation, which
`Algebra/ACVF/Substructure/AdjoinElement.lean` handles — and because `FieldEmbeddingData` mentions
only a ring homomorphism and its two reflection properties, the map on the new leading terms is
forced and none of the many-sorted plumbing of the `RV` sort is needed.

Two invariants ride along, and this file is mostly their bookkeeping:

* every value of `F` lies in `G`, and
* the embedding's values are the ones `e` prescribes: `val (rv (d x)) = e (val (rv x))`.

They are what let the ramified hypothesis `RamifiedMono` be met — the monomials `r · aⁱ` and
`d r · bⁱ` are ordered alike because `e` *reflects* the order of the `Γ` sort — and they are
preserved by the enlargement because `exists_monomial_adjoinHom` says every value of `F[a]` is a
value of `F` plus a multiple of `γ`, with the matching computation on the far side.

## Main statements

* `Language.exists_gamma_lift` : the enlargement.
* `Language.GammaApprox`, `Language.GammaApprox.chainBound` : the iteration.
* `Language.RVLift_full` : **`RVLift` in full** — every embedding of a substructure extends to an
  embedding of a field-like substructure containing it, with `N` itself as the target.
* `Language.RVLift_holds` : hence **`RVLift`**, the first of the two hypotheses of
  `ACVF_hasQERelTo_empty_of_lift_step`.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]
variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]

/-! ### The `Γ`-part of a substructure -/

section GammaPart

variable (S : rvLang.Substructure M)

/-- A substructure's `Γ`-part is closed under addition. -/
theorem add_mem_Gamma {γ δ : M RVSort.Γ} (hγ : γ ∈ S RVSort.Γ)
    (hδ : δ ∈ S RVSort.Γ) : γ + δ ∈ S RVSort.Γ :=
  S.fun_mem RVFunc.addΓ (γ, δ) (fun _ i => by
    cases i with
    | left i' => cases i'; exact hγ
    | right i' => cases i'; exact hδ)

/-- A substructure's `Γ`-part is closed under negation. -/
theorem neg_mem_Gamma {γ : M RVSort.Γ} (hγ : γ ∈ S RVSort.Γ) :
    -γ ∈ S RVSort.Γ :=
  S.fun_mem RVFunc.negΓ γ (fun _ i => by cases i; exact hγ)

/-- A substructure's `Γ`-part contains `∞`. -/
theorem top_mem_Gamma : (⊤ : M RVSort.Γ) ∈ S RVSort.Γ :=
  S.fun_mem RVFunc.inftyΓ _ (fun _ i => by cases i)

/-- The value of a product in the field sort. -/
theorem model_valrv_mul (x y : M RVSort.K) :
    valMap (rvMap (x * y)) = valMap (rvMap x) + valMap (rvMap y) := by
  rw [model_rv_mul, model_val_mul]

/-- A substructure's `Γ`-part is closed under the values of powers. -/
theorem valMap_pow_mem_Gamma {x : M RVSort.K}
    (hx : valMap (rvMap x) ∈ S RVSort.Γ) (k : ℕ) :
    valMap (rvMap (x ^ k)) ∈ S RVSort.Γ := by
  induction k with
  | zero =>
    rw [pow_zero, model_rv_one, model_val_one]
    exact zero_mem_Gamma
  | succ k ih =>
    rw [pow_succ, model_valrv_mul]
    exact add_mem_Gamma S ih hx

end GammaPart

/-! ### The embedding on the `Γ` sort -/

section GammaEmbedding

variable (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N)

theorem e_addΓ {γ δ : M RVSort.Γ} (hγ : γ ∈ S RVSort.Γ)
    (hδ : δ ∈ S RVSort.Γ) (h : γ + δ ∈ S RVSort.Γ) :
    e RVSort.Γ ⟨γ + δ, h⟩ = e RVSort.Γ ⟨γ, hγ⟩ + e RVSort.Γ ⟨δ, hδ⟩ :=
  e.map_fun' RVFunc.addΓ
    ((⟨γ, hγ⟩, ⟨δ, hδ⟩) : (fun s => ↥(S s)) [^] (⦃RVSort.Γ⦄ ⨯ ⦃RVSort.Γ⦄))

theorem e_negΓ {γ : M RVSort.Γ} (hγ : γ ∈ S RVSort.Γ)
    (h : -γ ∈ S RVSort.Γ) :
    e RVSort.Γ ⟨-γ, h⟩ = -(e RVSort.Γ ⟨γ, hγ⟩) :=
  e.map_fun' RVFunc.negΓ (⟨γ, hγ⟩ : ↥(S RVSort.Γ))

theorem e_zeroΓ (h : (0 : M RVSort.Γ) ∈ S RVSort.Γ) :
    e RVSort.Γ ⟨0, h⟩ = 0 :=
  e.map_fun' RVFunc.zeroΓ default

theorem e_topΓ (h : (⊤ : M RVSort.Γ) ∈ S RVSort.Γ) :
    e RVSort.Γ ⟨⊤, h⟩ = ⊤ :=
  e.map_fun' RVFunc.inftyΓ default

/-- The embedding reflects the order of the `Γ` sort. -/
theorem e_leΓ {γ δ : M RVSort.Γ} (hγ : γ ∈ S RVSort.Γ)
    (hδ : δ ∈ S RVSort.Γ) :
    e RVSort.Γ ⟨γ, hγ⟩ ≤ e RVSort.Γ ⟨δ, hδ⟩ ↔ γ ≤ δ :=
  e.map_rel' RVRel.leΓ
    ((⟨γ, hγ⟩, ⟨δ, hδ⟩) : (fun s => ↥(S s)) [^] (⦃RVSort.Γ⦄ ⨯ ⦃RVSort.Γ⦄))

theorem e_ltΓ {γ δ : M RVSort.Γ} (hγ : γ ∈ S RVSort.Γ)
    (hδ : δ ∈ S RVSort.Γ) :
    e RVSort.Γ ⟨γ, hγ⟩ < e RVSort.Γ ⟨δ, hδ⟩ ↔ γ < δ := by
  rw [← not_le, ← not_le, not_iff_not]
  exact e_leΓ S e hδ hγ

/-- `∞` is not the image of anything else, so an element of the `Γ`-part other than `∞` has an
image other than `∞`. -/
theorem e_ne_topΓ {γ : M RVSort.Γ} (hγ : γ ∈ S RVSort.Γ) (h : γ ≠ ⊤) :
    e RVSort.Γ ⟨γ, hγ⟩ ≠ ⊤ := by
  intro hc
  have h1 : e RVSort.Γ (⟨γ, hγ⟩ : ↥(S RVSort.Γ))
      = e RVSort.Γ (⟨⊤, top_mem_Gamma S⟩ : ↥(S RVSort.Γ)) := by
    rw [hc, e_topΓ S e]
  exact h (congrArg (fun z : ↥(S RVSort.Γ) => z.1) (e.injective RVSort.Γ h1))

/-- **The embedding commutes with `val ∘ rv` on powers.** -/
theorem e_valMap_pow {x : M RVSort.K} {y : N RVSort.K}
    (hxΓ : valMap (rvMap x) ∈ S RVSort.Γ)
    (hxy : valMap (rvMap y) = e RVSort.Γ ⟨valMap (rvMap x), hxΓ⟩) (k : ℕ) :
    valMap (rvMap (y ^ k))
      = e RVSort.Γ ⟨valMap (rvMap (x ^ k)), valMap_pow_mem_Gamma S hxΓ k⟩ := by
  induction k with
  | zero =>
    have h1 : e RVSort.Γ (⟨valMap (rvMap (x ^ 0)), valMap_pow_mem_Gamma S hxΓ 0⟩ :
          ↥(S RVSort.Γ))
        = e RVSort.Γ (⟨0, zero_mem_Gamma⟩ : ↥(S RVSort.Γ)) :=
      congrArg _ (Subtype.ext (by
        change valMap (rvMap (x ^ 0)) = (0 : M RVSort.Γ)
        rw [pow_zero, model_rv_one, model_val_one]))
    rw [h1, e_zeroΓ S e, pow_zero, model_rv_one, model_val_one]
  | succ k ih =>
    have h1 : e RVSort.Γ (⟨valMap (rvMap (x ^ (k + 1))), valMap_pow_mem_Gamma S hxΓ (k + 1)⟩ :
          ↥(S RVSort.Γ))
        = e RVSort.Γ (⟨valMap (rvMap (x ^ k)) + valMap (rvMap x),
            add_mem_Gamma S (valMap_pow_mem_Gamma S hxΓ k) hxΓ⟩ : ↥(S RVSort.Γ)) :=
      congrArg _ (Subtype.ext (by
        change valMap (rvMap (x ^ (k + 1)))
          = valMap (rvMap (x ^ k)) + valMap (rvMap x)
        rw [pow_succ, model_valrv_mul]))
    rw [h1, e_addΓ S e (valMap_pow_mem_Gamma S hxΓ k) hxΓ, ← ih, ← hxy, pow_succ,
      model_valrv_mul]

end GammaEmbedding

/-! ### The `Γ`-bookkeeping of a quotient -/

section DivGamma

variable (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N)
variable {T : Subring (M RVSort.K)} (dT : RingEmbeddingData T N)
variable (hTmem : ∀ x ∈ T, valMap (rvMap x) ∈ S RVSort.Γ)

include hTmem in
/-- The values of the subfield of quotients are still in the `Γ`-part. -/
theorem valMap_divField_mem {x : M RVSort.K} (hx : x ∈ divField T) :
    valMap (rvMap x) ∈ S RVSort.Γ := by
  obtain ⟨y, hy, z, hz, -, rfl⟩ := mem_divField_iff.mp hx
  rw [div_eq_mul_inv, model_valrv_mul, ← model_neg_val]
  exact add_mem_Gamma S (hTmem y hy) (neg_mem_Gamma S (hTmem z hz))

variable (hT : ∀ (x : M RVSort.K) (hx : x ∈ T),
  valMap (rvMap (dT.hom ⟨x, hx⟩)) = e RVSort.Γ ⟨valMap (rvMap x), hTmem x hx⟩)

include hT in
/-- **The `Γ`-bookkeeping passes to the subfield of quotients**, because `val ∘ rv` turns the
quotient into a difference and `e` is additive on the `Γ` sort. -/
theorem gamma_divHom {x : M RVSort.K} (hx : x ∈ divField T)
    (hmem : valMap (rvMap x) ∈ S RVSort.Γ) :
    valMap (rvMap (dT.divHom ⟨x, hx⟩)) = e RVSort.Γ ⟨valMap (rvMap x), hmem⟩ := by
  obtain ⟨y, hy, z, hz, -, hyz⟩ := mem_divField_iff.mp hx
  have hval : valMap (rvMap x) = valMap (rvMap y) + -(valMap (rvMap z)) := by
    rw [← hyz, div_eq_mul_inv, model_valrv_mul, ← model_neg_val]
  have h1 : e RVSort.Γ (⟨valMap (rvMap x), hmem⟩ : ↥(S RVSort.Γ))
      = e RVSort.Γ (⟨valMap (rvMap y) + -(valMap (rvMap z)),
          add_mem_Gamma S (hTmem y hy) (neg_mem_Gamma S (hTmem z hz))⟩ :
            ↥(S RVSort.Γ)) :=
    congrArg _ (Subtype.ext hval)
  rw [h1, e_addΓ S e (hTmem y hy) (neg_mem_Gamma S (hTmem z hz)), e_negΓ S e (hTmem z hz),
    ← hT y hy, ← hT z hz, dT.divHom_eq hy hz hyz, div_eq_mul_inv, model_valrv_mul,
    ← model_neg_val]

end DivGamma

/-! ### The enlargement -/

section Enlarge

variable (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N)
variable (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)
variable (hΓmem : ∀ x ∈ F, valMap (rvMap x) ∈ S RVSort.Γ)
variable (hΓ : ∀ (x : M RVSort.K) (hx : x ∈ F),
  valMap (rvMap (d.hom ⟨x, hx⟩)) = e RVSort.Γ ⟨valMap (rvMap x), hΓmem x hx⟩)
variable {a : M RVSort.K} {b : N RVSort.K}
variable (haΓ : valMap (rvMap a) ∈ S RVSort.Γ)
variable (hab : valMap (rvMap b) = e RVSort.Γ ⟨valMap (rvMap a), haΓ⟩)

include hΓmem haΓ in
/-- The value of a monomial `c · aⁱ` lies in the `Γ`-part. -/
theorem valMap_monomial_mem (c : F) (i : ℕ) :
    valMap (rvMap ((c : M RVSort.K) * a ^ i)) ∈ S RVSort.Γ := by
  rw [model_valrv_mul]
  exact add_mem_Gamma S (hΓmem _ c.2) (valMap_pow_mem_Gamma S haΓ i)

include hΓ hab in
/-- **And its image is the one `e` prescribes.** -/
theorem gamma_monomial (c : F) (i : ℕ) :
    valMap (rvMap (d.hom c * b ^ i))
      = e RVSort.Γ ⟨valMap (rvMap ((c : M RVSort.K) * a ^ i)),
          valMap_monomial_mem S F hΓmem haΓ c i⟩ := by
  have h1 : e RVSort.Γ (⟨valMap (rvMap ((c : M RVSort.K) * a ^ i)),
          valMap_monomial_mem S F hΓmem haΓ c i⟩ : ↥(S RVSort.Γ))
      = e RVSort.Γ (⟨valMap (rvMap (c : M RVSort.K)) + valMap (rvMap (a ^ i)),
          add_mem_Gamma S (hΓmem _ c.2) (valMap_pow_mem_Gamma S haΓ i)⟩ :
            ↥(S RVSort.Γ)) :=
    congrArg _ (Subtype.ext (by
      change valMap (rvMap ((c : M RVSort.K) * a ^ i))
        = valMap (rvMap (c : M RVSort.K)) + valMap (rvMap (a ^ i))
      rw [model_valrv_mul]))
  rw [h1, e_addΓ S e (hΓmem _ c.2) (valMap_pow_mem_Gamma S haΓ i), ← hΓ _ c.2,
    ← e_valMap_pow S e haΓ hab i, model_valrv_mul]

include hΓ hab in
/-- **The domination hypothesis, from the `Γ`-bookkeeping.** The monomials `r · aⁱ` and
`d r · bⁱ` are ordered alike because `e` *reflects* the order of the `Γ` sort, and every value in
sight lies in the `Γ`-part of `S`. -/
theorem gamma_mono :
    ∀ (r r' : F) (i i' : ℕ),
      valMap (rvMap ((r : M RVSort.K) * a ^ i))
          < valMap (rvMap ((r' : M RVSort.K) * a ^ i'))
        ↔ valMap (rvMap (d.hom r * b ^ i)) < valMap (rvMap (d.hom r' * b ^ i')) := by
  intro r r' i i'
  rw [gamma_monomial S e F d hΓmem hΓ haΓ hab r i, gamma_monomial S e F d hΓmem hΓ haΓ hab r' i']
  exact (e_ltΓ S e _ _).symm

variable (h : RamifiedReflectAll F.subtype d.hom (modelValSubring M) (modelValSubring N) a b)

include hΓmem haΓ h in
/-- The values of `F[a]` are in the `Γ`-part: by `exists_monomial_adjoinHom` each of them is the
value of a monomial. -/
theorem valMap_adjoin_mem (x : (evalOn F.subtype a).range) :
    valMap (rvMap (x : M RVSort.K)) ∈ S RVSort.Γ := by
  obtain ⟨c, hc, i, h1, -⟩ := exists_monomial_adjoinHom F d h x
  rw [h1]
  exact valMap_monomial_mem S F hΓmem haΓ ⟨c, hc⟩ i

include hΓ hab in
/-- **And the `Γ`-bookkeeping holds on `F[a]`.** -/
theorem gamma_adjoinHom (x : (evalOn F.subtype a).range)
    (hmem : valMap (rvMap (x : M RVSort.K)) ∈ S RVSort.Γ) :
    valMap (rvMap (adjoinHom F d h.toReflectData x))
      = e RVSort.Γ ⟨valMap (rvMap (x : M RVSort.K)), hmem⟩ := by
  obtain ⟨c, hc, i, h1, h2⟩ := exists_monomial_adjoinHom F d h x
  rw [congrArg valMap h2, gamma_monomial S e F d hΓmem hΓ haΓ hab ⟨c, hc⟩ i]
  exact congrArg _ (Subtype.ext (congrArg valMap h1).symm)

end Enlarge

/-! ### Realizing one value of the `Γ`-part -/

section Lift

variable (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N)
variable (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N)
variable (hΓmem : ∀ x ∈ F, valMap (rvMap x) ∈ S RVSort.Γ)
variable (hΓ : ∀ (x : M RVSort.K) (hx : x ∈ F),
  valMap (rvMap (d.hom ⟨x, hx⟩)) = e RVSort.Γ ⟨valMap (rvMap x), hΓmem x hx⟩)

include hΓ in
/-- **The element to adjoin, and its partner.** For a `γ` in the `Γ`-part that is not yet a value
of `F`, an `a` of the field sort with `val (rv a) = γ`, and a `b` with `val (rv b) = e γ`, whose
leading-term types over `F` and over `d F` match.

The order `n` of `γ` over the values of `F` splits the two cases. At finite order, `γ` is not
chosen and then realized: an `n`-th root of the witness `c₀` is taken, and its value is *forced*
to be `γ`, because `n`-th roots are unique in a linearly ordered group. The same on the far side,
so `b` needs no separate matching argument — which is the one place where this differs from
the routing, where the far-side element has to be chosen with care. -/
theorem exists_ramified_witness {γ : M RVSort.Γ} (hγS : γ ∈ S RVSort.Γ)
    (hγF : ∀ x ∈ F, valMap (rvMap x) ≠ γ) :
    ∃ (a : M RVSort.K) (b : N RVSort.K),
      valMap (rvMap a) = γ ∧ valMap (rvMap b) = e RVSort.Γ ⟨γ, hγS⟩ ∧
        RamifiedReflectAll F.subtype d.hom (modelValSubring M) (modelValSubring N) a b := by
  classical
  have hγtop : γ ≠ ⊤ := fun hc => hγF 0 F.zero_mem (by rw [model_val_zero, hc])
  obtain ⟨a₀, ha₀⟩ := valrv_surjective (M := M) γ
  have ha₀' : valMap (rvMap a₀) = γ := ha₀
  obtain ⟨b₀, hb₀⟩ := valrv_surjective (M := N) (e RVSort.Γ ⟨γ, hγS⟩)
  have hb₀' : valMap (rvMap b₀) = e RVSort.Γ ⟨γ, hγS⟩ := hb₀
  have ha₀0 : a₀ ≠ 0 := by
    intro hc
    rw [hc, model_val_zero] at ha₀'
    exact hγtop ha₀'.symm
  have hb₀0 : b₀ ≠ 0 := by
    intro hc
    rw [hc, model_val_zero] at hb₀'
    exact e_ne_topΓ S e hγS hγtop hb₀'.symm
  have haΓ₀ : valMap (rvMap a₀) ∈ S RVSort.Γ := by rw [ha₀']; exact hγS
  have hab₀ : valMap (rvMap b₀) = e RVSort.Γ ⟨valMap (rvMap a₀), haΓ₀⟩ := by
    rw [hb₀']
    exact congrArg _ (Subtype.ext ha₀'.symm)
  by_cases hfin : ∃ n : ℕ, 0 < n ∧ ∃ c ∈ F, valMap (rvMap (a₀ ^ n)) = valMap (rvMap c)
  · -- finite order over the values of `F`
    set n := Nat.find hfin with hndef
    obtain ⟨hn, c₀, hc₀F, hc₀⟩ := Nat.find_spec hfin
    have hord₀ : ∀ k : ℕ, 0 < k → k < n →
        ∀ c ∈ F, valMap (rvMap (a₀ ^ k)) ≠ valMap (rvMap c) := by
      intro k hk hkn c hc hcon
      exact Nat.find_min hfin hkn ⟨hk, c, hc, hcon⟩
    -- an `n`-th root of the witness, whose value is forced to be `γ`
    have hva₀ : (modelValSubring M).valuation a₀ ^ n = (modelValSubring M).valuation c₀ := by
      rw [← map_pow]
      exact (valMap_eq_iff_valuation _ _).mp hc₀
    obtain ⟨a, hapow, hava⟩ := exists_pow_eq_of_valuation (A := modelValSubring M) hn hva₀
    have haγ : valMap (rvMap a) = γ :=
      ((valMap_eq_iff_valuation _ _).mpr hava).trans ha₀'
    have haΓ : valMap (rvMap a) ∈ S RVSort.Γ := by rw [haγ]; exact hγS
    have ha0 : a ≠ 0 := by
      intro hc
      rw [hc, model_val_zero] at haγ
      exact hγtop haγ.symm
    -- and an `n`-th root of its image, whose value is forced likewise
    have hvb₀ : (modelValSubring N).valuation b₀ ^ n
        = (modelValSubring N).valuation (d.hom ⟨c₀, hc₀F⟩) := by
      rw [← map_pow]
      refine (valMap_eq_iff_valuation _ _).mp ?_
      rw [e_valMap_pow S e haΓ₀ hab₀ n, hΓ c₀ hc₀F]
      exact congrArg _ (Subtype.ext hc₀)
    obtain ⟨b, hbpow, hbvb⟩ := exists_pow_eq_of_valuation (A := modelValSubring N) hn hvb₀
    have hbγ : valMap (rvMap b) = e RVSort.Γ ⟨γ, hγS⟩ :=
      ((valMap_eq_iff_valuation _ _).mpr hbvb).trans hb₀'
    have hb0 : b ≠ 0 := by
      intro hc
      rw [hc, model_val_zero] at hbγ
      exact e_ne_topΓ S e hγS hγtop hbγ.symm
    have hab : valMap (rvMap b) = e RVSort.Γ ⟨valMap (rvMap a), haΓ⟩ := by
      rw [hbγ]
      exact congrArg _ (Subtype.ext haγ.symm)
    have hord : ∀ k : ℕ, 0 < k → k < n →
        ∀ c ∈ F, valMap (rvMap (a ^ k)) ≠ valMap (rvMap c) := by
      intro k hk hkn c hc hcon
      refine hord₀ k hk hkn c hc ?_
      refine Eq.trans ?_ hcon
      exact (valMap_eq_iff_valuation _ _).mpr (by rw [map_pow, map_pow, hava])
    exact ⟨a, b, haγ, hbγ,
      ramifiedReflectAll_finite_of_model F d ha0 hb0 hn
        (gamma_mono S e F d hΓmem hΓ haΓ hab) hord (c := ⟨c₀, hc₀F⟩) hapow hbpow⟩
  · -- infinite order over the values of `F`
    have hord : ∀ k : ℕ, 0 < k → ∀ c ∈ F, valMap (rvMap (a₀ ^ k)) ≠ valMap (rvMap c) :=
      fun k hk c hc hcon => hfin ⟨k, hk, c, hc, hcon⟩
    exact ⟨a₀, b₀, ha₀', hb₀',
      ramifiedReflectAll_infinite_of_model F d ha₀0 hb₀0
        (gamma_mono S e F d hΓmem hΓ haΓ₀ hab₀) hord⟩

include hΓ in
/-- **The `Γ`-part step, one value at a time.** A field-like embedding whose values lie in the
`Γ`-part of `S` and agree with `e` there extends to one that also realizes a prescribed
`γ ∈ S Γ`, with the two invariants intact. -/
theorem exists_gamma_lift {γ : M RVSort.Γ} (hγS : γ ∈ S RVSort.Γ)
    (hγF : ∀ x ∈ F, valMap (rvMap x) ≠ γ) :
    ∃ (F' : Subfield (M RVSort.K)) (hFF' : F ≤ F') (d' : FieldEmbeddingData F' N)
      (hΓmem' : ∀ x ∈ F', valMap (rvMap x) ∈ S RVSort.Γ),
      (∀ (x : M RVSort.K) (hx : x ∈ F), d'.hom ⟨x, hFF' hx⟩ = d.hom ⟨x, hx⟩) ∧
        (∀ (x : M RVSort.K) (hx : x ∈ F'),
          valMap (rvMap (d'.hom ⟨x, hx⟩)) = e RVSort.Γ ⟨valMap (rvMap x), hΓmem' x hx⟩) ∧
        ∃ x ∈ F', valMap (rvMap x) = γ := by
  obtain ⟨a, b, haγ, hbγ, h⟩ := exists_ramified_witness S e F d hΓmem hΓ hγS hγF
  have haΓ : valMap (rvMap a) ∈ S RVSort.Γ := by rw [haγ]; exact hγS
  have hab : valMap (rvMap b) = e RVSort.Γ ⟨valMap (rvMap a), haΓ⟩ := by
    rw [hbγ]
    exact congrArg _ (Subtype.ext haγ.symm)
  set T : Subring (M RVSort.K) := (evalOn F.subtype a).range with hTdef
  have hTmem : ∀ x ∈ T, valMap (rvMap x) ∈ S RVSort.Γ := fun x hx =>
    valMap_adjoin_mem S F d hΓmem haΓ h ⟨x, hx⟩
  have hTcompat : ∀ (x : M RVSort.K) (hx : x ∈ T),
      valMap (rvMap ((ringEmbeddingDataAdjoin F d h.toReflectData).hom ⟨x, hx⟩))
        = e RVSort.Γ ⟨valMap (rvMap x), hTmem x hx⟩ := fun x hx =>
    gamma_adjoinHom S e F d hΓmem hΓ haΓ hab h ⟨x, hx⟩ (hTmem x hx)
  have hFT : ∀ x ∈ F, x ∈ T := fun x hx => mem_evalOn_range_of_mem F a hx
  have hFF' : F ≤ divField T := fun x hx => subset_divField T x (hFT x hx)
  have hmem' : ∀ x ∈ divField T, valMap (rvMap x) ∈ S RVSort.Γ := fun x hx =>
    valMap_divField_mem S hTmem hx
  refine ⟨divField T, hFF', (ringEmbeddingDataAdjoin F d h.toReflectData).toFieldEmbeddingData,
    hmem', fun x hx => ?_, fun x hx => ?_,
    ⟨a, subset_divField T a (self_mem_evalOn_range F a), haγ⟩⟩
  · rw [(ringEmbeddingDataAdjoin F d h.toReflectData).toFieldEmbeddingData_hom_of_mem
      (hFT x hx)]
    exact adjoinHom_of_mem F d h.toReflectData hx
  · exact gamma_divHom S e (ringEmbeddingDataAdjoin F d h.toReflectData) hTmem hTcompat hx
      (hmem' x hx)

end Lift

/-! ### The iteration

`exists_gamma_lift` realizes one value; Zorn's lemma realizes them all. An approximation is a
subfield with its algebraic data and the two invariants, and the upper bound of a chain is the
union — which is again a subfield, because a chain is directed. -/

section Iteration

variable (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N)
variable (F₀ : Subfield (M RVSort.K)) (d₀ : FieldEmbeddingData F₀ N)

/-- **An approximation to the `Γ`-part step.** A subfield containing `F₀`, with the algebraic
data of an embedding extending that of `F₀`, all of whose values lie in the `Γ`-part of `S` and
are the ones `e` prescribes. -/
structure GammaApprox where
  /-- The subfield reached so far. -/
  F : Subfield (M RVSort.K)
  /-- It contains the subfield started from. -/
  hF₀ : F₀ ≤ F
  /-- The algebraic data of the embedding on it. -/
  d : FieldEmbeddingData F N
  /-- Which extends the one started from. -/
  d_ext : ∀ (x : M RVSort.K) (hx : x ∈ F₀), d.hom ⟨x, hF₀ hx⟩ = d₀.hom ⟨x, hx⟩
  /-- Its values lie in the `Γ`-part of `S`. -/
  hmem : ∀ x ∈ F, valMap (rvMap x) ∈ S RVSort.Γ
  /-- And they are the ones `e` prescribes. -/
  hcompat : ∀ (x : M RVSort.K) (hx : x ∈ F),
    valMap (rvMap (d.hom ⟨x, hx⟩)) = e RVSort.Γ ⟨valMap (rvMap x), hmem x hx⟩

namespace GammaApprox

/-- One approximation extends another when its subfield is larger and the homomorphisms agree. -/
instance instPreorder : Preorder (GammaApprox S e F₀ d₀) where
  le A B := A.F ≤ B.F ∧ ∀ (x : M RVSort.K) (hA : x ∈ A.F) (hB : x ∈ B.F),
    B.d.hom ⟨x, hB⟩ = A.d.hom ⟨x, hA⟩
  le_refl _ := ⟨le_refl _, fun _ _ _ => rfl⟩
  le_trans _ _ _ hAB hBC :=
    ⟨hAB.1.trans hBC.1, fun x hA hC => (hBC.2 x (hAB.1 hA) hC).trans (hAB.2 x hA _)⟩

section ChainBound

variable {S e F₀ d₀} (c : Set (GammaApprox S e F₀ d₀)) (hchain : IsChain (· ≤ ·) c)
  (hne : c.Nonempty)

include hchain hne

/-- The subfield reached by a chain of approximations. -/
def chainSubfield : Subfield (M RVSort.K) where
  carrier := {x | ∃ A ∈ c, x ∈ A.F}
  zero_mem' := by
    obtain ⟨A, hA⟩ := id hne
    exact ⟨A, hA, A.F.zero_mem⟩
  one_mem' := by
    obtain ⟨A, hA⟩ := id hne
    exact ⟨A, hA, A.F.one_mem⟩
  neg_mem' := by
    rintro x ⟨A, hA, hxA⟩
    exact ⟨A, hA, A.F.neg_mem hxA⟩
  inv_mem' := by
    rintro x ⟨A, hA, hxA⟩
    exact ⟨A, hA, A.F.inv_mem hxA⟩
  add_mem' := by
    rintro x y ⟨A, hA, hxA⟩ ⟨B, hB, hyB⟩
    obtain ⟨C, hC, hAC, hBC⟩ := hchain.directedOn A hA B hB
    exact ⟨C, hC, C.F.add_mem (hAC.1 hxA) (hBC.1 hyB)⟩
  mul_mem' := by
    rintro x y ⟨A, hA, hxA⟩ ⟨B, hB, hyB⟩
    obtain ⟨C, hC, hAC, hBC⟩ := hchain.directedOn A hA B hB
    exact ⟨C, hC, C.F.mul_mem (hAC.1 hxA) (hBC.1 hyB)⟩

@[simp]
theorem mem_chainSubfield {x : M RVSort.K} :
    x ∈ chainSubfield c hchain hne ↔ ∃ A ∈ c, x ∈ A.F := Iff.rfl

omit hne in
/-- On a chain the homomorphisms agree wherever both are defined. -/
theorem hom_eq_of_chain {A B : GammaApprox S e F₀ d₀} (hA : A ∈ c) (hB : B ∈ c)
    {x : M RVSort.K} (hxA : x ∈ A.F) (hxB : x ∈ B.F) :
    A.d.hom ⟨x, hxA⟩ = B.d.hom ⟨x, hxB⟩ := by
  by_cases hAB : A = B
  · subst hAB
    rfl
  · rcases hchain hA hB hAB with h | h
    · exact (h.2 x hxA hxB).symm
    · exact h.2 x hxB hxA

/-- The glued homomorphism, read off at any member of the chain that contains the point. -/
noncomputable def chainHomFun (x : chainSubfield c hchain hne) : N RVSort.K :=
  (Classical.choose x.2).d.hom ⟨x.1, (Classical.choose_spec x.2).2⟩

theorem chainHomFun_eq {A : GammaApprox S e F₀ d₀} (hA : A ∈ c)
    (x : chainSubfield c hchain hne) (hxA : (x : M RVSort.K) ∈ A.F) :
    chainHomFun c hchain hne x = A.d.hom ⟨x.1, hxA⟩ :=
  hom_eq_of_chain c hchain (Classical.choose_spec x.2).1 hA _ hxA

/-- Two points of the union lie in a common member of the chain. -/
theorem exists_common (x y : chainSubfield c hchain hne) :
    ∃ C ∈ c, ∃ (hx : (x : M RVSort.K) ∈ C.F) (hy : (y : M RVSort.K) ∈ C.F),
      chainHomFun c hchain hne x = C.d.hom ⟨x.1, hx⟩ ∧
        chainHomFun c hchain hne y = C.d.hom ⟨y.1, hy⟩ := by
  obtain ⟨A, hA, hxA⟩ := x.2
  obtain ⟨B, hB, hyB⟩ := y.2
  obtain ⟨C, hC, hAC, hBC⟩ := hchain.directedOn A hA B hB
  exact ⟨C, hC, hAC.1 hxA, hBC.1 hyB, chainHomFun_eq c hchain hne hC x _,
    chainHomFun_eq c hchain hne hC y _⟩

/-- The glued ring homomorphism. -/
noncomputable def chainHom : chainSubfield c hchain hne →+* N RVSort.K where
  toFun := chainHomFun c hchain hne
  map_one' := by
    obtain ⟨A, hA⟩ := id hne
    rw [chainHomFun_eq c hchain hne hA 1 A.F.one_mem]
    exact map_one A.d.hom
  map_zero' := by
    obtain ⟨A, hA⟩ := id hne
    rw [chainHomFun_eq c hchain hne hA 0 A.F.zero_mem]
    exact map_zero A.d.hom
  map_add' x y := by
    obtain ⟨C, hC, hx, hy, hex, hey⟩ := exists_common c hchain hne x y
    rw [hex, hey, chainHomFun_eq c hchain hne hC (x + y) (C.F.add_mem hx hy), ← map_add]
    exact congrArg C.d.hom (Subtype.ext rfl)
  map_mul' x y := by
    obtain ⟨C, hC, hx, hy, hex, hey⟩ := exists_common c hchain hne x y
    rw [hex, hey, chainHomFun_eq c hchain hne hC (x * y) (C.F.mul_mem hx hy), ← map_mul]
    exact congrArg C.d.hom (Subtype.ext rfl)

@[simp]
theorem chainHom_apply (x : chainSubfield c hchain hne) :
    chainHom c hchain hne x = chainHomFun c hchain hne x := rfl

/-- **The upper bound of a chain of approximations.** -/
noncomputable def chainBound : GammaApprox S e F₀ d₀ where
  F := chainSubfield c hchain hne
  hF₀ := by
    obtain ⟨A, hA⟩ := id hne
    exact fun {x} hx => ⟨A, hA, A.hF₀ hx⟩
  d :=
    { hom := chainHom c hchain hne
      rv_iff := by
        intro x y
        obtain ⟨C, hC, hx, hy, hex, hey⟩ := exists_common c hchain hne x y
        rw [chainHom_apply, chainHom_apply, hex, hey]
        exact C.d.rv_iff ⟨x.1, hx⟩ ⟨y.1, hy⟩
      val_iff := by
        intro x y
        obtain ⟨C, hC, hx, hy, hex, hey⟩ := exists_common c hchain hne x y
        rw [chainHom_apply, chainHom_apply, hex, hey]
        exact C.d.val_iff ⟨x.1, hx⟩ ⟨y.1, hy⟩ }
  d_ext x hx := by
    obtain ⟨A, hA⟩ := id hne
    change chainHomFun c hchain hne ⟨x, _⟩ = _
    rw [chainHomFun_eq c hchain hne hA ⟨x, _⟩ (A.hF₀ hx)]
    exact A.d_ext x hx
  hmem := by
    rintro x ⟨A, hA, hxA⟩
    exact A.hmem x hxA
  hcompat x hx := by
    obtain ⟨A, hA, hxA⟩ := id hx
    change valMap (rvMap (chainHomFun c hchain hne ⟨x, hx⟩)) = _
    rw [chainHomFun_eq c hchain hne hA ⟨x, hx⟩ hxA]
    exact A.hcompat x hxA

theorem le_chainBound {A : GammaApprox S e F₀ d₀} (hA : A ∈ c) : A ≤ chainBound c hchain hne := by
  refine ⟨fun {x} hx => ⟨A, hA, hx⟩, fun x hxA hxB => ?_⟩
  exact chainHomFun_eq c hchain hne hA ⟨x, hxB⟩ hxA

end ChainBound

end GammaApprox

end Iteration

/-! ### `RVLift` in full -/

open GammaApprox in
/-- **`RVLift`, in full.** Every `L_RV`-embedding of a substructure of a model of `ACVFTheory`
extends to an embedding of a **field-like** substructure containing it — and the target is `N`
itself, no elementary extension of it being needed anywhere in `RVLift`.

The iteration (`exists_fieldEmbeddingData_of_substructure`) produces a subfield `F₀` whose
leading terms are exactly the `RV`-part of `S`. The `Γ`-part step is Zorn's lemma on
`GammaApprox` above it: a maximal approximation realizes every value of the `Γ`-part, because
otherwise `exists_gamma_lift` would enlarge it. -/
theorem RVLift_full (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N) :
    ∃ (F : Subfield (M RVSort.K)) (hsub : S ≤ fieldSubstructure M F)
      (h : (fun s => ↥(fieldSubstructure M F s)) ↪[rvLang] N),
      ∀ (s : RVSort) (a : S s),
        h s (Substructure.inclusion hsub s a) = e s a := by
  classical
  obtain ⟨F₀, d₀, hF₀S, hF₀rv, hsurj, hextK, hextRV, hextΓ⟩ :=
    exists_fieldEmbeddingData_of_substructure S e
  have hmem₀ : ∀ x ∈ F₀, valMap (rvMap x) ∈ S RVSort.Γ := fun x hx =>
    valMap_mem_Gamma (hF₀rv x hx)
  have : Nonempty (GammaApprox S e F₀ d₀) :=
    ⟨⟨F₀, le_refl _, d₀, fun _ _ => rfl, hmem₀, fun x hx => hextΓ x hx (hmem₀ x hx)⟩⟩
  obtain ⟨m, hm⟩ := zorn_le_nonempty (α := GammaApprox S e F₀ d₀)
    (fun c hchain hne => ⟨chainBound c hchain hne,
      fun _ hA => le_chainBound c hchain hne hA⟩)
  -- maximality realizes every value of the `Γ`-part
  have hγsurj : ∀ γ ∈ S RVSort.Γ, ∃ x ∈ m.F, valMap (rvMap x) = γ := by
    intro γ hγ
    by_contra hcon
    push Not at hcon
    obtain ⟨F', hFF', d', hmem', hext', hcompat', x, hxF', hxγ⟩ :=
      exists_gamma_lift S e m.F m.d m.hmem m.hcompat hγ hcon
    have hmB : m ≤ (⟨F', m.hF₀.trans hFF', d',
        fun y hy => (hext' y (m.hF₀ hy)).trans (m.d_ext y hy), hmem', hcompat'⟩ :
          GammaApprox S e F₀ d₀) :=
      ⟨hFF', fun y hA _ => hext' y hA⟩
    exact hcon x ((hm hmB).1 hxF') hxγ
  -- and so `S` sits inside the field-like substructure of `m.F`
  have hsub : S ≤ fieldSubstructure M m.F := by
    intro s x hx
    match s with
    | RVSort.K => exact m.hF₀ (hF₀S x hx)
    | RVSort.RV =>
      obtain ⟨y, hy, hyx⟩ := hsurj x hx
      exact ⟨y, m.hF₀ hy, hyx⟩
    | RVSort.Γ => exact hγsurj x hx
  refine ⟨m.F, hsub, m.d.toEmbedding, fun s a => ?_⟩
  match s with
  | RVSort.K => exact (m.d_ext a.1 (hF₀S a.1 a.2)).trans (hextK a.1 a.2 (hF₀S a.1 a.2))
  | RVSort.RV =>
    obtain ⟨y, hy, hya⟩ := hsurj a.1 a.2
    have hrv : rvMap y ∈ S RVSort.RV := by rw [hya]; exact a.2
    have hcast : Substructure.inclusion hsub RVSort.RV a
        = ⟨rvMap y, ⟨y, m.hF₀ hy, rfl⟩⟩ := Subtype.ext hya.symm
    change m.d.rvComp _ = _
    rw [hcast, m.d.rvComp_apply (m.hF₀ hy) ⟨y, m.hF₀ hy, rfl⟩, m.d_ext y hy, hextRV y hy hrv]
    exact congrArg _ (Subtype.ext hya)
  | RVSort.Γ =>
    obtain ⟨y, hy, hyγ⟩ := hγsurj a.1 a.2
    have hcast : Substructure.inclusion hsub RVSort.Γ a
        = ⟨valMap (rvMap y), ⟨y, hy, rfl⟩⟩ := Subtype.ext hyγ.symm
    change m.d.gammaComp _ = _
    rw [hcast, m.d.gammaComp_apply hy ⟨y, hy, rfl⟩, m.hcompat y hy]
    exact congrArg _ (Subtype.ext hyγ)

/-- **`RVLift` holds** — steps `res(K(C)) = k(C)` and `v(K(C)) = Γ(C)` of Rideau-Kikuchi's
Proposition 2.1.10, in the form `ACVF_hasQERelTo_empty_of_lift_step` consumes them. Together with
`FieldStep`, this gives quantifier elimination for `ACVF` in `L_RV`: see `ACVF_hasQERelTo_empty`
in `Algebra/ACVF/QE.lean`. -/
theorem RVLift_holds : RVLift := by
  intro M N _ _ _ _ _ _ S e
  obtain ⟨F, hsub, h, hcomm⟩ := RVLift_full S e
  exact ⟨N, inferInstance, inferInstance, ElementaryEmbedding.refl rvLang N, F, hsub, h, hcomm⟩

end ManySorted.Language
