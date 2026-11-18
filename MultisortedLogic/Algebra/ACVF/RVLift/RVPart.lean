/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/

module

public import MultisortedLogic.Algebra.ACVF.RVLift.Routing

/-!
# Lifting the `RV`-part to the field sort: the iteration

`Algebra/ACVF/RVLift/Routing.lean` grows the field part of a substructure by one element whenever
its `RV`-part is not exhausted by the leading terms of that field part. This file iterates that, by
Zorn's lemma: **the field part of `S` grows to a subfield `F` whose leading terms are exactly the
`RV`-part of `S`, and the embedding extends to the field-like substructure of `F`**, with no
elementary extension of the target (`exists_fieldEmbeddingData_of_substructure`). The values of
`S` that are not values of its `RV`-part are left to the `Γ`-part step,
`Algebra/ACVF/RVLift/GammaPart.lean`.

## The shape of an approximation

`adjoinSubstructure` and `adjoinEmbedding` (`Algebra/ACVF/Substructure/FieldLike.lean`) say that a
substructure with the `RV`- and `Γ`-parts of `S` and a *larger field part* is nothing more than a
subring `T` of the field sort with `rv T ⊆ S RV`, and that an `L_RV`-embedding of it is nothing more
than a ring homomorphism `T →+* N K` compatible with `e` through `rv`. So the partially ordered set
to run Zorn's lemma on is a set of pairs `(T, φ)` of that kind — `LiftApprox` — and the upper bound
of a chain only has to glue **ring homomorphisms**, not `L_RV`-embeddings. The many-sorted plumbing
is done once, in `adjoinEmbedding`, and never again.

A maximal approximation is a subfield: otherwise the fraction-field step (`fracEmbedding`)
would enlarge it. And its leading terms exhaust `S RV`: otherwise the routing would enlarge it.
Those two facts are what `exists_fieldEmbeddingData_of_substructure` puts together.

## Main definitions

* `Language.LiftApprox` : an approximation, with its preorder.
* `Language.LiftApprox.base`, `Language.LiftApprox.ofSubstructure`,
  `Language.LiftApprox.chainBound`.

## Main statements

* `Language.exists_fieldEmbeddingData_of_substructure` : a subfield whose leading terms are exactly
  the `RV`-part of `S`, with the algebraic data of an embedding of its field-like substructure
  extending `e`.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring Polynomial

universe w

variable {M : RVSort → Type w} [rvLang.Structure M] [M ⊨ ACVFTheory]
variable {N : RVSort → Type w} [rvLang.Structure N] [N ⊨ ACVFTheory]
variable (S : rvLang.Substructure M) (e : (fun s => ↥(S s)) ↪[rvLang] N)

/-! ### Approximations -/

/-- **An approximation to the lift.** A subring `T` of the field sort containing the field part of
`S`, all of whose leading terms are already in the `RV`-part of `S`, together with an injective
ring homomorphism into the target that is compatible with `e` through `rv` and extends it on the
field part of `S`.

By `adjoinSubstructure` and `adjoinEmbedding` this is the same thing as a substructure with the
`RV`- and `Γ`-parts of `S` and a larger field part, together with an `L_RV`-embedding of it
extending `e`. -/
structure LiftApprox where
  /-- The subring of the field sort reached so far. -/
  T : Subring (M RVSort.K)
  /-- It contains the field part of `S`. -/
  hTS : ∀ x ∈ S RVSort.K, x ∈ T
  /-- Its leading terms are already in the `RV`-part of `S`. -/
  hT : ∀ x ∈ T, rvMap x ∈ S RVSort.RV
  /-- The ring homomorphism into the target. -/
  hom : T →+* N RVSort.K
  /-- It is injective. -/
  hom_inj : Function.Injective hom
  /-- It is compatible with `e` through `rv`. -/
  hom_rv : ∀ x : T, e RVSort.RV ⟨rvMap (x : M RVSort.K), hT _ x.2⟩ = rvMap (hom x)
  /-- And it extends `e` on the field part of `S`. -/
  hom_ext : ∀ (x : M RVSort.K) (hx : x ∈ S RVSort.K),
    hom ⟨x, hTS x hx⟩ = e RVSort.K ⟨x, hx⟩

namespace LiftApprox

/-- One approximation extends another when its subring is larger and the homomorphisms agree. -/
instance instPreorder : Preorder (LiftApprox S e) where
  le A B := A.T ≤ B.T ∧ ∀ (x : M RVSort.K) (hA : x ∈ A.T) (hB : x ∈ B.T),
    B.hom ⟨x, hB⟩ = A.hom ⟨x, hA⟩
  le_refl _ := ⟨le_refl _, fun _ _ _ => rfl⟩
  le_trans _ _ _ hAB hBC :=
    ⟨hAB.1.trans hBC.1, fun x hA hC => (hBC.2 x (hAB.1 hA) hC).trans (hAB.2 x hA _)⟩

/-- The approximation one starts from: the field part of `S` itself. -/
def base : LiftApprox S e where
  T := subringOfSubstructure S
  hTS _ hx := hx
  hT _ hx := rvMap_mem_RV hx
  hom := subHom S e
  hom_inj := subHom_injective S e
  hom_rv x := e_rvMap S e x.2 (rvMap_mem_RV x.2)
  hom_ext _ _ := rfl

instance instNonempty : Nonempty (LiftApprox S e) := ⟨base S e⟩

/-- **An approximation read off a substructure.** Any substructure with the `RV`-part of `S` and a
larger field part, with an embedding extending `e`, is an approximation. This is how the output of
the fraction-field step and of the routing is fed back into the iteration. -/
def ofSubstructure (S' : rvLang.Substructure M) (e' : (fun s => ↥(S' s)) ↪[rvLang] N)
    (hle : S ≤ S')
    (hRV : S' RVSort.RV = S RVSort.RV)
    (hext : ∀ (s : RVSort) (x : M s) (hx : x ∈ S s)
      (hx' : x ∈ S' s), e' s ⟨x, hx'⟩ = e s ⟨x, hx⟩) :
    LiftApprox S e where
  T := subringOfSubstructure S'
  hTS _ hx := hle RVSort.K hx
  hT _ hx := hRV ▸ rvMap_mem_RV hx
  hom := subHom S' e'
  hom_inj := subHom_injective S' e'
  hom_rv x := by
    rw [← e_rvMap S' e' x.2 (rvMap_mem_RV x.2)]
    exact (hext RVSort.RV _ (hRV ▸ rvMap_mem_RV x.2) (rvMap_mem_RV x.2)).symm
  hom_ext x hx := hext RVSort.K x hx _

/-! ### The upper bound of a chain

Because an approximation carries a *ring* homomorphism, the upper bound of a chain only has to
glue ring homomorphisms: any two elements of the union lie in a common member of the chain, and
there the two homomorphisms agree. -/

section ChainBound

variable {S e} (c : Set (LiftApprox S e)) (hchain : IsChain (· ≤ ·) c) (hne : c.Nonempty)

include hchain hne

/-- The subring reached by a chain of approximations. -/
def chainSubring : Subring (M RVSort.K) where
  carrier := {x | ∃ A ∈ c, x ∈ A.T}
  zero_mem' := by
    obtain ⟨A, hA⟩ := id hne
    exact ⟨A, hA, A.T.zero_mem⟩
  one_mem' := by
    obtain ⟨A, hA⟩ := id hne
    exact ⟨A, hA, A.T.one_mem⟩
  neg_mem' := by
    intro x hx
    obtain ⟨A, hA, hxA⟩ := hx
    exact ⟨A, hA, A.T.neg_mem hxA⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨A, hA, hxA⟩ := hx
    obtain ⟨B, hB, hyB⟩ := hy
    obtain ⟨C, hC, hAC, hBC⟩ := hchain.directedOn A hA B hB
    exact ⟨C, hC, C.T.add_mem (hAC.1 hxA) (hBC.1 hyB)⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨A, hA, hxA⟩ := hx
    obtain ⟨B, hB, hyB⟩ := hy
    obtain ⟨C, hC, hAC, hBC⟩ := hchain.directedOn A hA B hB
    exact ⟨C, hC, C.T.mul_mem (hAC.1 hxA) (hBC.1 hyB)⟩

@[simp]
theorem mem_chainSubring {x : M RVSort.K} :
    x ∈ chainSubring c hchain hne ↔ ∃ A ∈ c, x ∈ A.T := Iff.rfl

omit hne in
/-- On a chain the homomorphisms agree wherever both are defined. -/
theorem hom_eq_of_chain {A B : LiftApprox S e} (hA : A ∈ c) (hB : B ∈ c) {x : M RVSort.K}
    (hxA : x ∈ A.T) (hxB : x ∈ B.T) : A.hom ⟨x, hxA⟩ = B.hom ⟨x, hxB⟩ := by
  by_cases hAB : A = B
  · subst hAB
    rfl
  · rcases hchain hA hB hAB with h | h
    · exact (h.2 x hxA hxB).symm
    · exact h.2 x hxB hxA

/-- The glued homomorphism, read off at any member of the chain that contains the point. -/
noncomputable def chainHomFun (x : chainSubring c hchain hne) : N RVSort.K :=
  (Classical.choose x.2).hom ⟨x.1, (Classical.choose_spec x.2).2⟩

theorem chainHomFun_eq {A : LiftApprox S e} (hA : A ∈ c) (x : chainSubring c hchain hne)
    (hxA : (x : M RVSort.K) ∈ A.T) : chainHomFun c hchain hne x = A.hom ⟨x.1, hxA⟩ :=
  hom_eq_of_chain c hchain (Classical.choose_spec x.2).1 hA _ hxA

/-- The glued ring homomorphism. -/
noncomputable def chainHom : chainSubring c hchain hne →+* N RVSort.K where
  toFun := chainHomFun c hchain hne
  map_one' := by
    obtain ⟨A, hA⟩ := id hne
    rw [chainHomFun_eq c hchain hne hA 1 A.T.one_mem]
    exact map_one A.hom
  map_zero' := by
    obtain ⟨A, hA⟩ := id hne
    rw [chainHomFun_eq c hchain hne hA 0 A.T.zero_mem]
    exact map_zero A.hom
  map_add' x y := by
    obtain ⟨A, hA, hxA⟩ := x.2
    obtain ⟨B, hB, hyB⟩ := y.2
    obtain ⟨C, hC, hAC, hBC⟩ := hchain.directedOn A hA B hB
    have hx : (x : M RVSort.K) ∈ C.T := hAC.1 hxA
    have hy : (y : M RVSort.K) ∈ C.T := hBC.1 hyB
    rw [chainHomFun_eq c hchain hne hC x hx, chainHomFun_eq c hchain hne hC y hy,
      chainHomFun_eq c hchain hne hC (x + y) (C.T.add_mem hx hy), ← map_add]
    exact congrArg C.hom (Subtype.ext rfl)
  map_mul' x y := by
    obtain ⟨A, hA, hxA⟩ := x.2
    obtain ⟨B, hB, hyB⟩ := y.2
    obtain ⟨C, hC, hAC, hBC⟩ := hchain.directedOn A hA B hB
    have hx : (x : M RVSort.K) ∈ C.T := hAC.1 hxA
    have hy : (y : M RVSort.K) ∈ C.T := hBC.1 hyB
    rw [chainHomFun_eq c hchain hne hC x hx, chainHomFun_eq c hchain hne hC y hy,
      chainHomFun_eq c hchain hne hC (x * y) (C.T.mul_mem hx hy), ← map_mul]
    exact congrArg C.hom (Subtype.ext rfl)

@[simp]
theorem chainHom_apply (x : chainSubring c hchain hne) :
    chainHom c hchain hne x = chainHomFun c hchain hne x := rfl

/-- **The upper bound of a chain of approximations.** -/
noncomputable def chainBound : LiftApprox S e where
  T := chainSubring c hchain hne
  hTS x hx := by
    obtain ⟨A, hA⟩ := id hne
    exact ⟨A, hA, A.hTS x hx⟩
  hT x hx := by
    obtain ⟨A, hA, hxA⟩ := hx
    exact A.hT x hxA
  hom := chainHom c hchain hne
  hom_inj := by
    intro x y hxy
    obtain ⟨A, hA, hxA⟩ := x.2
    obtain ⟨B, hB, hyB⟩ := y.2
    obtain ⟨C, hC, hAC, hBC⟩ := hchain.directedOn A hA B hB
    have hx : (x : M RVSort.K) ∈ C.T := hAC.1 hxA
    have hy : (y : M RVSort.K) ∈ C.T := hBC.1 hyB
    rw [chainHom_apply, chainHom_apply, chainHomFun_eq c hchain hne hC x hx,
      chainHomFun_eq c hchain hne hC y hy] at hxy
    have h1 : (⟨(x : M RVSort.K), hx⟩ : C.T) = ⟨(y : M RVSort.K), hy⟩ := C.hom_inj hxy
    exact Subtype.ext (congrArg (fun z : C.T => (z : M RVSort.K)) h1)
  hom_rv x := by
    obtain ⟨A, hA, hxA⟩ := x.2
    rw [chainHom_apply, chainHomFun_eq c hchain hne hA x hxA]
    exact A.hom_rv ⟨x.1, hxA⟩
  hom_ext x hx := by
    obtain ⟨A, hA⟩ := id hne
    rw [chainHom_apply, chainHomFun_eq c hchain hne hA ⟨x, _⟩ (A.hTS x hx)]
    exact A.hom_ext x hx

theorem le_chainBound {A : LiftApprox S e} (hA : A ∈ c) : A ≤ chainBound c hchain hne := by
  refine ⟨fun {x} hx => ⟨A, hA, hx⟩, fun x hxA hxB => ?_⟩
  exact chainHomFun_eq c hchain hne hA ⟨x, hxB⟩ hxA

end ChainBound

/-! ### An approximation as a substructure -/

section ToSubstructure

variable {S e}

/-- The substructure an approximation describes: the field part grown, the other two sorts
those of `S`. -/
noncomputable def toSubstructure (A : LiftApprox S e) : rvLang.Substructure M :=
  adjoinSubstructure S A.T A.hTS A.hT

/-- And the `L_RV`-embedding of it that the approximation's ring homomorphism gives. -/
noncomputable def toEmb (A : LiftApprox S e) : (fun s => ↥(A.toSubstructure s)) ↪[rvLang] N :=
  adjoinEmbedding S A.hTS A.hT e A.hom A.hom_inj A.hom_rv

theorem le_toSubstructure (A : LiftApprox S e) :
    S ≤ A.toSubstructure := by
  intro s x hx
  match s with
  | RVSort.K => exact A.hTS x hx
  | RVSort.RV => exact hx
  | RVSort.Γ => exact hx

theorem toEmb_ext (A : LiftApprox S e) (s : RVSort) (x : M s)
    (hx : x ∈ S s) (hx' : x ∈ A.toSubstructure s) :
    A.toEmb s ⟨x, hx'⟩ = e s ⟨x, hx⟩ := by
  match s with
  | RVSort.K => exact A.hom_ext x hx
  | RVSort.RV => rfl
  | RVSort.Γ => rfl

/-! ### Closing an approximation under inversion -/

/-- The fraction-field step, as a step of the iteration. -/
noncomputable def fracApprox (A : LiftApprox S e) : LiftApprox S e :=
  ofSubstructure S e (fracAdjoin A.toSubstructure) (fracEmbedding A.toSubstructure A.toEmb)
    (by
      refine A.le_toSubstructure.trans fun s x hx => ?_
      match s with
      | RVSort.K => exact subset_fracIncl_range A.toSubstructure x hx
      | RVSort.RV => exact hx
      | RVSort.Γ => exact hx)
    rfl
    (by
      intro s x hx hx'
      match s with
      | RVSort.K =>
        rw [fracEmbedding_apply_K A.toSubstructure A.toEmb (A.hTS x hx) hx']
        exact A.toEmb_ext RVSort.K x hx (A.hTS x hx)
      | RVSort.RV => exact A.toEmb_ext RVSort.RV x hx hx
      | RVSort.Γ => exact A.toEmb_ext RVSort.Γ x hx hx)

theorem le_fracApprox (A : LiftApprox S e) : A ≤ A.fracApprox := by
  refine ⟨fun {x} hx => subset_fracIncl_range A.toSubstructure x hx, fun x hxA hxB => ?_⟩
  change subHom (fracAdjoin A.toSubstructure) (fracEmbedding A.toSubstructure A.toEmb) ⟨x, hxB⟩
    = A.hom ⟨x, hxA⟩
  rw [subHom_apply, fracEmbedding_apply_K A.toSubstructure A.toEmb hxA hxB]
  rfl

theorem inv_mem_fracApprox (A : LiftApprox S e) {x : M RVSort.K} (hx : x ∈ A.T) :
    x⁻¹ ∈ A.fracApprox.T :=
  (mem_fracIncl_range_iff A.toSubstructure).mpr
    ⟨1, (subringOfSubstructure A.toSubstructure).one_mem, x, hx, one_div x⟩

/-! ### Growing an approximation whose leading terms are not yet everything -/

/-- **The routing, as a step of the iteration.** -/
theorem exists_gt_of_notMem (A : LiftApprox S e) (hinv : ∀ x ∈ A.T, x⁻¹ ∈ A.T)
    {ξ : M RVSort.RV} (hξ : ξ ∈ S RVSort.RV)
    (hξF : ∀ x ∈ A.T, rvMap x ≠ ξ) :
    ∃ B : LiftApprox S e, A ≤ B ∧ ∃ x ∈ B.T, x ∉ A.T := by
  obtain ⟨x₀, hx₀F, S'', e'', hsub'', hmem'', hRV'', hΓ'', hext''⟩ :=
    exists_lift_of_notMem (Subring.toSubfield A.T hinv) A.toSubstructure A.toEmb
      (fun _ hx => hx) (fun _ hx => hx) hξ hξF
  have hextS : ∀ (s : RVSort) (x : M s) (hx : x ∈ S s)
      (hx' : x ∈ S'' s), e'' s ⟨x, hx'⟩ = e s ⟨x, hx⟩ := by
    intro s x hx hx'
    rw [hext'' s x (A.le_toSubstructure s hx) hx']
    exact A.toEmb_ext s x hx _
  refine ⟨ofSubstructure S e S'' e'' ((A.le_toSubstructure).trans hsub'') hRV'' hextS,
    ⟨fun {x} hx => hsub'' RVSort.K hx, fun x hxA hxB => ?_⟩, ?_⟩
  · change subHom S'' e'' ⟨x, hxB⟩ = A.hom ⟨x, hxA⟩
    rw [subHom_apply, hext'' RVSort.K x hxA hxB]
    rfl
  · exact ⟨x₀, hmem'', hx₀F⟩

end ToSubstructure

end LiftApprox

open Arity LiftApprox

/-! ### The assembly -/

/-- **The iteration, in algebraic form.** Zorn's lemma on `LiftApprox` produces a subfield of the
field sort containing the field part of `S`, whose leading terms are *exactly* the `RV`-part of
`S`, together with the algebraic data of an embedding of the field-like substructure it carries,
agreeing with `e` on all three sorts wherever `e` is defined.

The `Γ`-part is not brought down here: this says nothing about the values of `S` that are not values
of the `RV`-part. That is the `Γ`-part step, done in `Algebra/ACVF/RVLift/GammaPart.lean` on top of
this. -/
theorem exists_fieldEmbeddingData_of_substructure :
    ∃ (F : Subfield (M RVSort.K)) (d : FieldEmbeddingData F N),
      (∀ x ∈ S RVSort.K, x ∈ F) ∧
      (∀ x ∈ F, rvMap x ∈ S RVSort.RV) ∧
      (∀ ξ ∈ S RVSort.RV, ∃ x ∈ F, rvMap x = ξ) ∧
      (∀ (x : M RVSort.K) (hx : x ∈ S RVSort.K) (hx' : x ∈ F),
        d.hom ⟨x, hx'⟩ = e RVSort.K ⟨x, hx⟩) ∧
      (∀ (x : M RVSort.K) (hx : x ∈ F) (hrv : rvMap x ∈ S RVSort.RV),
        rvMap (d.hom ⟨x, hx⟩) = e RVSort.RV ⟨rvMap x, hrv⟩) ∧
      (∀ (x : M RVSort.K) (hx : x ∈ F) (hγ : valMap (rvMap x) ∈ S RVSort.Γ),
        valMap (rvMap (d.hom ⟨x, hx⟩)) = e RVSort.Γ ⟨valMap (rvMap x), hγ⟩) := by
  classical
  obtain ⟨m, hm⟩ := zorn_le_nonempty (α := LiftApprox S e)
    (fun c hchain hne => ⟨chainBound c hchain hne, fun _ hA => le_chainBound c hchain hne hA⟩)
  -- maximality closes the approximation under inversion
  have hinv : ∀ x ∈ m.T, x⁻¹ ∈ m.T := fun _ hx =>
    (hm (le_fracApprox m)).1 (inv_mem_fracApprox m hx)
  -- and makes its leading terms exhaust the `RV`-part
  have hsurj : ∀ ξ ∈ S RVSort.RV, ∃ x ∈ m.T, rvMap x = ξ := by
    intro ξ hξ
    by_contra hc
    push Not at hc
    obtain ⟨B, hmB, x, hxB, hxm⟩ := exists_gt_of_notMem m hinv hξ hc
    exact hxm ((hm hmB).1 hxB)
  set F : Subfield (M RVSort.K) := Subring.toSubfield m.T hinv with hFdef
  set φ : F →+* N RVSort.K :=
    { toFun := fun x => m.hom ⟨x.1, x.2⟩
      map_one' := map_one m.hom
      map_zero' := map_zero m.hom
      map_add' := fun _ _ => map_add m.hom _ _
      map_mul' := fun _ _ => map_mul m.hom _ _ } with hφdef
  have hrvφ : ∀ x : F, rvMap (φ x) = embRV S e (rvMap (x : M RVSort.K)) := by
    intro x
    rw [embRV_apply S e (m.hT _ x.2)]
    exact (m.hom_rv ⟨x.1, x.2⟩).symm
  refine ⟨F,
    { hom := φ
      rv_iff := by
        intro x y
        rw [hrvφ, hrvφ]
        exact ⟨fun h => congrArg _ h,
          fun h => embRV_inj S e (m.hT _ x.2) (m.hT _ y.2) h⟩
      val_iff := by
        intro x y
        rw [hrvφ, hrvφ]
        exact (valMap_embRV_le_iff S e (m.hT _ x.2) (m.hT _ y.2)).symm },
    fun x hx => m.hTS x hx, fun x hx => m.hT x hx, hsurj,
    fun x hx _ => m.hom_ext x hx, fun x hx hrv => ?_, fun x hx hγ => ?_⟩
  · change rvMap (φ ⟨x, hx⟩) = _
    rw [hrvφ, embRV_apply S e hrv]
  · change valMap (rvMap (φ ⟨x, hx⟩)) = _
    rw [hrvφ, valMap_embRV S e (m.hT x hx)]

end ManySorted.Language
