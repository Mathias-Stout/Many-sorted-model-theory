/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathias Stout
-/
module

public import MultisortedLogic.Algebra.DOAG.AffineTransfer
public import MultisortedLogic.Algebra.DOAG.Basic
public import MultisortedLogic.Separation
public import MultisortedLogic.RealizingTypes
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Quantifier elimination for divisible ordered abelian groups

Quantifier elimination for the one-sorted theory `DOAG` of nontrivial divisible ordered abelian
groups in the language of ordered abelian groups. The theory itself, and the correspondence between
its models and nontrivial divisible ordered abelian groups, are in `Algebra/DOAG/Basic.lean`.

## Main results

* `oag_qfMap_iff_orderedGroupHom`: the maps that preserve and reflect the quantifier-free formulas
  between ordered abelian groups are the injective additive maps that reflect the order.
* `DOAG_hasQERelTo_empty`: the one-sorted theory of nontrivial divisible ordered abelian groups
  eliminates quantifiers.

## Implementation notes

Quantifier elimination goes through the pointed tuple-extension criterion
`Theory.hasQERelTo_of_pointed_extension`. For tuples `x` in `M` and `y` in `N` with the same
quantifier-free type, the values at `x` of the terms form a subgroup `A` of `M`, and `u(x) ↦ u(y)`
is an order-reflecting additive map `ψ : A →+ N` (`doag_span_hom`). Given `b` in `M`, either some
nonzero multiple of `b` lies in `A`, and dividing in `N` gives a counterpart of `b`, or `b` cuts
`A`. The cut is then a type over `y`, finitely satisfiable in `N` by `exists_affine_cut_bounds`, and
it is realized next to a tuple with the same complete type as `y`
(`Formula.exists_realize_of_finite`). In both cases, `doag_qf_transfer_of_key` turns the transfer
of the affine inequalities `k • b ⋚ u(x)` into an equality of quantifier-free types, since the terms
are linear forms (`Term.exists_realize_eq_add_zsmul`).
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

universe w w' z

variable {S : Type z}

/-- **Embeddings are the quantifier-free maps**: between structures for `Language.oag s` on
ordered abelian groups, the families of maps that preserve and reflect the formulas
quantifier-free relative to no sorts are the injective ones that are additive and reflect the
order on `s`. -/
theorem oag_qfMap_iff_orderedGroupHom {s : S} {M : S → Type w} {N : S → Type w'}
    [(Language.oag s).Structure M] [(Language.oag s).Structure N] [AddCommGroup (M s)]
    [AddCommGroup (N s)] [LE (M s)] [LE (N s)] [CompatibleOAGroupL (Language.oag s) M s]
    [CompatibleOAGroupL (Language.oag s) N s] (f : ∀ s', M s' → N s') :
    (∀ {σ : Arity S} (φ : (Language.oag s).Formula σ), φ.IsQFRelTo ∅ → ∀ x : M [^] σ,
      (φ.Realize (x.map f) ↔ φ.Realize x)) ↔
    (∀ s', Function.Injective (f s')) ∧ (∀ a b : M s, f s (a + b) = f s a + f s b) ∧
      ∀ a b : M s, f s a ≤ f s b ↔ a ≤ b := by
  rw [← oag_embedding_iff]
  constructor
  · intro h
    exact ⟨(⟨f, fun φ hφ x hx => (h φ hφ x).2 hx⟩ :
      M →[FormulaClass.qfRelTo (Language.oag s) ∅]ᶠ N).toEmbedding, rfl⟩
  · rintro ⟨e, rfl⟩ σ φ hφ x
    exact e.realize_of_isQFRelTo_empty hφ x

/-! ### Quantifier elimination for DOAG -/

section DOAGQE

/-- The language of ordered abelian groups on the one-point sort type. -/
abbrev oagU : Language.{0, 0} Unit := Language.oag ()

/-- The one-sorted theory of nontrivial divisible ordered abelian groups. -/
abbrev DOAG : oagU.Theory := DOAGTheory oagU ()

/-- **Homomorphisms of ordered abelian groups**: between one-sorted structures for the language
of ordered abelian groups on ordered abelian groups, the homomorphisms of structures are the
monotone additive maps. -/
def oagHomEquivOrderAddMonoidHom (M N : Unit → Type*) [oagU.Structure M] [oagU.Structure N]
    [AddCommGroup (M ())] [AddCommGroup (N ())] [Preorder (M ())] [Preorder (N ())]
    [CompatibleOAGroupL oagU M ()] [CompatibleOAGroupL oagU N ()] :
    (M →[oagU] N) ≃ (M () →+o N ()) where
  toFun f :=
    { toFun := f ()
      map_zero' := by
        simpa using HomClass.map_fun (L := oagU) (M := M) (N := N) f oagFunc.zero PUnit.unit
      map_add' a b := by
        simpa using HomClass.map_fun (L := oagU) (M := M) (N := N) f oagFunc.add
          ((a, b) : M [^] (⦃()⦄ ⨯ ⦃()⦄))
      monotone' a b hab := by
        simpa using HomClass.map_rel (L := oagU) (M := M) (N := N) f oagRel.le
          ((a, b) : M [^] (⦃()⦄ ⨯ ⦃()⦄)) (by simpa using hab) }
  invFun g :=
    { toFun := fun _ => g
      map_fun' := by
        rintro σ t (_ | _ | _) x <;> simp
      map_rel' := by
        rintro σ ⟨⟩ x h
        simp only [oagRel.relMap_le_iff] at h ⊢
        simpa using g.monotone' h }
  left_inv _ := rfl
  right_inv _ := rfl

section Transfer

variable {M N : Unit → Type w} [oagU.Structure M] [oagU.Structure N]
  [AddCommGroup (M ())] [LinearOrder (M ())] [IsOrderedAddMonoid (M ())]
  [CompatibleOAGroupL oagU M ()] [AddCommGroup (N ())] [LinearOrder (N ())]
  [IsOrderedAddMonoid (N ())] [CompatibleOAGroupL oagU N ()] {σ : Arity Unit}

/-- **The quantifier-free transfer step**: if the affine inequalities `k • b ⋚ u(x)` and
`k • c ⋚ u(y)` agree for all integers `k` and all terms `u` in the variables of `σ`, then `(x, b)`
and `(y, c)` have the same quantifier-free type. The atomic formulas compare values of terms, and
the value of a term at `(x, b)` is `u(x) + k • b` (`Term.exists_realize_eq_add_zsmul`). -/
theorem doag_qf_transfer_of_key (x : M [^] σ) (y : N [^] σ) (b : M ()) (c : N ())
    (key : ∀ (k : ℤ) (u : oagU.Term σ ⦃()⦄),
      (k • b ≤ u.realize x ↔ k • c ≤ u.realize y) ∧ (u.realize x ≤ k • b ↔ u.realize y ≤ k • c)) :
    Formula.typeOf (FormulaClass.qfRelTo oagU ∅ (σ ⨯ ⦃()⦄)) ((x, b) : M [^] (σ ⨯ ⦃()⦄)) =
      Formula.typeOf (FormulaClass.qfRelTo oagU ∅ (σ ⨯ ⦃()⦄)) ((y, c) : N [^] (σ ⨯ ⦃()⦄)) := by
  have hle : ∀ t₁ t₂ : oagU.Term (σ ⨯ ⦃()⦄) ⦃()⦄,
      t₁.realize ((x, b) : M [^] (σ ⨯ ⦃()⦄)) ≤ t₂.realize ((x, b) : M [^] (σ ⨯ ⦃()⦄)) ↔
        t₁.realize ((y, c) : N [^] (σ ⨯ ⦃()⦄)) ≤ t₂.realize ((y, c) : N [^] (σ ⨯ ⦃()⦄)) := by
    intro t₁ t₂
    obtain ⟨u₁, k₁, h₁⟩ := t₁.exists_realize_eq_add_zsmul
    obtain ⟨u₂, k₂, h₂⟩ := t₂.exists_realize_eq_add_zsmul
    rw [h₁ M x b, h₂ M x b, h₁ N y c, h₂ N y c, add_zsmul_le_add_zsmul_iff,
      add_zsmul_le_add_zsmul_iff]
    have h := (key (k₁ - k₂) (u₂ +ₗ -ₗu₁)).1
    simp only [Term.realize_func, Term.realize_prod, CompatibleAddL.funMap_add,
      CompatibleNegL.funMap_neg] at h
    rwa [← sub_eq_add_neg, ← sub_eq_add_neg] at h
  have heq : ∀ t₁ t₂ : oagU.Term (σ ⨯ ⦃()⦄) ⦃()⦄,
      t₁.realize ((x, b) : M [^] (σ ⨯ ⦃()⦄)) = t₂.realize ((x, b) : M [^] (σ ⨯ ⦃()⦄)) ↔
        t₁.realize ((y, c) : N [^] (σ ⨯ ⦃()⦄)) = t₂.realize ((y, c) : N [^] (σ ⨯ ⦃()⦄)) := by
    intro t₁ t₂
    rw [le_antisymm_iff, le_antisymm_iff]
    exact and_congr (hle t₁ t₂) (hle t₂ t₁)
  refine Formula.typeOf_eq_typeOf_iff.2 fun φ hφ =>
    Formula.realize_iff_of_isQFRelTo_empty hφ _ _ fun ψ hψ => ?_
  cases hψ with
  | equal t₁ t₂ =>
    simp only [Formula.realize_equal, Interpret.ext_iff, ← Term.realize_get]
    refine forall_congr' fun s => forall_congr' fun i => ?_
    cases s
    exact heq _ _
  | rel r ts =>
    cases r
    cases ts with
    | prod t₁ t₂ => simpa using hle t₁ t₂

omit [IsOrderedAddMonoid (M ())] [IsOrderedAddMonoid (N ())] in
/-- **The span of a tuple, with its induced map**: for tuples `x` and `y` with the same
quantifier-free type, `u(x) ↦ u(y)` is a well-defined order-reflecting additive map from the
values at `x` of the terms to `N ()`. -/
theorem doag_span_hom (x : M [^] σ) (y : N [^] σ)
    (htp : Formula.typeOf (FormulaClass.qfRelTo oagU ∅ σ) x =
      Formula.typeOf (FormulaClass.qfRelTo oagU ∅ σ) y) :
    ∃ ψ : termValues oagU () x →+ N (), (∀ a a', ψ a ≤ ψ a' ↔ (a : M ()) ≤ a') ∧
      ∀ u : oagU.Term σ ⦃()⦄, ψ ⟨u.realize x, realize_mem_termValues u x⟩ = u.realize y := by
  have heq : ∀ u₁ u₂ : oagU.Term σ ⦃()⦄,
      u₁.realize x = u₂.realize x ↔ u₁.realize y = u₂.realize y := fun u₁ u₂ => by
    simpa using Formula.realize_iff_of_typeOf_eq htp (ψ := u₁ =' u₂) (.of_isAtomic (.equal _ _))
  have hle : ∀ u₁ u₂ : oagU.Term σ ⦃()⦄,
      u₁.realize x ≤ u₂.realize x ↔ u₁.realize y ≤ u₂.realize y := fun u₁ u₂ => by
    simpa using Formula.realize_iff_of_typeOf_eq htp (ψ := .rel oagRel.le (.prod u₁ u₂))
      (.of_isAtomic (.rel _ _))
  choose t ht using fun a : termValues oagU () x => mem_termValues.1 a.2
  have hadd : ∀ a₁ a₂, (t (a₁ + a₂)).realize y = (t a₁).realize y + (t a₂).realize y := by
    intro a₁ a₂
    simpa using (heq (t (a₁ + a₂)) (t a₁ +ₗ t a₂)).1 (by simp [ht])
  refine ⟨AddMonoidHom.mk' (fun a => (t a).realize y) hadd, fun a a' => ?_, fun u => ?_⟩
  · simpa [ht] using (hle (t a) (t a')).symm
  · exact (heq _ _).1 (ht _)

end Transfer

/-- **The extension step for DOAG**: given models `M`, `N`, tuples `x`, `y` with the same
quantifier-free type, and `b : M`, there are a structure `N'`, a tuple `y'` with the same complete
type as `y` and an element `c` such that `(x, b)` and `(y', c)` have the same quantifier-free
type. -/
theorem doag_tuple_ext (M N : Unit → Type) [oagU.Structure M] [oagU.Structure N]
    [∀ s, Nonempty (N s)] [M ⊨ DOAG] [N ⊨ DOAG] (σ : Arity Unit) (x : M [^] σ) (y : N [^] σ)
    (htp : Formula.typeOf (FormulaClass.qfRelTo oagU ∅ σ) x =
      Formula.typeOf (FormulaClass.qfRelTo oagU ∅ σ) y) (b : M ()) :
    ∃ (N' : Unit → Type) (_ : oagU.Structure N') (y' : N' [^] σ) (c : N' ()),
      Formula.typeOf (FormulaClass.all oagU σ) y' = Formula.typeOf (FormulaClass.all oagU σ) y ∧
      Formula.typeOf (FormulaClass.qfRelTo oagU ∅ (σ ⨯ ⦃()⦄)) ((x, b) : M [^] (σ ⨯ ⦃()⦄)) =
        Formula.typeOf (FormulaClass.qfRelTo oagU ∅ (σ ⨯ ⦃()⦄)) ((y', c) : N' [^] (σ ⨯ ⦃()⦄)) := by
  classical
  let := modelDOAGAddCommGroup oagU M ()
  let := modelLinearOrder oagU M ()
  have := modelIsOrderedAddMonoid oagU M ()
  have := modelDOAGDerivedCompatible oagU M ()
  let := modelDOAGAddCommGroup oagU N ()
  let := modelLinearOrder oagU N ()
  have := modelIsOrderedAddMonoid oagU N ()
  have := modelDOAGDerivedCompatible oagU N ()
  have : Nontrivial (N ()) := model_nontrivial oagU N ()
  let : DivisibleBy (N ()) ℕ := divisibleByOfSMulRightSurj (N ()) ℕ fun {n} hn =>
    model_nsmul_surjective oagU N () n hn
  let : DivisibleBy (N ()) ℤ := AddGroup.divisibleByIntOfDivisibleByNat (N ())
  obtain ⟨ψ, hψle, hψ⟩ := doag_span_hom x y htp
  by_cases hcase : ∃ (k : ℤ) (a : termValues oagU () x), k ≠ 0 ∧ k • b = a
  · -- **Divisible hull**: a nonzero multiple of `b` is the value of a term at `x`; divide its
    -- counterpart in `N`.
    obtain ⟨k₀, a₀, hk₀, hb₀⟩ :
        ∃ (k₀ : ℤ) (a₀ : termValues oagU () x), 0 < k₀ ∧ k₀ • b = a₀ := by
      obtain ⟨k, a, hk, hba⟩ := hcase
      rcases hk.lt_or_gt with hk | hk
      · exact ⟨-k, -a, neg_pos.2 hk, by rw [neg_zsmul, hba, AddSubgroup.coe_neg]⟩
      · exact ⟨k, a, hk, hba⟩
    have hc : k₀ • DivisibleBy.div (ψ a₀) k₀ = ψ a₀ := DivisibleBy.div_cancel _ hk₀.ne'
    refine ⟨N, inferInstance, y, DivisibleBy.div (ψ a₀) k₀, rfl,
      doag_qf_transfer_of_key x y b _ fun k u => ?_⟩
    simpa [hψ] using
      affine_key_of_zsmul_eq ψ hψle hk₀ hb₀ hc k ⟨u.realize x, realize_mem_termValues u x⟩
  · -- **Cut**: `b` cuts the values of the terms at `x`. The cut, as a type over `y`, is realized
    -- next to a tuple `y'` with the same complete type as `y`.
    have hnd : ∀ (k : ℤ) (a : termValues oagU () x), k ≠ 0 → k • b ≠ a :=
      fun k a hk h => hcase ⟨k, a, hk, h⟩
    let P : Set (oagU.Formula (σ ⨯ ⦃()⦄)) :=
      {φ | ∃ (k : ℤ) (u : oagU.Term σ ⦃()⦄), 0 < k ∧ u.realize x < k • b ∧
          φ = ∼(zsmulT k (.var (.right .var)) ≤ₗ u.relabel fun _ => .left)} ∪
        {φ | ∃ (k : ℤ) (u : oagU.Term σ ⦃()⦄), 0 < k ∧ k • b < u.realize x ∧
          φ = ∼(u.relabel (fun _ => .left) ≤ₗ zsmulT k (.var (.right .var)))}
    obtain ⟨N', _, y', c, hy', hc⟩ := Formula.exists_realize_of_finite y P fun P₀ hP₀ => by
      -- Finite satisfiability, by `exists_affine_cut_bounds`.
      have hchoice : ∀ φ : P₀, ∃ (k : ℤ) (u : oagU.Term σ ⦃()⦄), 0 < k ∧
          ((u.realize x < k • b ∧ φ.1 = ∼(zsmulT k (.var (.right .var)) ≤ₗ
              u.relabel fun _ => .left)) ∨
            (k • b < u.realize x ∧ φ.1 = ∼(u.relabel (fun _ => .left) ≤ₗ
              zsmulT k (.var (.right .var))))) := by
        rintro ⟨φ, hφ⟩
        rcases hP₀ hφ with ⟨k, u, hk, hlt, rfl⟩ | ⟨k, u, hk, hlt, rfl⟩
        · exact ⟨k, u, hk, .inl ⟨hlt, rfl⟩⟩
        · exact ⟨k, u, hk, .inr ⟨hlt, rfl⟩⟩
      choose k u hk hφ using hchoice
      obtain ⟨c₀, hc₀⟩ := exists_affine_cut_bounds ψ hψle b
        (P₀.attach.image fun φ => (k φ, ⟨(u φ).realize x, realize_mem_termValues _ _⟩))
        (by
          intro q hq
          obtain ⟨φ, -, rfl⟩ := Finset.mem_image.1 hq
          exact hk φ)
      refine ⟨c₀, fun φ hφ' => ?_⟩
      have hbd := hc₀ _ (Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨φ, hφ'⟩))
      simp only [hψ] at hbd
      rcases hφ ⟨φ, hφ'⟩ with ⟨hlt, hform⟩ | ⟨hlt, hform⟩
      · rw [show φ = _ from hform]
        simpa using hbd.1 hlt
      · rw [show φ = _ from hform]
        simpa using hbd.2 hlt
    -- `N'` is a model of `DOAG`, since `y'` has the complete type of `y`.
    have : N' ⊨ DOAG := ⟨fun θ hθ => (Sentence.realize_lift θ y').1
      ((Formula.realize_iff_of_typeOf_eq hy' (Set.mem_univ (Sentence.lift θ))).2
        ((Sentence.realize_lift θ y).2 (Theory.realize_sentence_of_mem hθ)))⟩
    let := modelDOAGAddCommGroup oagU N' ()
    let := modelLinearOrder oagU N' ()
    have := modelIsOrderedAddMonoid oagU N' ()
    have := modelDOAGDerivedCompatible oagU N' ()
    obtain ⟨ψ', hψ'le, hψ'⟩ := doag_span_hom x y'
      (htp.trans (Formula.typeOf_eq_typeOf_of_subset (fun _ _ => Set.mem_univ _) hy').symm)
    -- `c` realizes the cut of `b`, transported along `ψ'`.
    have hcut : ∀ (k : ℤ) (a : termValues oagU () x), 0 < k →
        ((a : M ()) < k • b → ψ' a < k • c) ∧ (k • b < a → k • c < ψ' a) := by
      rintro k ⟨_, u, rfl⟩ hk
      rw [hψ' u]
      constructor
      · intro hlt
        simpa using hc _ (Or.inl ⟨k, u, hk, hlt, rfl⟩)
      · intro hlt
        simpa using hc _ (Or.inr ⟨k, u, hk, hlt, rfl⟩)
    refine ⟨N', inferInstance, y', c, hy', doag_qf_transfer_of_key x y' b c fun k u => ?_⟩
    simpa [hψ'] using
      affine_key_of_cut_bounds ψ' hψ'le hnd hcut k ⟨u.realize x, realize_mem_termValues u x⟩

/-- **Quantifier elimination for DOAG**: the one-sorted theory of nontrivial divisible ordered
abelian groups eliminates quantifiers. -/
theorem DOAG_hasQERelTo_empty : DOAG.HasQERelTo (∅ : Set Unit) :=
  Theory.hasQERelTo_of_pointed_extension fun σ r r' htp _ _ b =>
    doag_tuple_ext r.carrier r'.carrier σ r.xs r'.xs htp b

end DOAGQE

end ManySorted.Language
