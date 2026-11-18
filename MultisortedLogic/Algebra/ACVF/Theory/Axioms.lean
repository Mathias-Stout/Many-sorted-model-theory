/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Algebra.ACVF.Theory.Structure
public import MultisortedLogic.Algebra.EOGroupModel
public import MultisortedLogic.Algebra.ACF.Basic

/-!
# Axioms for the leading term structure

The sentences here say that the sorts `RV` and `Γ` really are the leading term structure and
the value group of the field sort: `rv` is multiplicative with `rv x = 0 ↔ x = 0` and onto,
`val` turns multiplication into addition, the fibers of `rv` are the open balls, and the
valuation is ultrametric.

They are stated in the three-sorted language `L_RV` of `Algebra/ACVF/Theory/Language.lean` and are
the first step of the model-recovery layer: a model of these axioms carries a valued field structure
whose leading terms are its `RV` sort.

Note that `RV` is *not* axiomatized as a ring. Its addition is the residue field addition
extended by `0`, which is not associative. If `ξ ≠ 0` lies outside the residue field, as the
leading term of a nonzero element of the maximal ideal does, then
`(ξ + 1) + (-1) = 0 + (-1) = -1`, while `ξ + (1 + (-1)) = ξ + 0 = 0`. So ring axioms on the
`RV` sort would be false in the intended models.

## Main definitions

* `Language.RVAxiom` : the axioms.
* `Language.RVAxiom.toSentence` / `toProp` : their syntactic and semantic forms.
* `Language.RVAxiom.realize_toSentence_iff_toProp` : the bridge between them.
* `Language.RVAxiom.holds` : a valued field satisfies them.
* `Language.nontriviallyValued` : nontriviality of the valuation.
* `Language.ACVFTheory` : the theory `ACVF` in `L_RV`, with soundness `models_ACVFTheory`.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure ValuationSubring

universe u

/-- Axioms describing `RV` as the leading term structure of the field sort. -/
inductive RVAxiom : Type
  /-- `rv` is multiplicative. -/
  | rvMul
  /-- `rv x = 0` exactly for `x = 0`. -/
  | rvZero
  /-- Every leading term is the leading term of a field element. -/
  | rvSurj
  /-- `val` turns the multiplication of `RV` into the addition of `Γ`. -/
  | valMul
  /-- The fibers of `rv` are the open balls. -/
  | ball
  /-- The valuation is ultrametric. -/
  | ultrametric
  /-- `val` is onto the value group. -/
  | valSurj
  /-- `val 0 = ∞`. -/
  | valZero
  /-- The `1` of the `RV` sort is the leading term of `1`. -/
  | rvOne
  /-- The negation of the `RV` sort descends from the field: `-ξ = rv (-1) * ξ`. -/
  | negRV
  /-- The addition of the `RV` sort, where it does not cancel: on representatives whose sum
  is again a unit, it is the leading term of the sum. -/
  | rvAddRes
  /-- The addition of the `RV` sort is `0` when the left argument is outside the residue
  field. -/
  | rvAddZeroL
  /-- The addition of the `RV` sort is `0` when the right argument is outside the residue
  field. -/
  | rvAddZeroR
  /-- The addition of the `RV` sort is `0` when the residues cancel. -/
  | rvAddZeroSum
  /-- The inverse of `0` is `0`. -/
  | invZero
  /-- Every nonzero leading term is invertible. -/
  | mulInv
  deriving DecidableEq

namespace RVAxiom

/-- The axioms as `L_RV`-sentences. -/
def toSentence : RVAxiom → rvLang.Sentence
  | .rvMul => ∀' RVSort.K (∀' RVSort.K (rvT (#1 *ₗ #0) =' rvT #1 *ₗ rvT #0))
  | .rvZero => ∀' RVSort.K ((rvT #0 =' 0) ⇔ (#0 =' 0))
  | .rvSurj => ∀' RVSort.RV (∃' RVSort.K (rvT #0 =' #1))
  | .valMul => ∀' RVSort.RV (∀' RVSort.RV (valT (#1 *ₗ #0) =' valT #1 +ₗ valT #0))
  | .ball =>
      ∀' RVSort.K (∀' RVSort.K
        (∼(#0 =' 0) ⟹
          ((rvT #1 =' rvT #0) ⇔ ∼(valT (rvT (#1 +ₗ -ₗ#0)) ≤ₗ valT (rvT #0)))))
  | .ultrametric =>
      ∀' RVSort.K (∀' RVSort.K
        ((valT (rvT #1) ≤ₗ valT (rvT (#1 +ₗ #0))) ⊔ (valT (rvT #0) ≤ₗ valT (rvT (#1 +ₗ #0)))))
  | .valSurj => ∀' RVSort.Γ (∃' RVSort.RV (valT #0 =' #1))
  | .valZero => valT (rvT 0) =' `∞
  | .rvOne => rvT 1 =' 1
  | .negRV => ∀' RVSort.RV (-ₗ#0 =' rvT (-ₗ1) *ₗ #0)
  | .rvAddRes =>
      ∀' RVSort.K (∀' RVSort.K
        (((valT (rvT #1) =' 0) ⊔ (#1 =' 0)) ⟹
          (((valT (rvT #0) =' 0) ⊔ (#0 =' 0)) ⟹
            ((valT (rvT (#1 +ₗ #0)) =' 0) ⟹
              (rvT #1 +ₗ rvT #0 =' rvT (#1 +ₗ #0))))))
  | .rvAddZeroL =>
      ∀' RVSort.K (∀' RVSort.K
        (∼(valT (rvT #1) =' 0) ⟹ (∼(#1 =' 0) ⟹ (rvT #1 +ₗ rvT #0 =' 0))))
  | .rvAddZeroR =>
      ∀' RVSort.K (∀' RVSort.K
        (∼(valT (rvT #0) =' 0) ⟹ (∼(#0 =' 0) ⟹ (rvT #1 +ₗ rvT #0 =' 0))))
  | .rvAddZeroSum =>
      ∀' RVSort.K (∀' RVSort.K
        (∼(valT (rvT (#1 +ₗ #0)) =' 0) ⟹ (rvT #1 +ₗ rvT #0 =' 0)))
  | .invZero => invT 0 =' 0
  | .mulInv => ∀' RVSort.RV (∼(#0 =' 0) ⟹ (#0 *ₗ invT #0 =' 1))

variable (F : Type u) [Field F] (A : ValuationSubring F)

/-- What each axiom says about a valued field. Valuations are multiplicative here, as in
Mathlib, so a *smaller* valuation means *closer*. -/
def toProp : RVAxiom → Prop
  | .rvMul => ∀ x y : F, rv (A := A) (x * y) = rv (A := A) x * rv (A := A) y
  | .rvZero => ∀ x : F, rv (A := A) x = 0 ↔ x = 0
  | .rvSurj => ∀ ξ : A.RV, ∃ x : F, rv (A := A) x = ξ
  | .valMul => ∀ ξ η : A.RV, rvVal (ξ * η) = rvVal (A := A) ξ * rvVal (A := A) η
  | .ball => ∀ x y : F, y ≠ 0 →
      (rv (A := A) x = rv (A := A) y ↔ A.valuation (x - y) < A.valuation y)
  | .ultrametric => ∀ x y : F,
      A.valuation (x + y) ≤ A.valuation x ∨ A.valuation (x + y) ≤ A.valuation y
  | .valSurj => ∀ γ : A.ValueGroup, ∃ ξ : A.RV, rvVal (A := A) ξ = γ
  | .valZero => A.valuation (0 : F) = 0
  | .rvOne => rv (A := A) (1 : F) = 1
  | .negRV => ∀ ξ : A.RV, rvNeg A ξ = rv (A := A) (-1 : F) * ξ
  | .rvAddRes => ∀ x y : F, (A.valuation x = 1 ∨ x = 0) → (A.valuation y = 1 ∨ y = 0) →
      A.valuation (x + y) = 1 →
      rvAdd A (rv (A := A) x) (rv (A := A) y) = rv (A := A) (x + y)
  | .rvAddZeroL => ∀ x y : F, A.valuation x ≠ 1 → x ≠ 0 →
      rvAdd A (rv (A := A) x) (rv (A := A) y) = 0
  | .rvAddZeroR => ∀ x y : F, A.valuation y ≠ 1 → y ≠ 0 →
      rvAdd A (rv (A := A) x) (rv (A := A) y) = 0
  | .rvAddZeroSum => ∀ x y : F, A.valuation (x + y) ≠ 1 →
      rvAdd A (rv (A := A) x) (rv (A := A) y) = 0
  | .invZero => (0 : A.RV)⁻¹ = 0
  | .mulInv => ∀ ξ : A.RV, ξ ≠ 0 → ξ * ξ⁻¹ = 1

variable {F A}

/-- A valued field satisfies every axiom. -/
theorem holds (ax : RVAxiom) : ax.toProp F A := by
  cases ax with
  | rvMul => exact fun x y => map_mul _ _ _
  | rvZero => exact fun x => rv_eq_zero_iff
  | rvSurj => exact fun ξ => rv_surjective ξ
  | valMul => exact fun ξ η => map_mul _ _ _
  | ball =>
    intro x y hy
    rw [eq_comm]
    exact rv_eq_iff_valuation_sub_lt hy
  | ultrametric =>
    intro x y
    exact le_max_iff.mp (A.valuation.map_add_le_max' x y)
  | valSurj =>
    intro γ
    obtain ⟨x, hx⟩ := A.valuation_surjective γ
    exact ⟨rv x, by rw [rvVal_rv, hx]⟩
  | valZero => exact map_zero _
  | rvOne => exact map_one _
  | negRV => exact fun _ => rfl
  | rvAddRes =>
    intro x y hx hy hxy
    exact rvAdd_rv_rv_of_isResidue A ((isResidue_rv_iff A).mpr hx)
      ((isResidue_rv_iff A).mpr hy) hxy
  | rvAddZeroL =>
    intro x y hx hx0
    refine rvAdd_eq_zero_of_not_isResidue A ?_
    simp only [isResidue_rv_iff]
    rintro ⟨h1 | h1, -, -⟩
    · exact hx h1
    · exact hx0 h1
  | rvAddZeroR =>
    intro x y hy hy0
    refine rvAdd_eq_zero_of_not_isResidue A ?_
    simp only [isResidue_rv_iff]
    rintro ⟨-, h1 | h1, -⟩
    · exact hy h1
    · exact hy0 h1
  | rvAddZeroSum =>
    intro x y hxy
    exact rvAdd_eq_zero_of_not_isResidue A fun h => hxy h.2.2
  | invZero => exact inv_zero
  | mulInv => exact fun ξ hξ => mul_inv_cancel₀ hξ

/-- The bridge between the syntactic and semantic forms of each axiom. -/
theorem realize_toSentence_iff_toProp (ax : RVAxiom) :
    rvFam A ⊨ ax.toSentence ↔ ax.toProp F A := by
  cases ax
  case valZero => exact iff_of_true (by simp [toSentence]; rfl) (map_zero _)
  all_goals simp [toSentence, toProp, ← sub_eq_add_neg]

end RVAxiom

variable {F : Type u} [Field F] {A : ValuationSubring F}

/-- The theory of the leading term structure: the `RV`-specific axioms. -/
def RVTheory : rvLang.Theory := Set.range RVAxiom.toSentence

/-- **Soundness.** A valued field, viewed as an `L_RV`-structure, models the leading term
axioms. -/
theorem models_RVTheory : rvFam A ⊨ RVTheory := by
  rw [Theory.model_iff]
  rintro φ ⟨ax, rfl⟩
  rw [RVAxiom.realize_toSentence_iff_toProp]
  exact ax.holds

/-! ### The value group

`Additive αᵒᵈ` is a linearly ordered additive commutative group with top whenever `α` is a
linearly ordered commutative group with zero, so the `Γ` sort satisfies the axioms of an
ordered abelian group with `∞` from `Algebra/Group.lean`. -/

/-- The theory of the value group: an ordered abelian group with `∞`. -/
def GammaTheory : rvLang.Theory := EOCommGroupTheory rvLang RVSort.Γ

/-- **Soundness.** The value group of a valued field models the `Γ` axioms. -/
theorem models_GammaTheory : rvFam A ⊨ GammaTheory := by
  rw [Theory.model_iff]
  rintro φ ⟨ax, rfl⟩
  exact EOCommGroupAxiom.models_ax ax

/-! ### Nontriviality, and the theory `ACVF`

The remaining axiom is that the valuation is nontrivial. Note that it cannot be stated as
`∃ x : K, val (rv x) ≠ 0`: that is satisfied by `x = 0` in every valued field, since
`val (rv 0) = ∞`. The nonzero element has to be asked for explicitly, which is what
`∼((#0 =' 0) ⊔ _)` does. -/

/-- **Nontriviality of the valuation**: some nonzero element of `K` has valuation other than
`1`. -/
def nontriviallyValued : rvLang.Sentence :=
  ∃' RVSort.K ∼((#0 =' 0) ⊔ (valT (rvT #0) =' 0))

theorem realize_nontriviallyValued :
    rvFam A ⊨ nontriviallyValued ↔ ∃ x : F, x ≠ 0 ∧ A.valuation x ≠ 1 := by
  simp [nontriviallyValued]

/-- **The theory `ACVF`** in the three-sorted leading-term language: the leading-term axioms,
the value-group axioms, the axioms of an algebraically closed field on the sort `K`, and
nontriviality of the valuation.

The sort `RV` carries no ring axioms — see the note at the top of this file — and needs none:
its multiplication is pinned down by `rvMul` and `rvSurj`, and its addition is definable from
the rest, being the residue addition extended by `0`. -/
def ACVFTheory : rvLang.Theory :=
  RVTheory ∪ GammaTheory ∪ ACFTheory rvLang RVSort.K ∪ {nontriviallyValued}

/-- **Soundness.** An algebraically closed field with a nontrivial valuation, viewed as an
`L_RV`-structure, models `ACVFTheory`. -/
theorem models_ACVFTheory [IsAlgClosed F] (hnt : ∃ x : F, x ≠ 0 ∧ A.valuation x ≠ 1) :
    rvFam A ⊨ ACVFTheory := by
  have : IsAlgClosed (rvFam A RVSort.K) := inferInstanceAs (IsAlgClosed F)
  rw [ACVFTheory, Theory.model_union_iff, Theory.model_union_iff, Theory.model_union_iff,
    Theory.model_singleton_iff]
  exact ⟨⟨⟨models_RVTheory, models_GammaTheory⟩, models_ACFTheory⟩,
    realize_nontriviallyValued.2 hnt⟩

end ManySorted.Language
