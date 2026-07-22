/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathias Stout
-/
import MultisortedLogic.Examples.Field
import MultisortedLogic.Examples.Prec
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
  A file developing the language of valued fields in the three-sorted setting.
-/
namespace MSFirstOrder
namespace Language
open Signature BoundedFormula deBruijnVar

universe u v w z u' v' w' z'

section language_schemas

inductive VFSort (vals : Type _) : Type _ where
  | K : VFSort vals --Valued Field
  | V : VFSort vals --Value Group (with infinity)
  | G : VFSort vals --Vaue Group Sort (no infinity)
  | Res (n : vals) : VFSort vals --Residue Ring Sort
  | RV (n : vals) : VFSort vals --Leading Term Structures
  | M : VFSort vals -- Maximal ideal
  | O : VFSort vals -- Valuation Ring

/-
Below are types for the various kinds of functions between
valued field sorts. They are sort-generic, so for example
we can re-use the RingFunc schema for residue rings and for
valued fields, by taking `RingFunc K` or `RingFunc (Res n)`
-/

/--
Function schema for an ordered abelian group with infinity. -/
inductive EValGroupFunc {Sorts : Type _} :
    Signature Sorts → Sorts → Type _ where
  | infinity {G} : EValGroupFunc .nil G
  | zero {G}     : EValGroupFunc .nil G
  | neg {G}      : EValGroupFunc (of G) G
  | add {G}      : EValGroupFunc (⦃G⦄ ⨯ ⦃G⦄) G

/--
Function schema for an ordered abelian group. -/
inductive ValGroupFunc {Sorts : Type _} :
    Signature Sorts → Sorts → Type _ where
  | infinity {G} : ValGroupFunc .nil G
  | zero {G}     : ValGroupFunc .nil G
  | neg {G}      : ValGroupFunc (of G) G
  | add {G}      : ValGroupFunc ((⦃G⦄ ⨯ ⦃G⦄)) G

/--
Types schema for a module over a ring.
-/
inductive ModFunc {Sorts : Type _} :
    Signature Sorts → Sorts → Type _ where
  | zero {M}   : ModFunc .nil M
  | neg  {M}   : ModFunc (of M) M
  | add  {M}   : ModFunc ((⦃M⦄ ⨯ ⦃M⦄)) M
  | smul {M R} : ModFunc (fromList [R, M]) M

/--
Types schema for a non-unital algebra over a ring (or an ideal). -/
inductive IdealFunc {Sorts : Type _} {M R : Sorts} :
    Signature Sorts → Sorts → Type _ where
  | zero {M}  : IdealFunc .nil M
  | one  {M}  : IdealFunc .nil M
  | neg  {M}  : IdealFunc (of M) M
  | add  {M}  : IdealFunc ((⦃M⦄ ⨯ ⦃M⦄)) M
  | mul  {M}  : IdealFunc ((⦃M⦄ ⨯ ⦃M⦄)) M
  | smul {M R}: IdealFunc (⦃R⦄ ⨯ ⦃M⦄) M

/--
Function schema for rings over a sort. -/
inductive RingFunc {Sorts : Type _} :
    Signature Sorts → Sorts → Type _ where
  | zero {K}  : RingFunc .nil K
  | one  {K}  : RingFunc .nil K
  | neg  {K}  : RingFunc (of K) K
  | add  {K}  : RingFunc (⦃K⦄ ⨯  ⦃K⦄) K
  | mul  {K}  : RingFunc (⦃K⦄ ⨯ ⦃K⦄) K

end language_schemas

section VFLang

variable {Sorts : Type*} (L : Language Sorts) (M : Fam Sorts) (s : Sorts)
  {σ : Signature Sorts} {α : Fam Sorts} {v : α →ₛ M}

/-- A class for languages describing a valued field in Sort `s` -/
class VFL {Sorts : Type*} (L : Language Sorts) (s : Sorts) extends RingL L s where
  /- A formula describing the valuative less than relation
    - denoted additively, as is often the convention -/
  valF : L.Formula (⦃s⦄ ⨯ ⦃s⦄).IdxFam

/-- The `L`-structure lines up witht the existing commutative valued ring structure on the Sort `s`
  We assume `CommRing` instead of `Add, Mul, Zero, One`,  as `ValuativeRel` assumes `CommRing`. -/
class CompatibleVFL [VFL L s] [L.Structure M]
  [Add (M s)] [Mul (M s)] [Zero (M s)] [One (M s)] [Neg (M s)]
  [Prec (M s)]
  extends CompatibleRingL L M s where
  vle_eq : ∀ (x : Interpret M (⦃s⦄ ⨯ ⦃s⦄)),
    VFL.valF.Realize (L := L) (x.get) ↔ x.1 ≼ x.2

@[simp]
theorem CompatibleVFL.realize_iff
    [VFL L s] [L.Structure M]
    [Add (M s)] [Mul (M s)] [Zero (M s)] [One (M s)] [Neg (M s)] [Prec (M s)]
    [CompatibleVFL L M s] :
    ∀ x : Interpret M (⦃s⦄ ⨯ ⦃s⦄),
      VFL.valF.Realize (L := L) (x.get) ↔ x.1 ≼ x.2 := CompatibleVFL.vle_eq

variable {L} {M} {s} {xs : σ.Interpret M}

/-- Creates a bounded formula asserting that the valuation of the first term is at most that of the
  second term, using the `vleF'`-formula. -/
def VFL.vleF [VFL L s] (t u : L.Term (α ⊕ₛ σ.IdxFam) ⦃s⦄) :
    L.BoundedFormula α σ :=  VFL.valF.boundedFormula₂ t u

scoped infix:50 " ≤ₗᵥ " => VFL.vleF

@[simp]
theorem compatibleVFL.realize_vle
    [VFL L s] [L.Structure M]
    [Add (M s)] [Mul (M s)] [Zero (M s)] [One (M s)] [Neg (M s)] [Prec (M s)]
    [CompatibleVFL L M s]
    (x y : L.Term (α ⊕ₛ σ.IdxFam) ⦃s⦄) :
    (x ≤ₗᵥ y).Realize v xs ↔
    (x.realize (Fam.sumElim v xs) : M s) ≼ y.realize (Fam.sumElim v xs) := by
  rw [VFL.vleF]
  simp only [BoundedFormula.realize_boundedFormula₂, Term.realize_prod, CompatibleVFL.realize_iff]

end VFLang

section ValuedRingAxioms

/-- A `Prec` instance for types with `CommRing` and `ValuativeRel`.
    This identifies the `≼` relation with the valuative relation `≤ᵥ`. -/
instance instPrecOfValuativeRel {R : Type*} [CommRing R] [ValuativeRel R] : Prec R where
  prec := (· ≤ᵥ ·)

theorem prec_eq_valuativeRel {R : Type*} [CommRing R] [ValuativeRel R] (x y : R) :
    x ≼ y ↔ x ≤ᵥ y := Iff.rfl

variable {Sorts : Type*} (L : Language Sorts) (M : Fam Sorts) (s : Sorts)

/-- Axioms for a valued commutative ring in a VFL language.
    A valued commutative ring is a commutative ring with a valuative relation ≼ satisfying
    the axioms of `ValuativeRel`:
    - Totality: x ≼ y ∨ y ≼ x
    - Transitivity: x ≼ y → y ≼ z → x ≼ z
    - Addition compatibility: x ≼ z → y ≼ z → (x + y) ≼ z
    - Right multiplication compatibility: x ≼ y → x * z ≼ y * z
    - Multiplication cancellation: ¬(z ≼ 0) → x * z ≼ y * z → x ≼ y
    - Non-triviality: ¬(1 ≼ 0) -/
inductive ValuedRingAxiom : Type _
  | cring (ca : CommRingAxiom)  -- Commutative ring axioms
  | valTotal                     -- Totality: x ≼ y ∨ y ≼ x
  | valTrans                     -- Transitivity: x ≼ y → y ≼ z → x ≼ z
  | valAdd                       -- Addition: x ≼ z → y ≼ z → (x + y) ≼ z
  | valMulLeft                  -- Right mult: x ≼ y → x * z ≼ y * z
  | valMulCancel                 -- Cancellation: ¬(z ≼ 0) → x * z ≼ y * z → x ≼ y
  | notValOneZero                -- Non-triviality: ¬(1 ≼ 0)

namespace ValuedRingAxiom

@[simp]
def toSentence [VFL L s] : ValuedRingAxiom → L.Sentence
  | cring ca => ca.toSentence L s
  | valTotal =>
      -- ∀ x y, x ≼ y ∨ y ≼ x
      ∀' s (∀' s ((#1 ≤ₗᵥ #0) ⊔ (#0 ≤ₗᵥ #1)))
  | valTrans =>
      -- ∀ x y z, x ≼ y → y ≼ z → x ≼ z
      ∀' s (∀' s (∀' s (
        (#2 ≤ₗᵥ #1) ⟹ ((#1 ≤ₗᵥ #0) ⟹ (#2 ≤ₗᵥ #0)))))
  | valAdd =>
      -- ∀ x y z, x ≼ z → y ≼ z → (x + y) ≼ z
      ∀' s (∀' s (∀' s (
        (#2 ≤ₗᵥ #0) ⟹ ((#1 ≤ₗᵥ #0) ⟹ ((#2 +ₗ #1) ≤ₗᵥ #0)))))
  | valMulLeft =>
      --∀ x y, x ≼ y → ∀ (z : R), x * z ≼ y * z
      ∀' s (∀' s (
        (#1 ≤ₗᵥ #0) ⟹ (∀' s ((#2 *ₗ #0) ≤ₗᵥ (#1 *ₗ #0)))))
  | valMulCancel =>
      -- ∀ x y z, ¬(z ≼ 0) → x * z ≼ y * z → x ≼ y
      ∀' s (∀' s (∀' s (
        ∼(#0 ≤ₗᵥ 0) ⟹ (((#2 *ₗ #0) ≤ₗᵥ (#1 *ₗ #0)) ⟹ (#2 ≤ₗᵥ #1)))))
  | notValOneZero =>
      -- ¬(1 ≼ 0)
      ∼((1 : L.Term _ ⦃s⦄) ≤ₗᵥ 0)

@[simp]
def toProp (R : Type _) [Add R] [Mul R] [Neg R] [Zero R] [One R] [Prec R] :
    ValuedRingAxiom → Prop
  | cring ca => ca.toProp R
  | valTotal => ∀ x y : R, x ≼ y ∨ y ≼ x
  | valTrans => ∀ x y z : R, x ≼ y → y ≼ z → x ≼ z
  | valAdd => ∀ x y z : R, x ≼ z → y ≼ z → (x + y) ≼ z
  -- ∀ x y, x ≼ y → ∀ (z : R), x * z ≼ y * z
  | valMulLeft => ∀ x y : R, x ≼ y → ∀ z, x * z ≼ y * z
  | valMulCancel => ∀ x y z : R, ¬(z ≼ 0) → x * z ≼ y * z → x ≼ y
  | notValOneZero => ¬((1 : R) ≼ 0)

variable {L} {M} {s} [VFL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp
    [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)] [Prec (M s)]
    [CompatibleVFL L M s]
    (ax : ValuedRingAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  cases ax with
  | cring ca =>
    rw [toProp, toSentence]
    exact ca.realize_toSentence_iff_toProp
  | valTotal =>
    simp only [toProp, toSentence]
    simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll, or_iff_not_imp_left]
    rfl
  | valTrans | valAdd | valMulLeft | valMulCancel =>
      simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
        BoundedFormula.Quantifiable.mkAll]
      rfl
  | notValOneZero =>
    simp [Sentence.Realize, Formula.Realize]


lemma models_valuedRing_axioms
    [CommRing (M s)] [ValuativeRel (M s)] [CompatibleVFL L M s]
    (ax : ValuedRingAxiom) : M ⊨ ax.toSentence L s := by
  cases ax with
  | cring ca => exact ca.models_commring_axioms
  | valTotal =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact ValuativeRel.vle_total
  | valTrans =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact fun _ _ _ hxy hyz => ValuativeRel.vle_trans hxy hyz
  | valAdd =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact fun _ _ _ hxz hyz => ValuativeRel.vle_add hxz hyz
  | valMulLeft =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact fun _ _ z h => ValuativeRel.mul_vle_mul_left z h
  | valMulCancel =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact fun _ _ _ hz hxyz => ValuativeRel.vle_mul_cancel hz hxyz
  | notValOneZero =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact ValuativeRel.not_vle_one_zero

end ValuedRingAxiom

/-- Axioms for a valued field in a VFL language.
    A valued field is a valued commutative ring that is also a field. -/
inductive ValuedFieldAxiom : Type _
  | vring (va : ValuedRingAxiom)  -- Valued ring axioms
  | existsInv                     -- Every nonzero element has an inverse
  | existsPairNe                  -- There exist two distinct elements

namespace ValuedFieldAxiom

@[simp]
def toSentence [VFL L s] : ValuedFieldAxiom → L.Sentence
  | vring va => va.toSentence L s
  | existsInv =>
      -- ∀ x, x ≠ 0 → ∃ y, x * y = 1
      ∀' s (∼(#0 =' 0) ⟹ ∃' s ((#1 *ₗ #0) =' 1))
  | existsPairNe =>
      -- ∃ x y, x ≠ y
      ∃' s (∃' s (∼(#1 =' #0)))

@[simp]
def toProp (K : Type _) [Add K] [Mul K] [Neg K] [Zero K] [One K] [Prec K] :
    ValuedFieldAxiom → Prop
  | vring va => va.toProp K
  | existsInv => ∀ x : K, x ≠ 0 → ∃ y : K, x * y = 1
  | existsPairNe => ∃ x y : K, x ≠ y

variable {L} {M} {s} [VFL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp
    [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)] [Prec (M s)]
    [CompatibleVFL L M s]
    (ax : ValuedFieldAxiom) : (M ⊨ ax.toSentence L s) ↔ ax.toProp (M s) := by
  cases ax with
  | vring va =>
    rw [toProp, toSentence]
    exact va.realize_toSentence_iff_toProp
  | existsInv =>
    simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkAll, BoundedFormula.Quantifiable.mkEx]
    rfl
  | existsPairNe =>
    simp [Sentence.Realize, Formula.Realize, BoundedFormula.Realize,
      BoundedFormula.Quantifiable.mkEx]
    rfl

lemma models_valuedField_axioms
    [Field (M s)] [ValuativeRel (M s)] [CompatibleVFL L M s]
    (ax : ValuedFieldAxiom) : M ⊨ ax.toSentence L s := by
  cases ax with
  | vring va => exact va.models_valuedRing_axioms
  | existsInv =>
    rw [realize_toSentence_iff_toProp, toProp]
    intro x hx
    exact ⟨x⁻¹, mul_inv_cancel₀ hx⟩
  | existsPairNe =>
    rw [realize_toSentence_iff_toProp, toProp]
    exact ⟨0, 1, zero_ne_one⟩

end ValuedFieldAxiom

/-- The theory of valued commutative rings on sort `s`: all `ValuedRingAxiom` sentences. -/
def ValuedRingTheory [VFL L s] : Set L.Sentence :=
  Set.range (ValuedRingAxiom.toSentence L s)

/-- The theory of valued fields on sort `s`: all `ValuedFieldAxiom` sentences. -/
def ValuedFieldTheory [VFL L s] : Set L.Sentence :=
  Set.range (ValuedFieldAxiom.toSentence L s)

/-- A valued commutative ring models all valued ring axioms. -/
theorem models_valuedRing_theory
    [VFL L s] [L.Structure M] [CommRing (M s)] [ValuativeRel (M s)] [CompatibleVFL L M s] :
    M ⊨ ValuedRingTheory L s := by
  rw [Theory.model_iff]
  intro φ ⟨ax, hax⟩
  rw [← hax]
  exact ax.models_valuedRing_axioms

/-- A valued field models all valued field axioms. -/
theorem models_valuedField_theory
    [VFL L s] [L.Structure M] [Field (M s)] [ValuativeRel (M s)] [CompatibleVFL L M s] :
    M ⊨ ValuedFieldTheory L s := by
  rw [Theory.model_iff]
  intro φ ⟨ax, hax⟩
  rw [← hax]
  exact ax.models_valuedField_axioms

/-! ### Constructing ValuativeRel from axiom satisfaction -/

/-- If a structure satisfies all `ValuedRingAxiom` axioms,
  the `Prec` relation satisfies `ValuativeRel`. -/
@[reducible]
def valuativeRelOfAxioms {R : Type*} [CommRing R] [Prec R]
    (h_total : ∀ x y : R, x ≼ y ∨ y ≼ x)
    (h_trans : ∀ x y z : R, x ≼ y → y ≼ z → x ≼ z)
    (h_add : ∀ x y z : R, x ≼ z → y ≼ z → (x + y) ≼ z)
    (h_mul_left : ∀ x y : R, x ≼ y → ∀ (z : R), x * z ≼ y * z)
    (h_mul_cancel : ∀ x y z : R, ¬(z ≼ 0) → x * z ≼ y * z → x ≼ y)
    (h_not_one_zero : ¬((1 : R) ≼ 0)) : ValuativeRel R where
  vle := (· ≼ ·)
  vle_total := h_total
  vle_trans {z y x} := h_trans x y z
  vle_add {x y z} := h_add x y z
  mul_vle_mul_left {x y} := h_mul_left x y
  vle_mul_cancel {x y z} := h_mul_cancel x y z
  not_vle_one_zero := h_not_one_zero
  vle_mul_comm {x y} := by rw [mul_comm x y]; exact (h_total (y * x) (y * x)).elim id id

/-- If a structure models all valued ring axioms, we can construct a `ValuativeRel` instance. -/
@[reducible]
def valuativeRelOfModelsValuedRingTheory
    [VFL L s] [L.Structure M] [CommRing (M s)] [Prec (M s)] [CompatibleVFL L M s]
    (hM : M ⊨ ValuedRingTheory L s) : ValuativeRel (M s) := by
  rw [Theory.model_iff] at hM
  have h_total : M ⊨ ValuedRingAxiom.toSentence L s .valTotal := by
    apply hM; exact ⟨.valTotal, rfl⟩
  have h_trans : M ⊨ ValuedRingAxiom.toSentence L s .valTrans := by
    apply hM; exact ⟨.valTrans, rfl⟩
  have h_add : M ⊨ ValuedRingAxiom.toSentence L s .valAdd := by
    apply hM; exact ⟨.valAdd, rfl⟩
  have h_mul_right : M ⊨ ValuedRingAxiom.toSentence L s .valMulLeft := by
    apply hM; exact ⟨.valMulLeft, rfl⟩
  have h_mul_cancel : M ⊨ ValuedRingAxiom.toSentence L s .valMulCancel := by
    apply hM; exact ⟨.valMulCancel, rfl⟩
  have h_not_one_zero : M ⊨ ValuedRingAxiom.toSentence L s .notValOneZero := by
    apply hM; exact ⟨.notValOneZero, rfl⟩
  rw [ValuedRingAxiom.realize_toSentence_iff_toProp] at *
  exact valuativeRelOfAxioms h_total h_trans h_add h_mul_right h_mul_cancel h_not_one_zero

/-- If a structure models all valued field axioms, we can construct a `ValuativeRel` instance. -/
@[reducible]
def valuativeRelOfModelsValuedFieldTheory
    [VFL L s] [L.Structure M] [CommRing (M s)] [Prec (M s)] [CompatibleVFL L M s]
    (hM : M ⊨ ValuedFieldTheory L s) : ValuativeRel (M s) := by
  apply valuativeRelOfModelsValuedRingTheory (L := L) (M := M) (s := s)
  rw [Theory.model_iff] at hM ⊢
  intro φ ⟨ax, hax⟩
  rw [← hax]
  have : M ⊨ (ValuedFieldAxiom.vring ax).toSentence L s := by
    apply hM; exact ⟨.vring ax, rfl⟩
  simpa using this

end ValuedRingAxioms

/-
/- Basic experiments with a three-sorted language for valued fields-/
section ThreeSorted

open RingFunc


inductive Sorts₃
  | VF --  Home valued field sort
  | EVG -- Value group, with infinity
  | RF -- Residue field

open Sorts₃

inductive Functions₃ : Signature Sorts₃ → Sorts₃ → Type
  | VFFunc {σ s} (f : RingFunc VF σ s)        : Functions₃ σ s
  | RFFunc {σ s} (f : RingFunc RF σ s)        : Functions₃ σ s
  | EVGFunc {σ s} (f : EValGroupFunc EVG σ s) : Functions₃ σ s
  | ν   : Functions₃ (.of VF) EVG -- valuation map
  | res : Functions₃ (.of VF) RF -- residue map (extended by zero)
open Functions₃

inductive Relations₃ : Signature Sorts₃ → Type
  | LE : Relations₃ (bsig EVG)

/- A standard 3-sorted language for valued fields-/
def L₃ :  Language Sorts₃ where
  Functions := Functions₃
  Relations := Relations₃

instance instRingVF : RingL L₃ VF where
  addFunc   := VFFunc add
  mulFunc   := VFFunc mul
  negFunc   := VFFunc neg
  zeroConst := VFFunc zero
  oneConst  := VFFunc one

instance instRingRF : RingL L₃ RF where
  addFunc   := RFFunc add
  mulFunc   := RFFunc mul
  negFunc   := RFFunc neg
  zeroConst := RFFunc zero
  oneConst  := RFFunc one

open EValGroupFunc in
instance instAGroupEVG : AGroupL L₃ EVG where
  addFunc   := EVGFunc EValGroupFunc.add
  negFunc   := EVGFunc EValGroupFunc.neg
  zeroConst := EVGFunc EValGroupFunc.zero

instance instOrderEVG : OrderL L₃ EVG where
  orderRel := Relations₃.LE

instance instInfinityEVG : InfinityL L₃ EVG where
  inftyConst := EVGFunc EValGroupFunc.infinity

instance instOAGroupEVG : OAGroupL L₃ EVG where
  toAGroupL := instAGroupEVG
  toOrderL := instOrderEVG

instance instEOAGroupEVG : EOAGroupL L₃ EVG where
  toOAGroupL := instOAGroupEVG
  toInfinityL := instInfinityEVG

variable (K : Type*) [Field K] [ValuativeRel K]

open Classical

/-- The interpretation of the three sorts for a valued field `R`.
- `VF` is interpreted as `R` itself
- `RF` is interpreted as the residue field of `R` (at the support of the valuation)
- `EVG` is interpreted as the additive value group with infinity, using additive notation
-/
abbrev VFInterpret : Sorts₃ → Type _
  | VF  => K
  | RF  => (ValuativeRel.supp K).ResidueField
  | EVG => Additive (ValuativeRel.ValueGroupWithZero K)

/-- Todo: should this be a global instance or def?-/
noncomputable def StructureVF : L₃.Structure (VFInterpret K) where
  funMap := fun {σ s} f =>
    match s, σ, f with
    -- VF ring operations
    | _, _, VFFunc RingFunc.zero  => fun _ => (0 : K)
    | _, _, VFFunc RingFunc.one   => fun _ => (1 : K)
    | _, _, VFFunc RingFunc.neg   => fun x => - x
    | _, _, VFFunc RingFunc.add   => fun x => x.1 + x.2
    | _, _, VFFunc RingFunc.mul   => fun x => x.1 * x.2
    -- RF ring operations
    | _, _, RFFunc RingFunc.zero  => fun _ => (0 : (ValuativeRel.supp K).ResidueField)
    | _, _, RFFunc RingFunc.one   => fun _ => (1 : (ValuativeRel.supp K).ResidueField)
    | _, _, RFFunc RingFunc.neg   => fun x => -x
    | _, _, RFFunc RingFunc.add   => fun x => x.1 + x.2
    | _, _, RFFunc RingFunc.mul   => fun x => x.1 * x.2
    -- EVG extended value group operations (additive notation on multiplicative group)
    | _, _, EVGFunc EValGroupFunc.infinity =>
        fun _ => (Additive.ofMul (0 : ValuativeRel.ValueGroupWithZero K))
    | _, _, EVGFunc EValGroupFunc.zero =>
        fun _ => (Additive.ofMul (1 : ValuativeRel.ValueGroupWithZero K))
    | _, _, EVGFunc EValGroupFunc.neg =>
        fun x => Additive.ofMul (Additive.toMul x)⁻¹
    | _, _, EVGFunc EValGroupFunc.add =>
        fun x => Additive.ofMul (Additive.toMul x.1 * Additive.toMul x.2)
    -- Valuation map: K → EVG
    | _, _, ν => fun x => Additive.ofMul (ValuativeRel.valuation K x)
    -- Residue map: K → RF (defined on valuation ring, extended by zero)
    | _, _, res => fun x =>
        if x ∈ ValuativeRel.supp K then 0
        else algebraMap K (ValuativeRel.supp K).ResidueField x
  RelMap := fun {σ} r =>
    match σ, r with
    | _, Relations₃.LE => fun x => Additive.toMul x.1 ≤ Additive.toMul x.2

/-- Compatibility class for the three-sorted valued field language L₃.
This asserts that the interpretations of all function and relation symbols
agree with the existing typeclass instances on the three sorts:
- `M VF`: a field with a valuative relation (ring compatibility via `CompatibleRingL`)
- `M RF`: the residue field (ring compatibility via `CompatibleRingL`)
- `M EVG`: the extended value group with additive notation
    (group + order + infinity compatibility via existing classes)

The individual sort compatibilities are bundled as fields rather than instance parameters,
which makes constructing instances cleaner.
-/
class CompatibleL₃ (M : Sorts₃ → Type*) [L₃.Structure M]
    -- VF is a field with valuative relation
    [Field (M VF)] [ValuativeRel (M VF)]
    -- RF is a field
    [Field (M RF)]
    -- EVG is an ordered additive group with infinity (via Additive)
    [Add (M EVG)] [Neg (M EVG)] [Zero (M EVG)] [LE (M EVG)] [Top (M EVG)]
    : Prop where
  -- Individual sort compatibilities as fields
  compatVF : CompatibleRingL L₃ M VF
  compatRF : CompatibleRingL L₃ M RF
  compatEVG_group : CompatibleAGroupL L₃ M EVG
  compatEVG_order : CompatibleOrderL L₃ M EVG
  compatEVG_top : CompatibleTopL L₃ M EVG
 /- -- Type equalities linking the abstract sorts to the canonical types from ValuativeRel
 /- -- Type equalities linking the abstract sorts to the canonical types from ValuativeRel
  vg_eq : M EVG = Additive (ValuativeRel.ValueGroupWithZero (M VF))
  rf_eq : M RF = (ValuativeRel.supp (M VF)).ResidueField
  -- Valuation map compatibility: ν agrees with the canonical valuation
  val_eq : ∀ x : M VF,
    Structure.funMap (L := L₃) ν x = vg_eq ▸ Additive.ofMul (ValuativeRel.valuation (M VF) x)
  -- Residue map compatibility: res is defined on valuation ring, extended by zero
  res_eq : ∀ x : M VF,
    Structure.funMap (L := L₃) res x = rf_eq ▸
      (if x ∈ ValuativeRel.supp (M VF) then 0
       else algebraMap (M VF) (ValuativeRel.supp (M VF)).ResidueField x)
-/
-/

/-! ### Compatibility instances for `VFInterpret K` with `StructureVF K` -/


attribute [local instance] StructureVF

/-- Top instance for the value group with zero (infinity is 0 in multiplicative notation). -/
noncomputable instance instTopEVG : Top (VFInterpret K EVG) where
  top := Additive.ofMul (0 : ValuativeRel.ValueGroupWithZero K)

/-- TODO: instance or def?
  The canonical `StructureVF K` satisfies `CompatibleL₃`. -/
noncomputable instance instCompatibleL₃ : CompatibleL₃ (VFInterpret K) where
  compatVF := {
    add_eq := fun _ => rfl
    zero_eq := rfl
    neg_eq := fun _ => rfl
    mul_eq := fun _ => rfl
    one_eq := rfl
  }
  compatRF := {
    add_eq := fun _ => rfl
    zero_eq := rfl
    neg_eq := fun _ => rfl
    mul_eq := fun _ => rfl
    one_eq := rfl
  }
  compatEVG_group := {
    add_eq := fun _ => rfl
    zero_eq := rfl
    neg_eq := fun _ => rfl
  }
  compatEVG_order := {
    le_eq := fun _ => Iff.rfl
  }
  compatEVG_top := {
    infty_eq := rfl
  }



/-! ### Valued Field Axioms in L₃ -/

/-- Helper: apply the valuation map ν to a VF term, producing a EVG term. -/
abbrev νT {α : Sorts₃ → Type*} (t : L₃.Term α (.of VF)) : L₃.Term α (.of EVG) :=
  Term.func ν t

/-- Helper: apply the residue map res to a VF term, producing an RF term. -/
abbrev resT {α : Sorts₃ → Type*} (t : L₃.Term α (.of VF)) : L₃.Term α (.of RF) :=
  Term.func res t

/-- Axioms for the theory of valued fields in the three-sorted language L₃.
- VF is a field
- RF is a field
- EVG is an extended ordered abelian group (with infinity)
- ν : VF → EVG satisfies valuation axioms (multiplicative, ultrametric, ν(0) = ∞)
- ν is surjective
- res defines a ring morphism from {x : VF | ν(x) ≥ 0} to RF
-/
inductive ValuedFieldAxiom : Type
  | fieldVF (fa : FieldAxiom)           -- VF is a field
  | fieldRF (fa : FieldAxiom)           -- RF is a field
  | eoagroupEVG (ea : EOCommGroupAxiom) -- EVG is an extended ordered abelian group
  | nuMul                                -- ν(x * y) = ν(x) + ν(y)
  | nuUltra                              -- ν(x + y) ≤ max{ν(x), ν(y)}
  | nuZero                               -- ν(0) = ∞
  | nuSurj                               -- ν is surjective
  | resZero                              -- res(0) = 0
  | resOne                               -- res(1) = 1
  | resAdd                               -- res(x + y) = res(x) + res(y) (for ν(x), ν(y) ≥ 0)
  | resMul                               -- res(x * y) = res(x) * res(y) (for ν(x), ν(y) ≥ 0)

namespace ValuedFieldAxiom

/-- Convert a valued field axiom to a sentence in L₃. -/
@[simp]
def toSentence : ValuedFieldAxiom → L₃.Sentence
  | fieldVF fa => fa.toSentence L₃ VF
  | fieldRF fa => fa.toSentence L₃ RF
  | eoagroupEVG ea => ea.toSentence L₃ EVG
  | nuMul =>
      -- ∀ x y : VF, ν(x * y) = ν(x) + ν(y)
      ∀' VF (∀' VF (
        νT ((#1 : L₃.Term _ (.of VF)) *ₗ #0) =' (νT #1 +ₗ νT #0)
      ))
  | nuUltra =>
      -- ∀ x y : VF, ν(x + y) ≤ max{ν(x), ν(y)}
      -- This is equivalent to: ν(x + y) ≤ ν(x) ∨ ν(x + y) ≤ ν(y)
      ∀' VF (∀' VF (
        (νT ((#1 : L₃.Term _ (.of VF)) +ₗ #0) ≤ₗ νT #1)
        ⊔ (νT ((#1 : L₃.Term _ (.of VF)) +ₗ #0) ≤ₗ νT #0)
      ))
  | nuZero =>
      -- ν(0) = ∞
      νT (0 : L₃.Term _ (.of VF)) =' (`∞ : L₃.Term _ (.of EVG))
  | nuSurj =>
      -- ∀ v : EVG, ∃ x : VF, ν(x) = v
      ∀' EVG (∃' VF (νT #0 =' #1))
  | resZero =>
      -- res(0) = 0
      resT (0 : L₃.Term _ (.of VF)) =' (0 : L₃.Term _ (.of RF))
  | resOne =>
      -- res(1) = 1
      resT (1 : L₃.Term _ (.of VF)) =' (1 : L₃.Term _ (.of RF))
  | resAdd =>
      -- ∀ x y : VF, ν(x) ≥ 0 → ν(y) ≥ 0 → res(x + y) = res(x) + res(y)
      ∀' VF (∀' VF (
        (0 ≤ₗ νT (#1 : L₃.Term _ (.of VF))) ⟹
        (0 ≤ₗ νT (#0 : L₃.Term _ (.of VF))) ⟹
        (resT ((#1 : L₃.Term _ (.of VF)) +ₗ #0) =' (resT #1 +ₗ resT #0))
      ))
  | resMul =>
      -- ∀ x y : VF, ν(x) ≥ 0 → ν(y) ≥ 0 → res(x * y) = res(x) * res(y)
      ∀' VF (∀' VF (
        (0 ≤ₗ νT (#1 : L₃.Term _ (.of VF))) ⟹
        (0 ≤ₗ νT (#0 : L₃.Term _ (.of VF))) ⟹
        (resT ((#1 : L₃.Term _ (.of VF)) *ₗ #0) =' (resT #1 *ₗ resT #0))
      ))

variable (K : Type*) (k : Type*) (Γ : Type*)

/-- Convert a valued field axiom to its propositional interpretation.
- `K` is the valued field (VF sort)
- `k` is the residue field (RF sort)
- `Γ` is the extended value group (EVG sort), using additive notation
- `v : K → Γ` is the valuation map
- `r : K → k` is the residue map
-/
@[simp]
def toProp [Add K] [Mul K] [Neg K] [Zero K] [One K]
    [Add k] [Mul k] [Neg k] [Zero k] [One k]
    [Add Γ] [Neg Γ] [Zero Γ] [LE Γ] [Top Γ]
    (v : K → Γ) (r : K → k) : ValuedFieldAxiom → Prop
  | fieldVF fa => fa.toProp K
  | fieldRF fa => fa.toProp k
  | eoagroupEVG ea => ea.toProp Γ
  | nuMul => ∀ x y : K, v (x * y) = v x + v y
  | nuUltra => ∀ x y : K, v (x + y) ≤ v x ∨ v (x + y) ≤ v y
  | nuZero => v 0 = ⊤
  | nuSurj => ∀ g : Γ, ∃ x : K, v x = g
  | resZero => r 0 = 0
  | resOne => r 1 = 1
  | resAdd => ∀ x y : K, (0 : Γ) ≤ v x → (0 : Γ) ≤ v y → r (x + y) = r x + r y
  | resMul => ∀ x y : K, (0 : Γ) ≤ v x → (0 : Γ) ≤ v y → r (x * y) = r x * r y

variable {K k Γ}
variable (M : Sorts₃ → Type*) [L₃.Structure M]
variable [Add (M VF)] [Mul (M VF)] [Neg (M VF)] [Zero (M VF)] [One (M VF)]
variable [Add (M RF)] [Mul (M RF)] [Neg (M RF)] [Zero (M RF)] [One (M RF)]
variable [Add (M EVG)] [Neg (M EVG)] [Zero (M EVG)] [LE (M EVG)] [Top (M EVG)]
variable [CompatibleRingL L₃ M VF] [CompatibleRingL L₃ M RF]
variable [CompatibleOAGroupL L₃ M EVG] [CompatibleTopL L₃ M EVG]

/-- The valuation map as interpreted in the structure M. -/
def valMap : M VF → M EVG := Structure.funMap (L := L₃) ν

/-- The residue map as interpreted in the structure M. -/
def resMap : M VF → M RF := Structure.funMap (L := L₃) res

theorem toSentence_iff_toProp (ax : ValuedFieldAxiom) :
    (M ⊨ ax.toSentence) ↔ ax.toProp (M VF) (M RF) (M EVG) (valMap M) (resMap M) := by
  cases ax with
  | fieldVF fa =>
    rw [toProp, toSentence]
    exact fa.realize_toSentence_iff_toProp
  | fieldRF fa =>
    rw [toProp, toSentence]
    exact fa.realize_toSentence_iff_toProp
  | eoagroupEVG ea =>
    rw [toProp, toSentence]
    exact ea.realize_toSentence_iff_toProp
  | nuMul =>
    simp only [toProp, toSentence, valMap]
    simp? [Sentence.Realize, Formula.Realize]
  | nuUltra =>
    simp only [toProp, toSentence, valMap, νT, or_iff_not_imp_left]
    simp only [Sentence.Realize, Formula.Realize]
    simp? [BoundedFormula.Realize]
  | nuZero =>
    simp only [toProp, toSentence, valMap]
    simp? [Sentence.Realize, Formula.Realize]
  | nuSurj =>
    simp only [toProp, toSentence, valMap]
    simp? [Sentence.Realize, Formula.Realize, BoundedFormula.Realize]
  | resZero =>
    simp only [toProp, toSentence, resMap]
    simp? [Sentence.Realize, Formula.Realize]
  | resOne =>
    simp only [toProp, toSentence, resMap]
    simp? [Sentence.Realize, Formula.Realize]
  | resAdd =>
    simp only [toProp, toSentence, valMap, resMap]
    simp? [Sentence.Realize, Formula.Realize]
  | resMul =>
    simp only [toProp, toSentence, valMap, resMap]
    simp? [Sentence.Realize, Formula.Realize]

end ValuedFieldAxiom

/-- The theory of valued fields: all `ValuedFieldAxiom` sentences. -/
def ValuedFieldTheory : Set L₃.Sentence :=
  Set.range ValuedFieldAxiom.toSentence

/-! ### Models of the Valued Field Theory -/


attribute [local instance] StructureVF instTopEVG

-- TODO: remove these experiments
set_option diagnostics true
#synth L₃.Structure (VFInterpret K)
#synth CompatibleL₃ (VFInterpret K)
-- Local instances for compatibility, extracted from instCompatibleL₃
noncomputable instance instCompatibleRingVF' : CompatibleRingL L₃ (VFInterpret K) VF :=
  CompatibleL₃.compatVF

noncomputable instance instCompatibleRingRF' : CompatibleRingL L₃ (VFInterpret K) RF :=
  CompatibleL₃.compatRF

noncomputable instance instCompatibleOAGroupEVG : CompatibleOAGroupL L₃ (VFInterpret K) EVG where
  toCompatibleAGroupL := CompatibleL₃.compatEVG_group
  toCompatibleOrderL := CompatibleL₃.compatEVG_order

noncomputable instance instCompatibleTopEVG' : CompatibleTopL L₃ (VFInterpret K) EVG :=
  CompatibleL₃.compatEVG_top

#check Setoid
#check Quotient
--TODO: improve this
/-- A valued field with compatible L₃-structure models all valued field axioms. -/
theorem models_valued_field_axioms (ax : ValuedFieldAxiom) :
    VFInterpret K ⊨ ax.toSentence := by
  cases ax with
  | fieldVF fa =>
    -- For VF field axioms, use FieldAxiom.models_field_axioms directly
    simp only [ValuedFieldAxiom.toSentence]
    exact FieldAxiom.models_field_axioms fa
  | fieldRF fa =>
    -- For RF field axioms, use FieldAxiom.models_field_axioms directly
    simp only [ValuedFieldAxiom.toSentence]
    exact FieldAxiom.models_field_axioms fa
  | eoagroupEVG ea =>
    simp only [ValuedFieldAxiom.toSentence]
    -- The extended ordered abelian group axioms need the appropriate instances
    sorry
  | nuMul =>
    rw [ValuedFieldAxiom.toSentence_iff_toProp]
    simp only [ValuedFieldAxiom.toProp, ValuedFieldAxiom.valMap]
    intro x y
    simp only [VFInterpret, Structure.funMap]
    -- ν(x * y) = ν(x) + ν(y) follows from ValuativeRel.valuation being a valuation
    simp only [Valuation.map_mul, ofMul_mul]
  | nuUltra =>
    rw [ValuedFieldAxiom.toSentence_iff_toProp]
    simp only [ValuedFieldAxiom.toProp, ValuedFieldAxiom.valMap]
    intro x y
    simp only [VFInterpret, Structure.funMap]
    -- Ultrametric property follows from ValuativeRel
    simp? [Additive.ofMul]
    sorry
  | nuZero =>
    rw [ValuedFieldAxiom.toSentence_iff_toProp]
    simp only [ValuedFieldAxiom.toProp, ValuedFieldAxiom.valMap]
    simp only [VFInterpret, Structure.funMap]
    -- ν(0) = ∞ follows from valuation properties
    simp? [map_zero]
    rfl
  | nuSurj =>
    rw [ValuedFieldAxiom.toSentence_iff_toProp]
    simp only [ValuedFieldAxiom.toProp, ValuedFieldAxiom.valMap]
    intro g
    simp only [VFInterpret, Structure.funMap]
    -- Surjectivity of valuation
    sorry
  | resZero =>
    rw [ValuedFieldAxiom.toSentence_iff_toProp]
    simp only [ValuedFieldAxiom.toProp, ValuedFieldAxiom.resMap]
    simp only [VFInterpret, Structure.funMap]
    -- res(0) = 0: 0 ∈ supp K, so res(0) = 0 by definition
    simp only [ValuativeRel.supp, Ideal.zero_mem, ↓reduceIte]
  | resOne =>
    rw [ValuedFieldAxiom.toSentence_iff_toProp]
    simp only [ValuedFieldAxiom.toProp, ValuedFieldAxiom.resMap]
    simp only [VFInterpret, Structure.funMap]
    -- res(1) = 1: 1 ∉ supp K (supp is a proper ideal), so res(1) = algebraMap 1 = 1
    sorry
  | resAdd =>
    rw [ValuedFieldAxiom.toSentence_iff_toProp]
    simp only [ValuedFieldAxiom.toProp, ValuedFieldAxiom.valMap, ValuedFieldAxiom.resMap]
    intro x y hx hy
    simp only [VFInterpret, Structure.funMap] at *
    -- res is additive on the valuation ring
    sorry
  | resMul =>
    rw [ValuedFieldAxiom.toSentence_iff_toProp]
    simp only [ValuedFieldAxiom.toProp, ValuedFieldAxiom.valMap, ValuedFieldAxiom.resMap]
    intro x y hx hy
    simp only [VFInterpret, Structure.funMap] at *
    -- res is multiplicative on the valuation ring
    sorry

/-- A valued field with compatible L₃-structure models the valued field theory. -/
theorem models_valued_field_theory :
    VFInterpret K ⊨ ValuedFieldTheory := by
  rw [Theory.model_iff]
  intro φ ⟨ax, hax⟩
  rw [← hax]
  exact models_valued_field_axioms _ ax

#check HPow
#check HPow
end ThreeSorted
-/
end Language

end MSFirstOrder
