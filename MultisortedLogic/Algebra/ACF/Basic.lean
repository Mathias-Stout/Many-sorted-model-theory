/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson
-/
module

public import MultisortedLogic.Algebra.Field
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The theory of algebraically closed fields

The theory of algebraically closed fields on a sort `s` of a language with a ring language on `s`.
Quantifier elimination for the one-sorted theory `ACF` is in `Algebra/ACF/QE.lean`.

## Main results

* `ACFTheory L s`, `models_ACFTheory`, `modelField`, `modelIsAlgClosed`: the theory of
  algebraically closed fields, and the correspondence between its models and algebraically
  closed fields.

## References

The theory of algebraically closed fields was originally based on
`Mathlib/ModelTheory/Algebra/Field/IsAlgClosed.lean`, by Chris Hughes.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

universe u v w z

variable {S : Type z}

/-! ### Monic Horner polynomials -/

section Horner

variable {L : Language.{u, v} S} {Γ : Arity S} {s : S}

/-- The arity of the `n + 1` coefficients of a monic polynomial of degree `n + 1`. -/
def coeffSig (s : S) : ℕ → Arity S
  | 0 => ⦃s⦄
  | n + 1 => ⦃s⦄ ⨯ coeffSig s n

/-- The position of the `i`-th coefficient in `coeffSig s n`. Indices `i > n` are clamped to the
last position; the Horner constructions only use `i ≤ n`. -/
def coeffIdx (s : S) : (n : ℕ) → ℕ → (coeffSig s n).Idx s
  | 0, _ => .var
  | _ + 1, 0 => .left .var
  | n + 1, i + 1 => .right (coeffIdx s n i)

/-- The monic Horner term `a₀ + x * (a₁ + x * (⋯ + x * (aₙ + x)))`, which expands to
`x ^ (n + 1) + ∑ i ≤ n, aᵢ * x ^ i`. -/
def hornerT [RingL L s] (x : L.Term Γ ⦃s⦄) : ℕ → (ℕ → L.Term Γ ⦃s⦄) → L.Term Γ ⦃s⦄
  | 0, a => a 0 +ₗ x
  | n + 1, a => a 0 +ₗ x *ₗ hornerT x n (fun i => a (i + 1))

/-- The value of the monic Horner polynomial, using only `+` and `*`. -/
def hornerVal {K : Type*} [Add K] [Mul K] (x : K) : ℕ → (ℕ → K) → K
  | 0, a => a 0 + x
  | n + 1, a => a 0 + x * hornerVal x n (fun i => a (i + 1))

/-- The general Horner term `a₀ + x * (a₁ + x * (⋯ + x * aₙ))`, which expands to
`∑ i ≤ n, aᵢ * x ^ i`. -/
def polyT [RingL L s] (x : L.Term Γ ⦃s⦄) : ℕ → (ℕ → L.Term Γ ⦃s⦄) → L.Term Γ ⦃s⦄
  | 0, a => a 0
  | n + 1, a => a 0 +ₗ x *ₗ polyT x n (fun i => a (i + 1))

/-- The value of the general Horner polynomial. -/
def polyVal {K : Type*} [Add K] [Mul K] (x : K) : ℕ → (ℕ → K) → K
  | 0, a => a 0
  | n + 1, a => a 0 + x * polyVal x n (fun i => a (i + 1))

variable {M : S → Type w} [L.Structure M]

@[simp]
theorem realize_polyT [RingL L s] [Add (M s)] [Mul (M s)] [CompatibleAddL L M s]
    [CompatibleMulL L M s] (x : L.Term Γ ⦃s⦄) (n : ℕ) (a : ℕ → L.Term Γ ⦃s⦄) (xs : M [^] Γ) :
    (polyT x n a).realize xs = polyVal (x.realize xs) n (fun i => (a i).realize xs) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [polyT, polyVal, ih]

@[simp]
theorem realize_hornerT [RingL L s] [Add (M s)] [Mul (M s)] [CompatibleAddL L M s]
    [CompatibleMulL L M s] (x : L.Term Γ ⦃s⦄) (n : ℕ) (a : ℕ → L.Term Γ ⦃s⦄) (xs : M [^] Γ) :
    (hornerT x n a).realize xs = hornerVal (x.realize xs) n (fun i => (a i).realize xs) := by
  induction n generalizing a with
  | zero => simp [hornerT, hornerVal]
  | succ n ih => simp [hornerT, hornerVal, ih]

/-- The general Horner polynomial is `∑ i ≤ n, aᵢ xⁱ`. -/
theorem polyVal_eq_sum {K : Type*} [CommRing K] (x : K) (n : ℕ) (a : ℕ → K) :
    polyVal x n a = ∑ i ∈ Finset.range (n + 1), a i * x ^ i := by
  induction n generalizing a with
  | zero => simp [polyVal]
  | succ n ih =>
    rw [polyVal, ih, Finset.sum_range_succ' (fun i => a i * x ^ i) (n + 1), Finset.mul_sum]
    have hsum : ∑ i ∈ Finset.range (n + 1), x * (a (i + 1) * x ^ i)
        = ∑ i ∈ Finset.range (n + 1), a (i + 1) * x ^ (i + 1) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum]
    ring

/-- The value of a polynomial, in Horner form. -/
theorem polyVal_coeff_eq_eval {K : Type*} [CommRing K] (x : K) (q : Polynomial K) :
    polyVal x q.natDegree (fun i => q.coeff i) = q.eval x := by
  rw [polyVal_eq_sum, Polynomial.eval_eq_sum_range]

/-- The Horner value of the coefficients of `q` pushed through `f` is the value of `q.map f`. -/
theorem polyVal_map_eq_eval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (q : Polynomial R) (c : S) :
    polyVal c q.natDegree (fun i => f (q.coeff i)) = (q.map f).eval c := by
  rw [polyVal_eq_sum,
    Polynomial.eval_eq_sum_range' (lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_succ_self _))]
  exact Finset.sum_congr rfl (fun i _ => by rw [Polynomial.coeff_map])

/-- The Horner polynomial is the monic polynomial with the given coefficients. -/
theorem hornerVal_eq_monic {K : Type*} [CommRing K] (x : K) (n : ℕ) (a : ℕ → K) :
    hornerVal x n a = x ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), a i * x ^ i := by
  induction n generalizing a with
  | zero => simp [hornerVal]; ring
  | succ n ih =>
    rw [hornerVal, ih, Finset.sum_range_succ' (fun i => a i * x ^ i) (n + 1), mul_add,
      Finset.mul_sum]
    have hsum : ∑ i ∈ Finset.range (n + 1), x * (a (i + 1) * x ^ i)
        = ∑ i ∈ Finset.range (n + 1), a (i + 1) * x ^ (i + 1) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum]
    ring

/-- `hornerVal` depends only on the coefficients `a 0, …, a n`. -/
theorem hornerVal_congr {K : Type*} [Add K] [Mul K] (x : K) (n : ℕ) {a a' : ℕ → K}
    (h : ∀ i ≤ n, a i = a' i) : hornerVal x n a = hornerVal x n a' := by
  induction n generalizing a a' with
  | zero => simp [hornerVal, h 0 le_rfl]
  | succ n ih =>
    rw [hornerVal, hornerVal, h 0 (Nat.zero_le _),
      ih (fun i hi => h (i + 1) (Nat.succ_le_succ hi))]

/-- `polyVal` depends only on the coefficients `a 0, …, a n`. -/
theorem polyVal_congr {K : Type*} [Add K] [Mul K] (x : K) (n : ℕ) {a a' : ℕ → K}
    (h : ∀ i ≤ n, a i = a' i) : polyVal x n a = polyVal x n a' := by
  induction n generalizing a a' with
  | zero => simp [polyVal, h 0 le_rfl]
  | succ n ih =>
    rw [polyVal, polyVal, h 0 (Nat.zero_le _),
      ih (fun i hi => h (i + 1) (Nat.succ_le_succ hi))]

/-- The tuple of coefficients `a 0, …, a n`. -/
def mkCoeffTuple (s : S) : (n : ℕ) → (ℕ → M s) → M [^] coeffSig s n
  | 0, a => a 0
  | n + 1, a => (a 0, mkCoeffTuple s n (fun i => a (i + 1)))

theorem get_mkCoeffTuple (s : S) (n : ℕ) (a : ℕ → M s) :
    ∀ i ≤ n, (mkCoeffTuple s n a).get s (coeffIdx s n i) = a i := by
  induction n generalizing a with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    rfl
  | succ n ih =>
    rintro (_ | i) hi
    · rfl
    · exact ih (fun i => a (i + 1)) i (Nat.succ_le_succ_iff.mp hi)

end Horner

/-! ### The theory of algebraically closed fields -/

/-- The axioms of the theory `ACF` of algebraically closed fields: the field axioms together
with, for each `n`, the statement that every monic polynomial of degree `n + 1` has a root. -/
inductive ACFAxiom : Type
  | field (ax : FieldAxiom)
  | root (n : ℕ)

namespace ACFAxiom

variable (L : Language.{u, v} S) (s : S)

/-- The sentence `∀ a₀ ⋯ aₙ, ∃ x, x ^ (n + 1) + ∑ i ≤ n, aᵢ xⁱ = 0`, in Horner form. The `n + 1`
coefficients are quantified over in one go, as the arity `coeffSig s n`. -/
@[simp]
def toSentence [RingL L s] : ACFAxiom → L.Sentence
  | field ax => ax.toSentence L s
  | root n => ∀' (coeffSig s n) (∃' s
      (hornerT (.var (.right .var)) n (fun i => .var (.left (.right (coeffIdx s n i)))) =' 0))

/-- The mathematical content of an ACF axiom. -/
@[simp]
def toProp (K : Type*) [Add K] [Mul K] [Neg K] [Zero K] [One K] : ACFAxiom → Prop
  | field ax => ax.toProp K
  | root n => ∀ a : ℕ → K, ∃ x : K, hornerVal x n a = 0

variable {L s} {M : S → Type w} [RingL L s] [L.Structure M]

theorem realize_toSentence_iff_toProp [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)]
    [One (M s)] [CompatibleRingL L M s] (ax : ACFAxiom) :
    M ⊨ ax.toSentence L s ↔ ax.toProp (M s) := by
  cases ax with
  | field ax => exact FieldAxiom.realize_toSentence_iff_toProp ax
  | root n =>
    simp only [toSentence, toProp, Sentence.realize_def, Formula.realize_all,
      Formula.realize_ex, Formula.realize_equal, realize_hornerT, Term.realize_var,
      Interpret.get_left, Interpret.get_right, Interpret.get_var, realize_zero]
    refine ⟨fun h a => ?_, fun h as => h _⟩
    obtain ⟨b, hb⟩ := h (mkCoeffTuple s n a)
    exact ⟨b, (hornerVal_congr b n fun i hi => get_mkCoeffTuple s n a i hi) ▸ hb⟩

end ACFAxiom

/-- The theory of algebraically closed fields on sort `s`. -/
def ACFTheory (L : Language.{u, v} S) (s : S) [RingL L s] : L.Theory :=
  Set.range (ACFAxiom.toSentence L s)

/-! ### The monic polynomial attached to a coefficient sequence -/

section MonicPoly

variable {K : Type*} [CommRing K]

/-- The monic polynomial `X ^ (n + 1) + ∑ i ≤ n, aᵢ Xⁱ`, whose roots are exactly the solutions
of `hornerVal x n a = 0`. -/
noncomputable def monicPolyOfCoeffs (n : ℕ) (a : ℕ → K) : Polynomial K :=
  Polynomial.X ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), Polynomial.C (a i) * Polynomial.X ^ i

@[simp]
theorem eval_monicPolyOfCoeffs (n : ℕ) (a : ℕ → K) (x : K) :
    (monicPolyOfCoeffs n a).eval x = hornerVal x n a := by
  rw [hornerVal_eq_monic, monicPolyOfCoeffs]
  simp [Polynomial.eval_finsetSum]

theorem degree_monicPolyOfCoeffs [Nontrivial K] (n : ℕ) (a : ℕ → K) :
    (monicPolyOfCoeffs n a).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
  have hle : (∑ i ∈ Finset.range (n + 1), Polynomial.C (a i) * Polynomial.X ^ i).degree
      ≤ (n : WithBot ℕ) := by
    refine le_trans (Polynomial.degree_sum_le _ _) (Finset.sup_le fun i hi => ?_)
    refine le_trans (Polynomial.degree_C_mul_X_pow_le i (a i)) ?_
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [monicPolyOfCoeffs, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact lt_of_le_of_lt hle (by exact_mod_cast Nat.lt_succ_self n)

end MonicPoly

/-! ### Algebraically closed fields are models -/

/-- An algebraically closed field is a model of `ACFTheory`. -/
theorem models_ACFTheory {L : Language.{u, v} S} {M : S → Type w} {s : S} [RingL L s]
    [L.Structure M] [Field (M s)] [IsAlgClosed (M s)] [CompatibleRingL L M s] :
    M ⊨ ACFTheory L s := by
  refine (Theory.model_iff _).2 ?_
  rintro φ ⟨ax, rfl⟩
  rw [ACFAxiom.realize_toSentence_iff_toProp]
  cases ax with
  | field ax =>
    exact (FieldAxiom.realize_toSentence_iff_toProp (L := L) ax).1 (FieldAxiom.models_ax ax)
  | root n =>
    intro a
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (k := M s) (monicPolyOfCoeffs n a) (by
      rw [degree_monicPolyOfCoeffs]
      exact_mod_cast Nat.succ_ne_zero n)
    exact ⟨x, by rwa [Polynomial.IsRoot.def, eval_monicPolyOfCoeffs] at hx⟩

/-! ### Models are algebraically closed fields -/

section ModelAlgebra

variable (L : Language.{u, v} S) (M : S → Type w) (s : S) [RingL L s] [L.Structure M]
  [M ⊨ ACFTheory L s]

/-- Any ACF axiom holds in a model of `ACFTheory`, phrased with the operations read off from the
structure. -/
theorem model_acf_toProp (ax : ACFAxiom) :
    letI := modelAdd L M s
    letI := modelMul L M s
    letI := modelNeg L M s
    letI := modelZero L M s
    letI := modelOne L M s
    ax.toProp (M s) := by
  let := modelAdd L M s
  let := modelMul L M s
  let := modelNeg L M s
  let := modelZero L M s
  let := modelOne L M s
  have := modelRingCompatible L M s
  exact (ACFAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem (T := ACFTheory L s) (Set.mem_range_self ax))

/-- Any field axiom holds in a model of `ACFTheory`, phrased with the read-off operations. -/
theorem model_field_toProp (ax : FieldAxiom) :
    letI := modelAdd L M s
    letI := modelMul L M s
    letI := modelNeg L M s
    letI := modelZero L M s
    letI := modelOne L M s
    ax.toProp (M s) :=
  model_acf_toProp L M s (.field ax)

/-- The additive commutative group structure on sort `s` of a model of `ACFTheory`. -/
@[reducible] noncomputable def modelACFAddCommGroup : AddCommGroup (M s) :=
  letI := modelAdd L M s
  letI := modelNeg L M s
  letI := modelZero L M s
  { add := (· + ·)
    add_assoc := model_field_toProp L M s (.cring (.ring (.add (.aGroup (.aMonoid .addAssoc)))))
    zero := 0
    zero_add := model_field_toProp L M s (.cring (.ring (.add (.aGroup (.aMonoid .zeroAdd)))))
    add_zero := model_field_toProp L M s (.cring (.ring (.add (.aGroup (.aMonoid .addZero)))))
    nsmul := nsmulRec
    neg := Neg.neg
    zsmul := zsmulRec
    neg_add_cancel := model_field_toProp L M s (.cring (.ring (.add (.aGroup .negAddCancel))))
    add_comm := model_field_toProp L M s (.cring (.ring (.add .addComm))) }

/-- `0 * a = 0` in a model of `ACFTheory`, by right distributivity and cancellation. -/
theorem model_zero_mul :
    letI := modelACFAddCommGroup L M s
    letI := modelMul L M s
    ∀ a : M s, 0 * a = 0 := by
  let := modelACFAddCommGroup L M s
  let := modelMul L M s
  intro a
  have h := model_field_toProp L M s (.cring (.ring .rightDistrib)) 0 0 a
  rw [add_zero] at h
  exact (add_left_cancel (a := (0 : M s) * a) (b := 0) (by rw [add_zero]; exact h)).symm

/-- `a * 0 = 0` in a model of `ACFTheory`, by left distributivity. -/
theorem model_mul_zero :
    letI := modelACFAddCommGroup L M s
    letI := modelMul L M s
    ∀ a : M s, a * 0 = 0 := by
  let := modelACFAddCommGroup L M s
  let := modelMul L M s
  intro a
  have h := model_field_toProp L M s (.cring (.ring .leftDistrib)) a 0 0
  rw [add_zero] at h
  exact (add_left_cancel (a := a * (0 : M s)) (b := 0) (by rw [add_zero]; exact h)).symm

/-- The commutative ring structure on sort `s` of a model of `ACFTheory`. -/
@[reducible] noncomputable def modelCommRing : CommRing (M s) :=
  letI := modelACFAddCommGroup L M s
  letI := modelMul L M s
  letI := modelOne L M s
  { add := (· + ·)
    add_assoc := add_assoc
    zero := 0
    zero_add := zero_add
    add_zero := add_zero
    nsmul := nsmulRec
    neg := Neg.neg
    zsmul := zsmulRec
    neg_add_cancel := neg_add_cancel
    add_comm := add_comm
    mul := (· * ·)
    mul_assoc := model_field_toProp L M s (.cring (.ring (.mul .mulAssoc)))
    one := 1
    one_mul := model_field_toProp L M s (.cring (.ring (.mul .oneMul)))
    mul_one := model_field_toProp L M s (.cring (.ring (.mul .mulOne)))
    left_distrib := model_field_toProp L M s (.cring (.ring .leftDistrib))
    right_distrib := model_field_toProp L M s (.cring (.ring .rightDistrib))
    zero_mul := model_zero_mul L M s
    mul_zero := model_mul_zero L M s
    mul_comm := model_field_toProp L M s (.cring .mulComm) }

/-- A model of `ACFTheory` is a field on sort `s`. -/
theorem modelIsField :
    letI := modelCommRing L M s
    IsField (M s) := by
  let := modelCommRing L M s
  exact { exists_pair_ne := model_field_toProp L M s .existsPairNe
          mul_comm := mul_comm
          mul_inv_cancel := fun {a} ha => model_field_toProp L M s .existsInv a ha }

/-- The field structure on sort `s` of a model of `ACFTheory`. -/
@[reducible] noncomputable def modelField : Field (M s) :=
  letI := modelCommRing L M s
  (modelIsField L M s).toField

/-- The structure is compatible with the derived field structure. -/
theorem modelFieldCompatible :
    letI := modelField L M s
    CompatibleRingL L M s := by
  let := modelField L M s
  exact { funMap_add := fun _ => rfl, funMap_mul := fun _ => rfl, funMap_neg := fun _ => rfl,
          funMap_zero := rfl, funMap_one := rfl }

/-- A model of `ACFTheory` is algebraically closed on sort `s`. -/
theorem modelIsAlgClosed :
    letI := modelField L M s
    IsAlgClosed (M s) := by
  let := modelCommRing L M s
  let := modelField L M s
  refine IsAlgClosed.of_exists_root (k := M s) (fun p hmonic hirr => ?_)
  obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n + 1 := by
    refine ⟨p.natDegree - 1, ?_⟩
    have hne : p.natDegree ≠ 0 := fun h =>
      hirr.not_isUnit (by rw [hmonic.natDegree_eq_zero.mp h]; exact isUnit_one)
    omega
  obtain ⟨x, hx⟩ := model_acf_toProp L M s (.root n) (fun i => p.coeff i)
  refine ⟨x, ?_⟩
  rw [hornerVal_eq_monic] at hx
  rw [Polynomial.eval_eq_sum_range, hn, Finset.sum_range_succ, ← hn,
    Polynomial.coeff_natDegree, hmonic.leadingCoeff, one_mul, hn, add_comm]
  exact hx

end ModelAlgebra

end ManySorted.Language
