/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Jonas van der Schaaf
-/
module

public import MultisortedLogic.Algebra.ACF.Basic
public import MultisortedLogic.AlgebraicBackground.Field
public import MultisortedLogic.Separation
public import MultisortedLogic.RealizingTypes
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Quantifier elimination for algebraically closed fields

Quantifier elimination for the one-sorted theory `ACF` of algebraically closed fields in the
language of rings. The theory itself, and the correspondence between its models and algebraically
closed fields, are in `Algebra/ACF/Basic.lean`.

## Main results

* `ACF_hasQERelTo_empty`: the one-sorted theory of algebraically closed fields eliminates
  quantifiers.

## Implementation notes

The `ℤ`-polynomials in the variables of a tuple of shape `σ` are `MvPolynomial (σ.Idx ()) ℤ`. The
polynomial of a term is its value in this polynomial ring (`polyOfTerm`), and the dictionary
`realize_eq_evalHom` between terms and polynomials is `HomClass.realize_term` applied to
evaluation, seen as a homomorphism of structures (`homOfRingHom`).

Quantifier elimination goes through the pointed tuple-extension criterion
`Theory.hasQERelTo_of_pointed_extension`. Tuples `x` in `M` and `y` in `N` with the same
quantifier-free type generate a common field `F` (`acf_algebraize`). Given `b` in `M`, if `b` is
algebraic over `F`, then a root in `N` of its minimal polynomial matches it. Otherwise, the type
over `y` saying that `t(y, X) ≠ 0` for every term `t` whose polynomial is nonzero over `F` is
finitely satisfiable in `N`, which is infinite. It is realized next to a tuple with the same
complete type as `y` (`Formula.exists_realize_of_finite`).
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

/-! ### Quantifier elimination for ACF -/

section ACFQE

/-- The language of rings over the one-point sort type. -/
abbrev ringU : Language.{0, 0} Unit := Language.ring ()

/-- The one-sorted theory of algebraically closed fields. -/
abbrev ACF : ringU.Theory := ACFTheory ringU ()

/-- A commutative ring is a structure for the language of rings. -/
instance ringStructure (R : Type*) [CommRing R] : ringU.Structure (fun _ => R) where
  funMap
    | .add, x => x.1 + x.2
    | .mul, x => x.1 * x.2
    | .neg, x => -x
    | .zero, _ => 0
    | .one, _ => 1
  RelMap r := Empty.elim r

instance (R : Type*) [CommRing R] : CompatibleRingL ringU (fun _ => R) () where
  funMap_add _ := rfl
  funMap_mul _ := rfl
  funMap_neg _ := rfl
  funMap_zero := rfl
  funMap_one := rfl

variable {σ : Arity Unit}

/-- The ring of `ℤ`-polynomials in the positions of `σ`. -/
abbrev polyRing (σ : Arity Unit) : Type := MvPolynomial (σ.Idx ()) ℤ

/-- Evaluation of `ℤ`-polynomials in the positions of `σ` at a tuple. -/
noncomputable def evalHom (M : Unit → Type) [CommRing (M ())] (x : M [^] σ) :
    polyRing σ →+* M () :=
  MvPolynomial.eval₂Hom (Int.castRingHom (M ())) (x.get ())

/-- The `ℤ`-polynomial of a term: its value in the polynomial ring, at the variables. -/
noncomputable def polyOfTerm (t : ringU.Term σ ⦃()⦄) : polyRing σ :=
  t.realize (M := fun _ => polyRing σ) (Interpret.ofFn fun _ i => MvPolynomial.X i)

/-! ### Peeling off the last variable

A `ℤ`-polynomial in the positions of `σ ⨯ ⦃()⦄` is a one-variable polynomial over the
`ℤ`-polynomials in the positions of `σ`. -/

/-- The images of the positions of `σ ⨯ ⦃()⦄`: a position of `σ` becomes a constant, the last
position becomes `X`. -/
noncomputable def peelVar : (σ ⨯ ⦃()⦄).Idx () → Polynomial (polyRing σ)
  | .left i => Polynomial.C (MvPolynomial.X i)
  | .right _ => Polynomial.X

/-- **Peeling off the last variable**: `ℤ[σ, x] → ℤ[σ][X]`. -/
noncomputable def peelPoly : polyRing (σ ⨯ ⦃()⦄) →+* Polynomial (polyRing σ) :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) peelVar

/-- Evaluating at `(x, b)` means evaluating the peeled one-variable polynomial at `b`, with
coefficients evaluated at `x`. -/
theorem evalHom_prod_eq_eval_peel (M : Unit → Type) [CommRing (M ())] (x : M [^] σ) (b : M ())
    (p : polyRing (σ ⨯ ⦃()⦄)) :
    evalHom M ((x, b) : M [^] (σ ⨯ ⦃()⦄)) p =
      Polynomial.eval b ((peelPoly p).map (evalHom M x)) := by
  have key : evalHom M ((x, b) : M [^] (σ ⨯ ⦃()⦄)) =
      (Polynomial.evalRingHom b).comp ((Polynomial.mapRingHom (evalHom M x)).comp peelPoly) := by
    refine MvPolynomial.ringHom_ext (fun n => by simp [evalHom, peelPoly]) (fun i => ?_)
    cases i with
    | left i => simp [evalHom, peelPoly, peelVar]
    | right j => cases j; simp [evalHom, peelPoly, peelVar]
  exact RingHom.congr_fun key p

/-- **The polynomial-to-field bridge**: if the evaluation at `x` factors through a field `F`,
then the polynomial condition at `(x, b)` is the vanishing of an `F`-polynomial at `b`. -/
theorem evalHom_prod_eq_aeval (M : Unit → Type) [CommRing (M ())] {F : Type} [Field F]
    [Algebra F (M ())]
    (x : M [^] σ) (b : M ()) (toF : polyRing σ →+* F)
    (hf : ∀ p, algebraMap F (M ()) (toF p) = evalHom M x p) (p : polyRing (σ ⨯ ⦃()⦄)) :
    evalHom M ((x, b) : M [^] (σ ⨯ ⦃()⦄)) p = Polynomial.aeval b ((peelPoly p).map toF) := by
  rw [evalHom_prod_eq_eval_peel]
  have hcomp : (algebraMap F (M ())).comp toF = evalHom M x :=
    RingHom.ext (fun p => by rw [RingHom.comp_apply]; exact hf p)
  rw [← hcomp, ← Polynomial.map_map, Polynomial.eval_map, ← Polynomial.aeval_def]

/-! ### Rings as structures for the language of rings -/

section Rings

variable {M N : Unit → Type} [ringU.Structure M] [ringU.Structure N] [CommRing (M ())]
  [CommRing (N ())] [CompatibleRingL ringU M ()] [CompatibleRingL ringU N ()]

/-- A ring homomorphism is a homomorphism of structures for the language of rings. -/
def homOfRingHom (f : M () →+* N ()) : M →[ringU] N where
  toFun _ := f
  map_fun' g x := by
    cases g
    · change f (funMap (L := ringU) AddL.addFunc x) = funMap (L := ringU) AddL.addFunc _
      simp
    · change f (funMap (L := ringU) MulL.mulFunc x) = funMap (L := ringU) MulL.mulFunc _
      simp
    · change f (funMap (L := ringU) NegL.negFunc x) = funMap (L := ringU) NegL.negFunc _
      simp
    · change f (funMap (L := ringU) (M := M) ZeroL.zeroConst x) =
        funMap (L := ringU) (M := N) ZeroL.zeroConst _
      cases x
      simp [Interpret.map]
    · change f (funMap (L := ringU) (M := M) OneL.oneConst x) =
        funMap (L := ringU) (M := N) OneL.oneConst _
      cases x
      simp [Interpret.map]
  map_rel' r := Empty.elim r

@[simp]
theorem homOfRingHom_apply (f : M () →+* N ()) (a : M ()) : homOfRingHom f () a = f a :=
  rfl

/-- A homomorphism of structures for the language of rings is a ring homomorphism. -/
def ringHomOfHom {F : Type*} [DFunLike F Unit fun s => M s → N s] [HomClass ringU F M N]
    (e : F) : M () →+* N () where
  toFun := e ()
  map_one' := by
    simpa [Interpret.map] using HomClass.map_fun e (OneL.oneConst (L := ringU) (s := ())) PUnit.unit
  map_mul' a b := by
    simpa using HomClass.map_fun e (MulL.mulFunc (L := ringU) (s := ()))
      ((a, b) : M [^] (⦃()⦄ ⨯ ⦃()⦄))
  map_zero' := by
    simpa [Interpret.map] using
      HomClass.map_fun e (ZeroL.zeroConst (L := ringU) (s := ())) PUnit.unit
  map_add' a b := by
    simpa using HomClass.map_fun e (AddL.addFunc (L := ringU) (s := ()))
      ((a, b) : M [^] (⦃()⦄ ⨯ ⦃()⦄))

@[simp]
theorem ringHomOfHom_apply {F : Type*} [DFunLike F Unit fun s => M s → N s]
    [HomClass ringU F M N] (e : F) (a : M ()) : ringHomOfHom e a = e () a :=
  rfl

variable (M N) in
/-- Every term of sort `()` realizes as the value of its polynomial. -/
theorem realize_eq_evalHom (x : M [^] σ) (t : ringU.Term σ ⦃()⦄) :
    t.realize x = evalHom M x (polyOfTerm t) := by
  have h := HomClass.realize_term (homOfRingHom (evalHom M x))
    (Interpret.ofFn fun _ i => MvPolynomial.X i : (fun _ => polyRing σ) [^] σ) t
  have hx : (Interpret.ofFn fun _ i => MvPolynomial.X i : (fun _ => polyRing σ) [^] σ).map
      (homOfRingHom (evalHom M x)) = x :=
    Interpret.ext fun s i => by cases s; simp [evalHom]
  rw [hx] at h
  exact h

/-- Every `ℤ`-polynomial is the polynomial of a term. -/
theorem exists_polyOfTerm_eq (p : polyRing σ) : ∃ t : ringU.Term σ ⦃()⦄, polyOfTerm t = p := by
  induction p using MvPolynomial.induction_on with
  | C k => exact ⟨intCastT k, by simp [polyOfTerm, eq_intCast]⟩
  | add p q hp hq =>
    obtain ⟨tp, rfl⟩ := hp
    obtain ⟨tq, rfl⟩ := hq
    exact ⟨tp +ₗ tq, by simp [polyOfTerm]⟩
  | mul_X p i hp =>
    obtain ⟨tp, rfl⟩ := hp
    exact ⟨tp *ₗ .var i, by simp [polyOfTerm]⟩

variable (M N) in
/-- **Same quantifier-free type means same polynomial relations**: tuples with the same
quantifier-free type are annihilated by exactly the same `ℤ`-polynomials. -/
theorem ker_evalHom_eq_of_tpEq (x : M [^] σ) (y : N [^] σ)
    (htp : Formula.typeOf (FormulaClass.qfRelTo ringU ∅ σ) x =
      Formula.typeOf (FormulaClass.qfRelTo ringU ∅ σ) y) :
    RingHom.ker (evalHom M x) = RingHom.ker (evalHom N y) := by
  ext p
  obtain ⟨t, rfl⟩ := exists_polyOfTerm_eq p
  have h := Formula.realize_iff_of_typeOf_eq htp (ψ := t =' 0)
    (Formula.IsQFRelTo.of_isAtomic (.equal _ _))
  rw [Formula.realize_equal, Formula.realize_equal, realize_zero, realize_zero,
    realize_eq_evalHom, realize_eq_evalHom] at h
  rw [RingHom.mem_ker, RingHom.mem_ker, h]

/-- Evaluating polynomials at a tuple commutes with homomorphisms. -/
theorem evalHom_map {F : Type*} [DFunLike F Unit fun s => M s → N s] [HomClass ringU F M N]
    (e : F) (x : M [^] σ) (p : polyRing σ) :
    evalHom N (x.map e) p = ringHomOfHom e (evalHom M x p) := by
  have key : evalHom N (x.map e) = (ringHomOfHom e).comp (evalHom M x) :=
    MvPolynomial.ringHom_ext (fun n => by simp [evalHom]) (fun i => by simp [evalHom])
  rw [key, RingHom.comp_apply]

variable (M N) in
/-- **The quantifier-free transfer step**: if `x` and `y` are annihilated by exactly the same
`ℤ`-polynomials, then they have the same quantifier-free type. The language of rings has no
relation symbols, so atomic formulas are equations between tuples of terms, which reduce entry by
entry to polynomial identities. -/
theorem acf_qf_transfer_of_key {Γ : Arity Unit} (x : M [^] Γ) (y : N [^] Γ)
    (key : ∀ p : polyRing Γ, evalHom M x p = 0 ↔ evalHom N y p = 0) :
    Formula.typeOf (FormulaClass.qfRelTo ringU ∅ Γ) x =
      Formula.typeOf (FormulaClass.qfRelTo ringU ∅ Γ) y := by
  refine Formula.typeOf_eq_typeOf_iff.2 fun φ hφ =>
    Formula.realize_iff_of_isQFRelTo_empty hφ x y fun ψ hψ => ?_
  cases hψ with
  | equal t₁ t₂ =>
    simp only [Formula.realize_equal, Interpret.ext_iff, ← Term.realize_get]
    refine forall_congr' fun s => forall_congr' fun i => ?_
    cases s
    rw [realize_eq_evalHom, realize_eq_evalHom, realize_eq_evalHom, realize_eq_evalHom,
      ← sub_eq_zero, ← map_sub, key, map_sub, sub_eq_zero]
  | rel r _ => exact Empty.elim r

end Rings

/-- **Algebraization**: tuples `x` and `y` with the same quantifier-free type generate a common
field `F`, the field of rational functions in the tuple, embedding into both models compatibly
with evaluation of polynomials at the tuples. -/
theorem acf_algebraize (M N : Unit → Type) [ringU.Structure M] [ringU.Structure N]
    [Field (M ())] [Field (N ())] [CompatibleRingL ringU M ()] [CompatibleRingL ringU N ()]
    (x : M [^] σ) (y : N [^] σ)
    (htp : Formula.typeOf (FormulaClass.qfRelTo ringU ∅ σ) x =
      Formula.typeOf (FormulaClass.qfRelTo ringU ∅ σ) y) :
    ∃ (F : Type) (_ : Field F) (fM : F →+* M ()) (fN : F →+* N ()) (toF : polyRing σ →+* F),
      Function.Injective fM ∧ Function.Injective fN ∧
      (∀ p, fM (toF p) = evalHom M x p) ∧ (∀ p, fN (toF p) = evalHom N y p) := by
  classical
  have hker : RingHom.ker (evalHom M x) = RingHom.ker (evalHom N y) :=
    ker_evalHom_eq_of_tpEq M N x y htp
  have : (RingHom.ker (evalHom M x)).IsPrime := RingHom.ker_isPrime _
  let : IsDomain (polyRing σ ⧸ RingHom.ker (evalHom M x)) := Ideal.Quotient.isDomain _
  have hMinj : Function.Injective (RingHom.kerLift (evalHom M x)) :=
    RingHom.kerLift_injective _
  have hNinj : Function.Injective
      ((RingHom.kerLift (evalHom N y)).comp (Ideal.quotEquivOfEq hker).toRingHom) := by
    simp only [RingHom.coe_comp]
    exact (RingHom.kerLift_injective _).comp (Ideal.quotEquivOfEq hker).injective
  refine ⟨FractionRing (polyRing σ ⧸ RingHom.ker (evalHom M x)), inferInstance,
    IsFractionRing.lift hMinj, IsFractionRing.lift hNinj,
    (algebraMap _ _).comp (Ideal.Quotient.mk (RingHom.ker (evalHom M x))),
    RingHom.injective _, RingHom.injective _, fun p => ?_, fun p => ?_⟩
  · rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]
  · rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
    change (evalHom N y).kerLift
      (Ideal.quotEquivOfEq hker (Ideal.Quotient.mk (RingHom.ker (evalHom M x)) p)) = evalHom N y p
    rw [Ideal.quotEquivOfEq_mk, RingHom.kerLift_mk]

/-- **The extension step for ACF**: given models `M`, `N`, tuples `x`, `y` with the same
quantifier-free type, and `b : M`, there are a structure `N'`, a tuple `y'` with the same
complete type as `y` and an element `c` such that `(x, b)` and `(y', c)` have the same
quantifier-free type. -/
theorem acf_tuple_ext (M N : Unit → Type) [ringU.Structure M] [ringU.Structure N]
    [∀ s, Nonempty (N s)] [M ⊨ ACF] [N ⊨ ACF] (σ : Arity Unit) (x : M [^] σ) (y : N [^] σ)
    (htp : Formula.typeOf (FormulaClass.qfRelTo ringU ∅ σ) x =
      Formula.typeOf (FormulaClass.qfRelTo ringU ∅ σ) y) (b : M ()) :
    ∃ (N' : Unit → Type) (_ : ringU.Structure N') (y' : N' [^] σ) (c : N' ()),
      Formula.typeOf (FormulaClass.all ringU σ) y' = Formula.typeOf (FormulaClass.all ringU σ) y ∧
      Formula.typeOf (FormulaClass.qfRelTo ringU ∅ (σ ⨯ ⦃()⦄)) ((x, b) : M [^] (σ ⨯ ⦃()⦄)) =
        Formula.typeOf (FormulaClass.qfRelTo ringU ∅ (σ ⨯ ⦃()⦄)) ((y', c) : N' [^] (σ ⨯ ⦃()⦄)) := by
  classical
  let := modelField ringU M ()
  let := modelField ringU N ()
  have := modelFieldCompatible ringU M ()
  have := modelFieldCompatible ringU N ()
  have := modelIsAlgClosed ringU N ()
  obtain ⟨F, _, fM, fN, toF, -, -, hfM, hfN⟩ := acf_algebraize M N x y htp
  let : Algebra F (M ()) := fM.toAlgebra
  let : Algebra F (N ()) := fN.toAlgebra
  by_cases hb : IsAlgebraic F b
  · -- **Algebraic case**: a root of the minimal polynomial of `b` already lies in `N`.
    obtain ⟨c, hc⟩ := hb.exists_aeval_eq_zero_iff (L := N ())
    refine ⟨N, inferInstance, y, c, rfl, acf_qf_transfer_of_key M N _ _ fun p => ?_⟩
    rw [evalHom_prod_eq_aeval M x b toF hfM, evalHom_prod_eq_aeval N y c toF hfN]
    exact hc _
  · -- **Transcendental case**: the type over `y` saying that `t(y, X) ≠ 0` for every term `t`
    -- whose polynomial is nonzero over `F`.
    let P : Set (ringU.Formula (σ ⨯ ⦃()⦄)) :=
      {φ | ∃ t, (peelPoly (polyOfTerm t)).map toF ≠ 0 ∧ φ = ∼(t =' 0)}
    obtain ⟨N', _, y', c, hy', hc⟩ := Formula.exists_realize_of_finite y P fun P₀ hP₀ => by
      choose t ht0 hteq using fun φ : P₀ => hP₀ φ.2
      obtain ⟨c₀, hc₀⟩ := exists_forall_aeval_ne_zero (L := N ())
        (P₀.attach.image fun φ => (peelPoly (polyOfTerm (t φ))).map toF) (by
          intro q hq
          obtain ⟨φ, _, rfl⟩ := Finset.mem_image.1 hq
          exact ht0 φ)
      refine ⟨c₀, fun φ hφ => ?_⟩
      have hform : φ = ∼(t ⟨φ, hφ⟩ =' 0) := hteq ⟨φ, hφ⟩
      rw [hform, Formula.realize_not, Formula.realize_equal, realize_zero, realize_eq_evalHom,
        evalHom_prod_eq_aeval N y c₀ toF hfN]
      exact hc₀ _ (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
    -- `y'` has the complete type of `y`: `N'` is a model of `ACF`, and the polynomials vanishing
    -- at `y'` are those vanishing at `y`.
    have : N' ⊨ ACF := ⟨fun θ hθ => (Sentence.realize_lift θ y').1
      ((Formula.realize_iff_of_typeOf_eq hy' (Set.mem_univ (Sentence.lift θ))).2
        ((Sentence.realize_lift θ y).2 (Theory.realize_sentence_of_mem hθ)))⟩
    let := modelField ringU N' ()
    have := modelFieldCompatible ringU N' ()
    have hker := ker_evalHom_eq_of_tpEq N' N y' y
      (Formula.typeOf_eq_typeOf_of_subset (fun _ _ => Set.mem_univ _) hy')
    -- A polynomial whose peeled form vanishes over `F` vanishes at `(y', c)`.
    have hzero : ∀ p : polyRing (σ ⨯ ⦃()⦄), (peelPoly p).map toF = 0 →
        evalHom N' ((y', c) : N' [^] (σ ⨯ ⦃()⦄)) p = 0 := by
      intro p hp
      have hN : (peelPoly p).map (evalHom N y) = 0 := by
        rw [← show fN.comp toF = evalHom N y from RingHom.ext hfN, ← Polynomial.map_map, hp,
          Polynomial.map_zero]
      have hN' : (peelPoly p).map (evalHom N' y') = 0 := by
        ext n
        have := congrArg (AddMonoidAlgebra.coeff · n) hN
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this ⊢
        rw [← RingHom.mem_ker, hker, RingHom.mem_ker]
        exact this
      rw [evalHom_prod_eq_eval_peel, hN', Polynomial.eval_zero]
    refine ⟨N', inferInstance, y', c, hy', acf_qf_transfer_of_key M N' _ _ fun p => ?_⟩
    rw [evalHom_prod_eq_aeval M x b toF hfM]
    by_cases hq : (peelPoly p).map toF = 0
    · rw [hq, map_zero]
      exact ⟨fun _ => hzero p hq, fun _ => rfl⟩
    · obtain ⟨t, rfl⟩ := exists_polyOfTerm_eq p
      have ht := hc _ ⟨t, hq, rfl⟩
      rw [Formula.realize_not, Formula.realize_equal, realize_zero, realize_eq_evalHom] at ht
      exact iff_of_false (fun h => hb ⟨_, hq, h⟩) ht

/-- **Quantifier elimination for ACF**: the one-sorted theory of algebraically closed fields
eliminates quantifiers. -/
theorem ACF_hasQERelTo_empty : ACF.HasQERelTo (∅ : Set Unit) :=
  Theory.hasQERelTo_of_pointed_extension fun σ r r' htp _ _ b =>
    acf_tuple_ext r.carrier r'.carrier σ r.xs r'.xs htp b

end ACFQE

end ManySorted.Language
