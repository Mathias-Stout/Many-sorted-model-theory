import MultisortedLogic.Examples.Ring
import MultisortedLogic.Bundled
import Mathlib.RingTheory.FreeCommRing


namespace MSFirstOrder
open Language Term Theory

universe u v w z u' v' w' z'
variable {Sorts : Type z}
variable {L : Language.{u, v, z} Sorts}
--variable {M : Fam.{w} Sorts}
variable {α : Fam.{u'} Sorts}
variable {σ : Signature Sorts}
variable {s : Sorts}

section RingL

/-- "The ring language on a sort s" -/
inductive ringFunc (s : Sorts) : Signature Sorts → Sorts → Type
  | add : ringFunc s (⦃s⦄ ⨯ ⦃s⦄) s
  | mul : ringFunc s (⦃s⦄ ⨯ ⦃s⦄) s
  | neg : ringFunc s ⦃s⦄ s
  | zero : ringFunc s ⦃⦄ s
  | one : ringFunc s ⦃⦄ s
  deriving DecidableEq

/-- The language of rings contains the operations (+,*,-,0,1) -/
def Language.ring (s : Sorts) : Language.{0, 0, z} Sorts:=
  { Functions := ringFunc s
    Relations := fun _ => Empty }
  deriving Language.IsAlgebraic

open Language

--TOOD: move these lemmas to syntax, replace
lemma Term.size_lt_func {f : L.Functions σ s} {ts : L.Term α σ} :
    ts.size < (func f ts).size := by
  simp only [size, lt_add_iff_pos_left, Order.lt_two_iff, zero_le]

lemma Term.size_lt_prod_left {ξ : Signature Sorts} {t₁ : L.Term α σ} {t₂ : L.Term α ξ} :
    t₁.size < (t₁.prod t₂).size := by
  rw [Term.size]
  linarith

lemma Term.size_lt_prod_right {ξ : Signature Sorts} {t₁ : L.Term α σ} {t₂ : L.Term α ξ} :
    t₂.size < (t₁.prod t₂).size := by
  rw [Term.size]
  linarith


instance instRingL : RingL (ring s) s where
    addFunc   := .add
    mulFunc   := .mul
    negFunc   := .neg
    zeroConst := .zero
    oneConst  := .one

end RingL

/-
Every polynomial over `ℤ` in variables `α s` defines a term that is equal to its interpretation
-/
theorem exists_term_realize_eq_freeCommRing
    [RingL L s]
    (p : FreeCommRing (α s)) :
    ∃ t : L.Term α ⦃s⦄, ∀ (M : Fam.{w} Sorts)
    [CommRing (M s)] [L.Structure M] [CompatibleRingL L M s]
    (v : α →ₛ M), t.realize v = FreeCommRing.lift (v s) p := by
  induction p with
  | neg_one =>
      use -1
      intros
      simp only [CompatibleNegL.realize_neg, CompatibleOneL.realize_one, map_neg, map_one]
  | of a =>
      use Term.var s a
      intros
      simp only [realize_var, FreeCommRing.lift_of]
  | add a b ha hb =>
      obtain ⟨ta, hta⟩ := ha
      obtain ⟨tb, htb⟩ := hb
      use ta + tb
      intros
      simp only [CompatibleAddL.realize_add, hta, htb, map_add]
  | mul a b ha hb =>
      obtain ⟨ta, hta⟩ := ha
      obtain ⟨tb, htb⟩ := hb
      use ta * tb
      intros
      simp only [CompatibleMulL.realize_mul, hta, htb, map_mul]


/-- Make a `Language.ring.Term α` from an element of `FreeCommRing α` -/
noncomputable def termOfFreeCommRing
  (M : Fam.{w} Sorts)
  [RingL L s] [L.Structure M] [CommRing (M s)] [CompatibleRingL L M s] (p : FreeCommRing (α s)) :
  L.Term α ⦃s⦄ := Classical.choose (exists_term_realize_eq_freeCommRing.{u, v, w, z, u'} p)


/-  Terms in the pure ring language can be represented by polynomials
 -/
noncomputable def polynomial_ofTerm {s : Sorts} {σ : Signature Sorts} (hσ : σ.OneSort s) :
    (Term.{0, 0, z, u'} (Language.ring s) α σ) →
      ⟨fun s ↦ MvPolynomial (α s) ℤ⟩ [^] σ
  | nil => PUnit.unit
  | var s' v => MvPolynomial.X v
  | func ringFunc.zero _ => (0 : MvPolynomial _ _)
  | func ringFunc.one _ => (1 : MvPolynomial _ _)
  | func ringFunc.neg t => (-1 : MvPolynomial _ _) * polynomial_ofTerm hσ t
  | func ringFunc.add (Term.prod t₁ t₂) =>
    (1 : MvPolynomial _ _) * polynomial_ofTerm hσ t₁ + polynomial_ofTerm hσ t₂
  | func ringFunc.mul (Term.prod t₁ t₂) =>
    (1 : MvPolynomial _ _) * polynomial_ofTerm hσ t₁ * polynomial_ofTerm hσ t₂
  | prod t₁ t₂ => ⟨polynomial_ofTerm hσ.prodl t₁, polynomial_ofTerm hσ.prodr t₂⟩

-- Should lift go to Signature.lean?
def lift {M : Fam.{u} Sorts} {N : Fam.{u'} Sorts} (f : M s → N s) :
    {σ : Signature Sorts} → (hσ : σ.OneSort s) → M [^] σ → N [^] σ
  | Signature.nil => fun _ _ ↦ PUnit.unit
  | Signature.of _ =>
    fun hσ ↦ hσ.of_in ▸ f
  | Signature.prod _ _ => fun hσ ↦ Prod.map (lift f hσ.prodl) (lift f hσ.prodr)


theorem polynomial_ofTerm_eval {M : Fam.{w} Sorts} [(ring s).Structure M]
    [ringstruc : CommRing (M s)] [compat : CompatibleRingL (Language.ring s) M s]
    {σ : Signature Sorts} (hσ : σ.OneSort s) (t : Term.{0, 0, z, u'} (Language.ring s) α σ)
    (v : α →ₛ M) :
  t.realize v = lift (MvPolynomial.eval₂ (Int.castRingHom (M s)) (v s)) hσ (polynomial_ofTerm hσ t)
  := by
    induction t with
    | nil =>
      rfl
    | @var s' a =>
      cases hσ
      simp [lift, polynomial_ofTerm]
    | func f ts hts =>
      cases f <;> cases ts
      · rename_i a b
        simp only [lift, polynomial_ofTerm, one_mul]
        change Structure.funMap (L := ring s)
          (ringFunc.add : (ring s).Functions (⦃s⦄ ⨯ ⦃s⦄) s) (Term.realize v (a.prod b)) = _
        erw [compat.add_eq]
        rw [MvPolynomial.eval₂_add, hts (Signature.OneSort.prod hσ hσ)]
        rfl
      · rename_i a b
        simp only [lift, polynomial_ofTerm, one_mul]
        change Structure.funMap (L := ring s)
          (ringFunc.mul : (ring s).Functions (⦃s⦄ ⨯ ⦃s⦄) s) (Term.realize v (a.prod b)) = _
        erw [compat.mul_eq]
        rw [MvPolynomial.eval₂_mul, hts (Signature.OneSort.prod hσ hσ)]
        rfl
      · rename_i a
        simp only [lift, polynomial_ofTerm, neg_mul, one_mul,
          MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X]
        change Structure.funMap (L := ring s)
          (ringFunc.neg : (ring s).Functions ⦃s⦄ s) (Term.realize v (Term.var s a)) = _
        erw [compat.neg_eq]
        rfl
      · rename_i σ' r f
        simp only [lift, polynomial_ofTerm, neg_mul, one_mul, MvPolynomial.eval₂_neg]
        change Structure.funMap (L := ring s)
          (ringFunc.neg : (ring s).Functions ⦃s⦄ s) (Term.realize v (Term.func f r)) = _
        rw [hts hσ]
        simp only [lift]
        erw [compat.neg_eq]
      · simp only [realize_func, lift, polynomial_ofTerm, MvPolynomial.eval₂_zero, ←compat.zero_eq]
        rfl
      · simp only [realize_func, lift, polynomial_ofTerm, MvPolynomial.eval₂_one, ←compat.one_eq]
        rfl
    | prod _ _ ht₁ ht₂ =>
      apply Prod.ext
      · simp only [realize_prod, lift, polynomial_ofTerm, Prod.map_apply]
        rw [ht₁]
      · simp only [realize_prod, lift, polynomial_ofTerm, Prod.map_apply]
        rw [ht₂]

/-
theorem exists_term_realize_eq_freeCommRing (p : FreeCommRing (α s)) :
    ∃ t : L.Term α (.of s), ∀
      (t.realize FreeCommRing.of : FreeCommRing (α s)) = p :=
  FreeCommRing.induction_on p
    ⟨-1, by simp?⟩
    (fun a => ⟨Term.var a, by simp? [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all?⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all?⟩)

-/
end MSFirstOrder
