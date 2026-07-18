/-
Based on the corresponding Mathlib file by Aaron Anderson
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MultisortedLogic.ElementarySubstructures
import MultisortedLogic.Encoding

/-!
# Skolem Functions and Downward Löwenheim–Skolem (Many-Sorted)

## Main Definitions

- `MSFirstOrder.Language.skolem₁` is a language consisting of Skolem functions for another
  language.

## Main Results

- `MSFirstOrder.Language.exists_elementarySubstructure_card_eq` is the Downward Löwenheim–Skolem
  theorem: If `s` is a family of sets in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (#(Σ s, A s), L.card) ≤ κ` and `κ ≤ #(Σ s, M s)`, then `M` has an elementary substructure
  containing `A` of cardinality `κ` in each sort.

## TODO

- Use `skolem₁` recursively to construct an actual Skolemization of a language.
-/

universe u u' v z w w'

namespace MSFirstOrder

namespace Language

open Structure Cardinal Signature Interpret

variable {Sorts : Type z}
variable (L : Language.{u, v, z} Sorts) {M : Fam.{w} Sorts}
  [L.Structure M] [∀ s, Nonempty (M s)]

/-- A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a language.
For each bounded formula `φ` with bound variables of signature `σ.prod (.of s)`, we add
a function symbol of arity `σ` returning sort `s`, which will be interpreted as a Skolem
function witnessing the existential quantifier over sort `s`. -/
@[simps]
def skolem₁ : Language Sorts :=
  ⟨fun σ s => L.BoundedFormula Fam.EmptyFam (σ.prod (.of s)), fun _ => Empty⟩

variable {L}

/-- The structure assigning each function symbol of `L.skolem₁` to a Skolem function generated with
choice. -/
noncomputable instance skolem₁Structure : L.skolem₁.Structure M :=
  ⟨fun {_σ _s} φ x => Classical.epsilon fun a => φ.Realize default ⟨x, a⟩,
   fun {_} r => Empty.elim r⟩

/-! ## Cardinality Lemmas for Skolem Languages

The cardinality bounds for the Skolem language require careful universe management.
The key facts are:
- `L.skolem₁.Functions σ s = L.BoundedFormula Fam.EmptyFam (σ.prod (.of s))`
- The cardinality of all bounded formulas is bounded by `max ℵ₀ L.card` (from Encoding.lean)
- Therefore the combined language `L.sum L.skolem₁` has bounded function symbols

These bounds are used in the proof of exists_elementarySubstructure_card_eq via
lift_card_closure_le from SubstructureMS.lean.
-/

/-- The sigma of all Skolem function symbols is bounded by the sigma of all bounded formulas. -/
theorem card_skolem₁_functions_le :
    #(Σ s σ, L.skolem₁.Functions σ s) ≤ #(Σ σ, L.BoundedFormula Fam.EmptyFam σ) := by
  apply Cardinal.mk_le_of_injective
    (f := fun ⟨s, σ, φ⟩ => ⟨σ.prod (.of s), φ⟩)
  intro ⟨s₁, σ₁, φ₁⟩ ⟨s₂, σ₂, φ₂⟩ h
  -- From σ₁.prod (.of s₁) = σ₂.prod (.of s₂), we get σ₁ = σ₂ and s₁ = s₂
  injection h with hprod hφ
  injection hprod with h1 h2
  injection h2 with h3
  subst h1
  subst h3
  cases hφ
  rfl

lemma add_le_of_le_of_le_of_infinite
  {X Y Z : Cardinal}
  (hXZ : X ≤ Z)
  (hYZ : Y ≤ Z)
  (hZinf : (ℵ₀ : Cardinal) ≤ Z) :
  X + Y ≤ Z :=
by
  by_cases h: ℵ₀ ≤ X
  case pos =>
    -- reduce addition to max using infinitude of Z
    calc
      X + Y = max X Y := by
        simpa [max_comm] using
          (Cardinal.add_eq_max (a := X) (b := Y) h)
      _ ≤ Z := max_le hXZ hYZ
  case neg =>
    by_cases h': ℵ₀ ≤ Y
    case pos =>
      simp_all only [not_le]
      rw[add_comm, add_eq_max h']
      simp_all
    case neg =>
      apply le_trans (b:= ℵ₀)
      · simp_all only [not_le]
        have h := Cardinal.add_lt_aleph0  h' h
        simp_all only [add_le_aleph0, le_of_lt, and_self]
      · exact hZinf

def f : (s : Sorts) → (σ : Signature Sorts) → (L.Functions σ s → L.BoundedFormula Fam.EmptyFam σ) :=
    fun _ σ f =>
      let v : L.Term (Fam.EmptyFam ⊕ₛ σ.IdxFam) σ := (Term.varTerm (L:= L) σ).bind
        ⟨fun s v => Term.var s (Sum.inr v)⟩
      BoundedFormula.equal (Term.func f v) (Term.func f v)

def F (s : Sorts) (σ : Signature Sorts)
    (g : L.Functions σ s) : L.BoundedFormula Fam.EmptyFam σ :=
by
  classical
  let v : L.Term (Fam.EmptyFam ⊕ₛ σ.IdxFam) σ :=
    (Term.varTerm (L := L) σ).bind ⟨fun s v => Term.var s (Sum.inr v)⟩
  exact BoundedFormula.equal (Term.func g v) (Term.func g v)

lemma hinj : ∀ s σ, Function.Injective (fun g : L.Functions σ s => F s σ g) := by
  intro s σ g g' h
  simp_all only [F, BoundedFormula.equal.injEq, heq_eq_eq, Term.func.injEq, and_true, true_and,
    and_self]

def bundledInj
  {Sorts : Type z} {L : Language Sorts} :
  ((i₁ : Signature Sorts) × (i : Sorts) ×  L.Functions i₁ i) ↪
    (Σ i : Signature Sorts, L.BoundedFormula Fam.EmptyFam i) :=
by
  classical
  refine
  { toFun := ?_
    inj'  := ?_ }
  · intro x
    -- unpack ULift + the triple
    rcases x with ⟨s, σ, g⟩
    exact ⟨s ,  F σ s g⟩
  · intro x y h
    rcases x with ⟨s, σ, g⟩
    rcases y with ⟨s', σ', g'⟩
    -- equality in Σ gives: σ = σ' and HEq of the payloads
    rcases (Sigma.mk.inj_iff.mp h) with ⟨hσ, hHEq⟩
    subst hσ
    cases hHEq
    rfl

def inj_prodSingleton
  {Sorts : Type z} {L : Language Sorts} :
  ((i₁ : Signature Sorts) × (i : Sorts) × L.BoundedFormula Fam.EmptyFam (i₁ ⨯ ⦃i⦄)) ↪
    (Σ i : Signature Sorts, L.BoundedFormula Fam.EmptyFam i) :=
by
  classical
  refine
  { toFun := ?_
    inj'  := ?_ }
  · rintro ⟨σ, s, φ⟩
    exact ⟨σ ⨯ ⦃s⦄, φ⟩
  · rintro ⟨s, σ, φ⟩ ⟨s', σ', φ'⟩ h
    -- equality in Σ gives index equality + HEq of payloads
    rcases (Sigma.mk.inj_iff.mp h) with ⟨hidx, hφ⟩
    -- from hidx : (σ ⨯ ⦃s⦄) = (σ' ⨯ ⦃s'⦄), get σ=σ' and s=s'
    -- (this step depends on your Signature API; often `cases hidx` is enough)
    cases hidx
    -- now hφ : HEq φ φ' but indices are definitional equal, so it’s just Eq
    cases hφ
    rfl

def nat_formula_inj : ℕ → L.BoundedFormula Fam.EmptyFam .nil
  | 0 => .falsum
  | n + 1 => (nat_formula_inj n).imp .falsum

lemma nat_formula_inj_size (n : ℕ) :
  (nat_formula_inj (L:= L) n).size = 2*n + 1:= by
  induction n
  case zero => simp only [nat_formula_inj, BoundedFormula.size]
  case succ n ih =>
    simp only [nat_formula_inj, BoundedFormula.size, ih]
    linarith

lemma nat_formula_inj_inj : Function.Injective (nat_formula_inj (L:=L)) := by
  intro a b h
  apply congrArg (BoundedFormula.size (L:= L)) at h
  simp only [nat_formula_inj_size, Nat.add_right_cancel_iff, mul_eq_mul_left_iff,
    OfNat.ofNat_ne_zero, or_false] at h
  exact h

theorem card_functions_sum_skolem₁ :
    #( (η : Signature Sorts) × (s : Sorts)  × (L.sum L.skolem₁).Functions η s) ≤
    #(Σ σ, L.BoundedFormula Fam.EmptyFam σ) := by
  simp only [card_functions_sum, skolem₁_Functions, mk_sigma, sum_add_distrib']
  apply add_le_of_le_of_le_of_infinite
  · simp only [←lift_sum]
    simp only [←mk_sigma]
    apply mk_le_of_injective ( f:= bundledInj ∘ ULift.down )
    simp only [EmbeddingLike.comp_injective]
    intro x y
    simp only [ULift.down_inj, imp_self]
  · simp only [←lift_sum]
    simp only [←mk_sigma]
    apply mk_le_of_injective (f:= inj_prodSingleton  ∘ ULift.down)
    simp only [EmbeddingLike.comp_injective]
    intro x y
    simp only [ULift.down_inj, imp_self]
  · classical
    let α := (Σ i : Signature Sorts, L.BoundedFormula Fam.EmptyFam i)
    let e : ℕ → α :=
      fun i  => ⟨.nil, nat_formula_inj i⟩
    -- Nat infinite + injection into α gives α infinite
    haveI : Infinite α := by
      apply Infinite.of_injective e
      intro i j h
      simp_all only [e]
      simp_all only [Sigma.mk.injEq, heq_eq_eq, true_and, α]
      exact nat_formula_inj_inj h
    -- now the real lemma:
    have hα : (Cardinal.aleph0 : Cardinal) ≤ #α :=
      Cardinal.aleph0_le_mk α
    -- convert #(Σ i, ...) to the sum of cardinals
    simpa [α, Cardinal.mk_sigma] using hα

theorem card_functions_sum_skolem₁_le :
    #( (η : Signature Sorts) × (s : Sorts)  × (L.sum L.skolem₁).Functions η s) ≤
    max ℵ₀ (lift #Sorts + L.card) := by
  apply le_trans (b:= #(Σ σ, L.BoundedFormula Fam.EmptyFam σ))
  · exact card_functions_sum_skolem₁
  · refine _root_.trans BoundedFormula.card_le' (lift_le.{max u v}.1 ?_)
    apply  (le_trans (lift_le.mpr BoundedFormula.BFCode_card))
    simp_all only [mk_sigma, mk_eq_zero, sum_const, lift_uzero, lift_zero, mul_zero, add_zero,
      lift_max, lift_aleph0, lift_add, lift_lift, ge_iff_le, le_refl]

/-- Bounded formulas with empty free variables are countable when the language is countable. -/
instance instCountableBoundedFormulaEmpty
    [Countable Sorts]
    [Countable (Σ η s, L.Functions η s)]
    [Countable (Σ σ, L.Relations σ)] :
    Countable (Σ σ, L.BoundedFormula Fam.EmptyFam σ) := by
  haveI : Countable (Σ s : Sorts, (Fam.EmptyFam : Sorts → Type _) s) := by
    have : IsEmpty (Σ s : Sorts, (Fam.EmptyFam : Sorts → Type _) s) := ⟨fun ⟨_, x⟩ => x.elim⟩
    infer_instance
  exact BoundedFormula.countable

/-- The Skolem function symbols are countable when the language is countable. -/
instance instCountableSkolem₁Functions
    [Countable Sorts]
    [Countable (Σ η s, L.Functions η s)]
    [Countable (Σ σ, L.Relations σ)] :
    Countable (Σ σ s, L.skolem₁.Functions σ s) := by
  have hinj : Function.Injective
      (fun (x : Σ σ s, L.skolem₁.Functions σ s) =>
        (⟨x.1.prod (.of x.2.1), x.2.2⟩ : Σ σ, L.BoundedFormula Fam.EmptyFam σ)) := by
    intro ⟨s₁, σ₁, φ₁⟩ ⟨s₂, σ₂, φ₂⟩ h
    injection h with hprod hφ
    injection hprod with h1 h2
    injection h2 with h3
    subst h1
    subst h3
    cases hφ
    rfl
  exact Function.Injective.countable hinj

/-- The sum language `L.sum L.skolem₁` has countable function symbols
    when the original language has countable function symbols and relations. -/
instance instCountableSumSkolem₁Functions
    [Countable Sorts]
    [Countable (Σ η s, L.Functions η s)]
    [Countable (Σ σ, L.Relations σ)] :
    Countable (Σ σ s, (L.sum L.skolem₁).Functions σ s) := by
  -- (L.sum L.skolem₁).Functions σ s = L.Functions σ s ⊕ L.skolem₁.Functions σ s
  -- The sigma over this sum is equivalent to the sum of the sigmas
  haveI h1 : Countable (Σ σ s, L.Functions σ s) := inferInstance
  haveI h2 : Countable (Σ σ s, L.skolem₁.Functions σ s) := instCountableSkolem₁Functions
  exact Countable.of_equiv
    ((Σ σ s, L.Functions σ s) ⊕ (Σ σ s, L.skolem₁.Functions σ s))
    { toFun := fun x => match x with
        | Sum.inl ⟨s, σ, f⟩ => ⟨s, σ, Sum.inl f⟩
        | Sum.inr ⟨s, σ, f⟩ => ⟨s, σ, Sum.inr f⟩
      invFun := fun ⟨s, σ, f⟩ => match f with
        | Sum.inl f => Sum.inl ⟨s, σ, f⟩
        | Sum.inr f => Sum.inr ⟨s, σ, f⟩
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro ⟨s, σ, f⟩; cases f <;> rfl }

namespace Substructure

theorem skolem₁_reduct_isElementary (S : (L.sum L.skolem₁).Substructure M) :
    (LHom.sumInl.substructureReduct S).IsElementary := by
  -- The reduct has the same underlying set as S
  let S' := LHom.sumInl.substructureReduct S
  apply S'.isElementary_of_exists
  intro s σ φ xs a h
  -- xs : S'[^]σ where S'.Subtype = S.Subtype (same underlying sets, same coercion)
  -- The formula φ is simultaneously a Skolem function symbol in L.skolem₁
  let φ' : (L.sum L.skolem₁).Functions σ s := LHom.sumInr.onFunction φ
  -- Coerce xs to get M-valued tuple using composition with Subtype.val
  let coe_xs : M[^]σ := S.subtype <$>ₛ xs
  -- The Skolem function applied to the coerced tuple gives a witness
  have hmem : funMap φ' coe_xs ∈ S s := by
    apply S.fun_mem φ' coe_xs
    intro t i
    exact Set.mem_of_eq_of_mem
      (congrFun (DFunLike.congr_fun (get_map xs S.subtype) t) i) (xs.get t i).2
  refine ⟨⟨funMap φ' coe_xs, hmem⟩, ?_⟩
  /- The Skolem function chooses a witness via epsilon
    By definition of skolem₁Structure, funMap (Sum.inr φ) x =
    epsilon (fun a => φ.Realize default ⟨x, a⟩)
    Since ⟨a, h⟩ witnesses the existential, epsilon_spec gives us the result -/
  have hrealize : φ.Realize default (coe_xs, funMap (L := L.sum L.skolem₁) φ' coe_xs) := by
    -- By definition φ' = Sum.inr φ and funMap (Sum.inr φ) = epsilon ...
    change φ.Realize default (coe_xs, funMap (L := L.sum L.skolem₁) (Sum.inr φ) coe_xs)
    have heq : funMap (L := L.sum L.skolem₁) (Sum.inr φ) coe_xs =
        Classical.epsilon fun a => φ.Realize default (coe_xs, a) := rfl
    rw [heq]
    -- h has type: φ.Realize default (S'.subtype <$>ₛ xs, a)
    -- S'.subtype <$>ₛ xs = coe_xs since S'.subtype s x = x.1
    have hcoe : S'.subtype <$>ₛ xs = coe_xs := rfl
    have h' : (fun b => φ.Realize default (coe_xs, b)) a := by rw [← hcoe]; exact h
    have hex : ∃ b, φ.Realize default (coe_xs, b) := ⟨a, h'⟩
    exact Classical.epsilon_spec hex
  exact hrealize

/-- Any `L.sum L.skolem₁`-substructure is an elementary `L`-substructure. -/
noncomputable def elementarySkolem₁Reduct (S : (L.sum L.skolem₁).Substructure M) :
    L.ElementarySubstructure M :=
  ⟨LHom.sumInl.substructureReduct S, S.skolem₁_reduct_isElementary⟩

theorem coeSort_elementarySkolem₁Reduct (S : (L.sum L.skolem₁).Substructure M) :
    (S.elementarySkolem₁Reduct : DepSet M) = S := by
  rfl

end Substructure

open Substructure

variable (L) (M)

/-- The elementary substructure obtained from the bottom Skolem substructure is small.
    Note: The universe level depends on the combined language's universe levels. -/
instance Substructure.elementarySkolem₁Reduct.instSmall (s : Sorts) :
    Small.{max (max u v) z} ((⊥ : (L.sum L.skolem₁).Substructure M).elementarySkolem₁Reduct s) := by
  rw [coeSort_elementarySkolem₁Reduct]
  exact Substructure.small_bot s

/-- There exists an elementary substructure that is small in each sort. -/
theorem exists_small_elementarySubstructure :
    ∃ S : L.ElementarySubstructure M, ∀ s, Small.{max (max u v) z} (S s) :=
  ⟨Substructure.elementarySkolem₁Reduct ⊥, fun _ => inferInstance⟩

variable {M}
open Fam Signature Substructure
/-- The **Downward Löwenheim–Skolem theorem** (many-sorted version):
  If `A` is a family of sets in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (#(Σ s, A s), L.card) ≤ κ` and `κ ≤ #(Σ s, M s)`, then `M` has an elementary substructure
  containing `A` of cardinality `κ` (in each sort, up to lifts).

  Note: The precise universe constraints differ from the single-sorted case due to the
  additional sort universe `z`. The statement below is a placeholder that needs careful
  universe management to be fully correct. -/
theorem exists_elementarySubstructure_card_eq
    (A : DepSet M) (κ : Cardinal.{w'}) (h1 : ℵ₀ ≤ κ)
    (h2 : lift.{w'} #(Σ s, A s) ≤ lift.{max z w} κ)
    (h3 : lift #Sorts + lift.{w'} L.card ≤ lift.{max u v z} κ)
    (h4 : lift.{max w z} κ ≤ lift.{w'} #(Σ s, M s)) :
    ∃ S : L.ElementarySubstructure M, (∀ s, A s ⊆ (S : L.Substructure M) s) ∧
      lift.{w'} #(Σ s, (S : L.Substructure M) s) = lift.{max z w} κ := by
  have hk := h1
  --have : ∀ s : Sorts, ∃ A' : Set (M s),
  obtain ⟨A'', hA''⟩ := Cardinal.le_mk_iff_exists_set.1 h4
  --A'' has type `Set (ULift.{max w' z, max w z} ((s : Sorts) × M s))`
  --We need to convert it to an appropriate lifted DepSet
  let A' : (DepSet M) := DepSet.mk (fun s => ({a | ⟨s, a⟩ ∈ A''} : Set (M s)))
  have hA' : lift.{w'} #(Σ s, A' s) = lift.{max w z} κ := by
    rw[←hA'']
    --A bijection between `Sigma A'` and `A''`
    let e0 : ((s : Sorts) × ↑(A'.carrier s)) ≃ (↑A'') :=
    ⟨ fun x => by
        rcases x with ⟨s, a, ha⟩
        simp only [Set.mem_setOf_eq, A'] at ha
        exact ⟨_, ha⟩
      ,
      fun x => by
        rcases x with ⟨⟨s,a⟩, ha⟩
        simp only [Set.coe_setOf, A']
        exact ⟨s, ⟨a, ha⟩⟩
      ,
      (by intro x; simp only [Subtype.coe_eta, Sigma.eta, id_eq]),
      (by intro x; simp only [id_eq, Sigma.eta])
     ⟩
    classical
    have h :
        #(ULift.{w', max w z} ((s : Sorts) × ↑(A'.carrier s))) = #↑A'' := by
      -- `Equiv.ulift` is the equivalence `ULift T ≃ T`
      exact Cardinal.mk_congr (Equiv.ulift.trans e0)
    simpa using h
  rw [← aleph0_le_lift.{_, max w z}] at h1
  rw [← hA'] at h1 h2 ⊢
  --Obtain our structure:
  let S := elementarySkolem₁Reduct
                (Substructure.closure
                      (L.sum L.skolem₁)
                      (A ⊔ A')
                )
  use S
  have h_sub : A ⊆ (S : L.Substructure M) := by
    intro xs h
    unfold S Substructure.closure elementarySkolem₁Reduct
    simp_all only [ge_iff_le, mk_sigma, lift_sum, Set.coe_setOf, DepSet.sup_eq_union,
      DepSet.union_subset_iff, LHom.coe_substructureReduct, aleph0_le_lift, A']
    obtain ⟨s, x⟩ := xs
    simp_all only [DepSet.mem_sigma, Substructure.sInf_apply, Set.mem_setOf_eq,
      DepSetLike.carrier_toDepSet, Set.mem_iInter, and_imp]
    intro X hi hi'
    change x ∈ X s
    apply DepSet.subset_intro_mem_eq.mp hi
    exact h
  have hA'_inf:  ℵ₀ ≤ #((s : Sorts) × ↑(A'.carrier s)) := by
                  rw[←lift_le.{w'}]
                  apply le_trans (b:= lift.{max w z} κ)
                  · simp only [lift_aleph0, ge_iff_le, aleph0_le_lift]
                    simp_all only [mk_sigma, lift_sum, Set.coe_setOf, ge_iff_le,  A', S]
                  · simp_all only [mk_sigma, lift_sum, Set.coe_setOf, ge_iff_le, le_refl, A', S]
  have h_le:  #((s : Sorts) × ↑(A.carrier s)) ≤ #((s : Sorts) × ↑(A'.carrier s)) := by
    rw[←lift_le.{w'}]
    exact h2
  have hA_plus_A' : #((s : Sorts) × ↑(A'.carrier s)) + #((s : Sorts) × ↑(A.carrier s)) =
            #((s : Sorts) × ↑(A'.carrier s))
  := by
      rw[Cardinal.add_eq_max (a:= #((s : Sorts) × ↑(A'.carrier s)))
                                  (b:= #((s : Sorts) × ↑(A.carrier s)))
                (by
                rw[←lift_le.{w'}]
                simp only [lift_aleph0, mk_sigma, lift_sum, ge_iff_le]
                simp at hA'_inf
                simp_all only [mk_sigma, lift_sum, Set.coe_setOf, ge_iff_le, aleph0_le_lift, A', S])
      ]
      simpa using h_le
  constructor
  --Goal: `∀ (s : Sorts), A.carrier s ⊆ (↑↑S).carrier s`
  · rw[←DepSet.subset_intro_mem_eq]; exact h_sub
  --Goal : `lift.{w'} #(Σ s, (S : L.Substructure M).Subtype s) = lift.{max z w} κ`
  let h := lift_card_closure_le (L := L.sum L.skolem₁) (A := A ⊔ A')
  · apply le_antisymm
    · apply lift_le.{w', max w z}.2
      apply lift_le.{max u (max u v) z}.1
      have h5 : max ℵ₀
               (lift.{max u (max u v) z, max w z} #((s : Sorts) ×
                ↑(max A.carrier (fun s ↦ A'.carrier s) s)) +
                lift.{w, max (max u (max u v) z) z}
                #( (η : Signature Sorts) × (s : Sorts)  × (L.sum L.skolem₁).Functions η s))
              ≤ lift.{max u (max u v) z} #((s : Sorts) × ↑(A'.carrier s)) := by
          rw [max_le_iff, aleph0_le_lift, ← aleph0_le_lift.{_, w'}, add_eq_max, max_le_iff, lift_le]
          constructor
          · simp_all only [mk_sigma, lift_sum, Set.coe_setOf, ge_iff_le, aleph0_le_lift, A', S]
          · have hun: #((s : Sorts) × ↑(max A.carrier (fun s ↦ A'.carrier s) s))
                      = #(Σ s, A' s) := by
                apply le_antisymm
                · simp only [Pi.sup_apply, Set.sup_eq_union]
                  have hpoint : ∀ i, #↑(A.carrier i ∪ A'.carrier i)
                    ≤ #↑(A.carrier i) + #↑(A'.carrier i) := by
                    intro i
                    simpa only [Cardinal.mk_set] using
                      (Cardinal.mk_union_le (A.carrier i) (A'.carrier i))
                  have hsum : (Cardinal.sum fun i ↦ #↑(A.carrier i ∪ A'.carrier i))
                    ≤ Cardinal.sum fun i ↦ (#↑(A.carrier i) + #↑(A'.carrier i)) := by
                    exact Cardinal.sum_le_sum _ _ hpoint
                    -- finish by distributing sum over addition
                  apply le_trans (b := #((s : Sorts) × ↑(A.carrier s)) +
                    #((s : Sorts) × ↑(A'.carrier s)))
                  · simpa only [mk_sigma, sum_add_distrib'] using hsum
                  · rw[add_comm, hA_plus_A']
                · simp only [Pi.sup_apply, Set.sup_eq_union, mk_sigma]
                  apply sum_le_sum;
                  intro i
                  apply mk_le_mk_of_subset
                  simp only [Set.subset_union_right]
            constructor
            · apply le_trans (b:= #((s : Sorts) × ↑(A.carrier s)) +
                #((s : Sorts) × ↑(A'.carrier s)))
              · simp only [Pi.sup_apply, Set.sup_eq_union, mk_sigma]
                have hpoint : ∀ i, #↑(A.carrier i ∪ A'.carrier i)
                  ≤ #↑(A.carrier i) + #↑(A'.carrier i) := by
                  intro i
                  simpa only [Cardinal.mk_set] using
                    (Cardinal.mk_union_le (A.carrier i) (A'.carrier i))
                simp only [← Cardinal.sum_add_distrib]
                exact Cardinal.sum_le_sum _ _ hpoint
              · rw[add_comm, hA_plus_A']
            · rw[←lift_le.{max w' (max (max u v) w) z}]
              have : lift.{max w' (max (max u v) w) z, max (max (max u v) w) z}
                     (lift.{max u (max u v) z, max w z} #((s : Sorts) × ↑(A'.carrier s))) =
                    lift.{max w' (max (max u v) w) z} κ := by
                    simp only [lift_lift]
                    rw[←lift_inj.{_, max w' (max (max u v) w) z}]
                    simp only [lift_lift]
                    rw[←lift_inj.{_, max w' (max (max u v) w) z}] at hA'
                    simp only [lift_lift] at hA'
                    exact hA'
              rw[this]
              apply le_trans (b:= max ℵ₀ (lift.{max w' (max (max u v) w) z} #Sorts +
                lift.{max w' (max (max u v) w) z} L.card))
              · rw[lift_lift]
                rw[←lift_le.{max w' (max (max u v) w) z}, lift_max, lift_lift, lift_aleph0]
                rw[lift_add, lift_lift, lift_lift]
                let h:= card_functions_sum_skolem₁_le (L:= L)
                rw[←lift_le.{max w' (max (max u v) w) z}, lift_max, lift_aleph0] at h
                apply le_trans h
                simp only [lift_add, lift_lift, le_refl]
              · rw[←lift_le.{max w' (max (max u v) w) z}] at h3
                apply max_le
                · simp only [aleph0_le_lift, hk]
                · simpa only [lift_add, lift_lift, ge_iff_le] using h3
          · simp only [Pi.sup_apply, Set.sup_eq_union, mk_sigma, lift_sum, ge_iff_le]
            apply le_trans (b:= sum fun i ↦ lift.{max (max u v) z, w} #↑(A'.carrier i))
            · rw[←lift_le.{max (max (max u v) w) z}] at hA'_inf
              apply le_trans (b:=lift.{max (max (max u v) w) z, max w z}
                #((s : Sorts) × ↑(A'.carrier s)))
              · simpa only [mk_sigma, lift_sum, lift_aleph0, ge_iff_le] using hA'_inf
              · simp only [mk_sigma, ←lift_sum]
                rw[←lift_le.{max (max w z) (max u v)}]
                simp only [lift_lift]
                simp only [lift_sum, ge_iff_le, le_refl]
            · apply sum_le_sum;
              intro i
              rw[lift_le]
              apply mk_le_mk_of_subset
              simp only [Set.subset_union_right]
      unfold S
      exact h.trans h5
    · have h_sub' : ∀ s, A' s ⊆ (S : L.Substructure M) s := by
        intro s a ha
        unfold S elementarySkolem₁Reduct
        change
          a ∈
            (LHom.sumInl.substructureReduct
              (Substructure.closure (L.sum L.skolem₁) (A ⊔ A'))) s
        exact
          (Substructure.subset_closure (L := L.sum L.skolem₁) (A := A ⊔ A') s)
            (by
              change a ∈ (A ⊔ A') s
              exact Or.inr ha)
      apply lift_le.2
      let f: (s : Sorts) × (A' s) → (s : Sorts) × (S : L.Substructure M) s :=
        fun ⟨s, ⟨a, ha⟩⟩ => ⟨s, ⟨a, h_sub' s ha⟩⟩
      apply Cardinal.mk_le_of_injective (f:= f)
      intro x y hxy
      rcases x with ⟨x, hx⟩
      rcases y with ⟨y, hy⟩
      simp only [DepSetLike.carrier_toDepSet, Sigma.mk.injEq, f] at hxy
      simp only [Sigma.mk.injEq, hxy, true_and]
      rcases hxy with ⟨hxy, hsub⟩
      subst hxy
      simp_all only [mk_sigma, lift_sum, ge_iff_le, heq_eq_eq, Subtype.mk.injEq, aleph0_le_lift]
      obtain ⟨val, property⟩ := hx
      obtain ⟨val_1, property_1⟩ := hy
      exact Subtype.ext (show val = val_1 from Subtype.ext_iff.mp hsub)






end Language

end MSFirstOrder
