import MultisortedLogic.Semantics
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import MultisortedLogic.RealizeSimps
/-
Basic examples with vector spaces
We use a similar set-up as in Mathlib\ModelTheory\Algebra\Ring\Basic.lean
(authored by Chrish Hughes under the Apache 2.0 license)
Still, dependent types seem to make life harder, as is illustrated by
relatively awkward proofs for simple statements. -/


namespace MSFirstOrder

namespace MSLanguage

open MSLanguage

universe u v w z u' v'

inductive ModuleSorts where
  | RSort
  | MSort
deriving DecidableEq

variable {α : ModuleSorts → Type*}

open ModuleSorts Finsupp Fam

/- trivial lemmas, asserting that there are only finitely many sorts -/
instance ModuleSortsFintype : Fintype ModuleSorts := by
  apply Fintype.ofList [RSort,MSort]
  intro x
  match x with
  | RSort => tauto
  | MSort => tauto

inductive moduleFunc : List ModuleSorts → ModuleSorts → Type
  | zeroR   : moduleFunc [] RSort
  | oneR    : moduleFunc [] RSort
  | negR    : moduleFunc [RSort] RSort
  | addR    : moduleFunc [RSort, RSort] RSort
  | mulR    : moduleFunc [RSort,RSort] RSort

  | zeroM   : moduleFunc [] MSort
  | negM  : moduleFunc [MSort] MSort
  | addM    : moduleFunc [MSort,MSort] MSort

  | smul    : moduleFunc [RSort,MSort] MSort

def rmod : MSLanguage ModuleSorts := {
  Functions := moduleFunc
  Relations := fun _ => Empty
}

open moduleFunc

/-- `ModuleFunc.addR`, but with the defeq type `rmod.Functions (2 0) RSort` instead
of `ModuleFunc (2 0) RSort`. Similarly for the others -/
abbrev addRFunc : rmod.Functions [RSort, RSort] RSort := addR

abbrev mulRFunc : rmod.Functions [RSort, RSort] RSort := mulR

abbrev negRFunc : rmod.Functions [RSort] RSort := negR

abbrev zeroRFunc : rmod.Functions [] RSort := zeroR

abbrev oneRFunc : rmod.Functions [] RSort := oneR

abbrev addMFunc : rmod.Functions [MSort, MSort] MSort := addM

abbrev negMFunc : rmod.Functions [MSort] MSort := negM

abbrev zeroMFunc : rmod.Functions [] MSort := zeroM

abbrev smulFunc : rmod.Functions [RSort, MSort] MSort := smul

--Instances for the ring sort
instance {α : ModuleSorts → Type*} : Zero (MSLanguage.rmod.Term α RSort) :=
{ zero := Constants.term zeroRFunc}

theorem zeroR_def (α : ModuleSorts → Type*) : (0 : MSLanguage.rmod.Term α RSort)
  = Constants.term zeroRFunc := rfl

instance (α : ModuleSorts → Type*) : One (MSLanguage.rmod.Term α RSort) :=
{ one := Constants.term oneRFunc}

theorem oneR_def (α : ModuleSorts → Type*) : (1 : MSLanguage.rmod.Term α RSort)
  = Constants.term oneRFunc := rfl

instance (α : ModuleSorts → Type*) : Add (MSLanguage.rmod.Term α RSort) :=
{ add := addRFunc.apply₂ }

theorem addR_def (α : ModuleSorts → Type*) (t₁ t₂ : MSLanguage.rmod.Term α RSort) :
    t₁ + t₂ = addRFunc.apply₂ t₁ t₂ := rfl

instance (α : ModuleSorts → Type*) : Mul (MSLanguage.rmod.Term α RSort) :=
{ mul := mulRFunc.apply₂ }

theorem mulR_def (α : ModuleSorts → Type*) (t₁ t₂ : MSLanguage.rmod.Term α RSort) :
    t₁ * t₂ = mulRFunc.apply₂ t₁ t₂ := rfl

instance (α : ModuleSorts → Type*) : Neg (MSLanguage.rmod.Term α RSort) :=
{ neg := negRFunc.apply₁ }

theorem negR_def (α : ModuleSorts → Type*) (t : MSLanguage.rmod.Term α RSort) :
    - t = negRFunc.apply₁ t := rfl


--instances for the module sort
instance {α : ModuleSorts → Type*} : Zero (MSLanguage.rmod.Term α MSort) :=
{ zero := Constants.term zeroMFunc}

theorem zeroM_def (α : ModuleSorts → Type*) : (0 : MSLanguage.rmod.Term α MSort)
  = Constants.term zeroMFunc := rfl

instance (α : ModuleSorts → Type*) : Add (MSLanguage.rmod.Term α MSort) :=
{ add := addMFunc.apply₂ }

theorem addM_def (α : ModuleSorts → Type*) (t₁ t₂ : MSLanguage.rmod.Term α MSort) :
    t₁ + t₂ = addMFunc.apply₂ t₁ t₂ := rfl

instance (α : ModuleSorts → Type*) : Neg (MSLanguage.rmod.Term α MSort) :=
{ neg := negMFunc.apply₁ }

theorem negM_def (α : ModuleSorts → Type*) (t : MSLanguage.rmod.Term α MSort) :
    - t = negMFunc.apply₁ t := rfl

--instance for scalar multiplication
instance (α : ModuleSorts → Type*) :
  SMul (MSLanguage.rmod.Term α RSort) (MSLanguage.rmod.Term α MSort) :=
{ smul := smulFunc.apply₂ }

theorem smul_def {α} (t₁ : MSLanguage.rmod.Term α RSort) (t₂ : MSLanguage.rmod.Term α MSort) :
    t₁ • t₂ = smulFunc.apply₂ t₁ t₂ := rfl

/-- Making this an abbrev instead of a def makes Lean automatically unfold this,
which helps with typeclass inference, see below -/
abbrev RMod (R M : Type u) : ModuleSorts → Type _
  | RSort => R
  | MSort => M

--TODO: get rid of SortedTuple.evalᵢⱼ using e.g. metaprogramming
/-- Analogue of the CompatibleRing typeclass -/
class CompatibleModule (R M : Type u)
  [Add R] [Mul R] [Neg R] [One R] [Zero R] [Add M] [Zero M] [Neg M] [SMul R M]
    extends MSLanguage.rmod.MSStructure (RMod R M) where
  funMap_addR : ∀ xs, funMap addRFunc xs = xs.eval₂₁ + xs.eval₂₂
  funMap_mulR : ∀ xs, funMap mulRFunc xs = xs.eval₂₁ * xs.eval₂₂
  funMap_negR : ∀ xs, funMap negRFunc xs = - xs.eval₁
  funMap_zeroR : ∀ xs, funMap zeroRFunc xs = 0
  funMap_oneR : ∀ xs, funMap oneRFunc xs = 1

  funMap_addM   : ∀ xs, funMap addMFunc xs = xs.eval₂₁ + xs.eval₂₂
  funMap_negM   : ∀ xs, funMap negMFunc xs = - xs.eval₁
  funMap_zeroM  : ∀ xs, funMap zeroMFunc xs = 0
  funMap_smul   : ∀ xs, funMap smulFunc xs = xs.eval₂₁ • xs.eval₂₂

open CompatibleModule

attribute [simp] funMap_addR funMap_mulR funMap_negR funMap_zeroR funMap_oneR
attribute [simp] funMap_zeroM funMap_negM funMap_addM funMap_smul

section realizing

variable {R M : Type u}
[Add R] [Mul R] [Neg R] [One R] [Zero R] [Add M] [Zero M] [Neg M] [SMul R M] [CompatibleModule R M]
variable (v : α →ₛ RMod R M)

theorem realize_addR (x y : rmod.Term α RSort) :
    Term.realize v (x + y) = Term.realize v x + Term.realize v y := by
  simp [addR_def, funMap_addR]
  rfl

theorem realize_mulR (x y : rmod.Term α RSort) :
    Term.realize v (x * y) = Term.realize v x * Term.realize v y := by
  simp [mulR_def, funMap_mulR]
  rfl

theorem realize_negR (x : rmod.Term α RSort) :
    Term.realize v (- x) = - Term.realize v x := by
  simp [negR_def, funMap_negR]
  rfl

theorem realize_zeroR :
    Term.realize v (0 : rmod.Term α RSort) = 0 := by
  simp [zeroR_def,constantMap, funMap_zeroR]


theorem realize_oneR :
    Term.realize v (1 : rmod.Term α RSort) = 1 := by
  simp [oneR_def, constantMap, funMap_oneR]


theorem realize_addM (x y : rmod.Term α MSort) :
    Term.realize v (x + y) = Term.realize v x + Term.realize v y := by
  simp [addM_def, funMap_addM]
  rfl

theorem realize_negM (x : rmod.Term α MSort) :
    Term.realize v (- x) = - Term.realize v x := by
  simp [negM_def, funMap_negM]
  rfl

theorem realize_zeroM :
    Term.realize v (0 : rmod.Term α MSort) = 0 := by
  simp [zeroM_def, constantMap, funMap_zeroM]

theorem realize_smul (r : rmod.Term α RSort) (m : rmod.Term α MSort) :
    Term.realize v (r • m) = Term.realize v r • Term.realize v m := by
  simp [smul_def, funMap_smul]
  rfl

end realizing

def compatibleOfModule (R M : Type u)
  [Add R] [Mul R] [Neg R] [One R] [Zero R] [Add M] [Zero M] [Neg M] [SMul R M] :
  CompatibleModule R M :=
  { funMap := fun {l} {s} f =>
      match l, s, f with
      | _, RSort, .zeroR => fun _ => 0
      | _, RSort, .oneR => fun _ => 1
      | _, RSort, .negR => fun xs => - xs.eval₁
      | _, RSort, .addR => fun xs => xs.eval₂₁ + xs.eval₂₂
      | _, RSort, .mulR => fun xs => xs.eval₂₁ * xs.eval₂₂
      | _, MSort, .zeroM => fun _ => 0
      | _, MSort, .negM => fun xs => - xs.eval₁
      | _, MSort, .addM => fun xs => xs.eval₂₁ + xs.eval₂₂
      | _, MSort, .smul => fun xs => xs.eval₂₁ • xs.eval₂₂
    funMap_zeroR := fun _ => rfl
    funMap_oneR := fun _ => rfl
    funMap_negR := fun _ => rfl
    funMap_addR := fun _ => rfl
    funMap_mulR := fun _ => rfl
    funMap_zeroM := fun _ => rfl
    funMap_negM := fun _ => rfl
    funMap_addM := fun _ => rfl
    funMap_smul := fun _ => rfl
    RelMap := Empty.elim }


/-- ℂ as a 2D module over ℝ. -/
abbrev RC : ModuleSorts → Type := RMod ℝ ℂ

/-- ℝ as a 1D module over ℝ. -/
abbrev RR : ModuleSorts → Type := RMod ℝ ℝ

noncomputable instance : MSStructure rmod RC := (compatibleOfModule ℝ ℂ).toMSStructure

instance : MSStructure rmod RR := (compatibleOfModule ℝ ℝ).toMSStructure

/-TODO: in order to use the `Add` instance, we have to cast over `σ := [RSort]`.
This is undesirable -/
example : rmod.Sentence :=
  let σ := [RSort]
  have h : σ[0] = RSort := rfl
  have : NeZero σ.length := Nat.instNeZeroSucc
  ∃'  ( ((h ▸ (σ&0) ) + ( h ▸ (σ&0)) ) =' 0)

/- Custom notation, to try and fix the issue above -/
infixl:65 " +ᵣ "  => addRFunc.apply₂
infixl:70 " *ᵣ "  => mulRFunc.apply₂
prefix:75 " -ᵣ "  => negRFunc.apply₁
infixl:67 " •' " => smulFunc.apply₂
infixl:65 " +ₘ " => addMFunc.apply₂
prefix:75 " -ₘ " => negMFunc.apply₁

abbrev no_two_torsion : rmod.Sentence :=
  let σ := [MSort]
  have : NeZero σ.length := Nat.instNeZeroSucc
  -- note just using zero on "0" in the right-hand side fails, as Lean does not find the instance
  -- `OfNat (rmod.Term (fun s => Empty ⊕ ([] ++ [MSort]).toFam s)) σ[0] 0`
  ∼ (∃' ((( ((σ&0) +ₘ (σ&0)) =' 0) ) ⊓ ( ∼ (( (σ&0)) =' (-ₘ 0) )) ) )


example : RR  ⊨ no_two_torsion := by
  unfold no_two_torsion
  letI := compatibleOfModule ℝ ℝ
  simp [Sentence.Realize, Formula.Realize ,SortedTuple.fromList',
    SortedTuple.eval₂₁, SortedTuple.eval₂₂, SortedTuple.eval₁, SortedTuple.toMap]
  intro x
  -- I am not sure why this gets unfolded as Term.realize
  have : Term.realize (L := rmod) (Fam.sumElim (fun s (a : Empty) ↦ a.elim)
    ((default : SortedTuple [] (RMod ℝ ℝ)).extend x).toFMap) 0 = (0 : RMod ℝ ℝ MSort) := rfl
  rw [this]
  intro h
  norm_num at *
  exact h

open SortedTuple

open Term

def myVarSymbols : ModuleSorts → Type
 | _ => ℕ

/-- Make a free variable symbol -/
def mk_var : (s : ModuleSorts) → ℕ → Term rmod myVarSymbols s :=
  fun s n => var s n

--The new Functions.apply₂ works great here!
noncomputable def smul_terms {α : ModuleSorts → Type*} :
  Term rmod α RSort → Term rmod α MSort → Term rmod α MSort :=
  Functions.apply₂ smul

noncomputable def addM_terms {α : ModuleSorts → Type*} :
  Term rmod α MSort → Term rmod α MSort → Term rmod α MSort :=
  Functions.apply₂ addM

@[simp]
theorem funMap_smul_eq {r : RC RSort} {m : RC MSort} :
    MSStructure.funMap smulFunc (!ₛ[⟨RSort, r⟩, ⟨MSort, m⟩] :
      SortedTuple [RSort,MSort] RC) = r • m := rfl
theorem funMap_smul_eq' {r : RR RSort} {m : RR MSort} :
    MSStructure.funMap smulFunc (!ₛ[⟨RSort, r⟩, ⟨MSort, m⟩] :
      SortedTuple [RSort,MSort] RR) = r • m := rfl
@[simp]
theorem funMap_addM_eq {m n : RC MSort} :
    MSStructure.funMap addMFunc (!ₛ[⟨MSort, m⟩, ⟨MSort, n⟩] :
      SortedTuple [MSort,MSort] RC) = m + n := rfl


def v₀ : rmod.Term myVarSymbols MSort := mk_var MSort 0
def v₁ : Term rmod myVarSymbols MSort := mk_var MSort 1

def s₀ : Term rmod myVarSymbols RSort := mk_var RSort 0
def s₁ : Term rmod myVarSymbols RSort := mk_var RSort 1


noncomputable def sv₀ : Term rmod myVarSymbols MSort := smul_terms s₀ v₀

/-- simple assignment function, mapping all named variables of the
ring sort to 1 and all those of the module sort to 0 -/
@[simp]
def my_vals : (myVarSymbols →ₛ RC) := fun s (n : ℕ) =>
  match s with
  | RSort => (n : ℝ)
  | MSort => (n : ℂ)

-- easy example, holds by unfolding definitions
example : Term.realize my_vals v₀ = (0 : ℂ) := by
  rw [v₀,mk_var]
  simp

--with the current assignment scalars s₀, s₁ should be equal
def φ₀ := s₀.equal s₁

/-- Either holds or fails after unfolding definitions,
depending on the choices for variable assignments -/
example : ¬ φ₀.Realize my_vals := by
  rw[φ₀]
  unfold s₀ s₁ mk_var
  simp only [Formula.realize_equal, realize_var, my_vals]
  norm_num

-- current shorthand for defining variable symbols does not work so well ...
noncomputable example : rmod.BoundedFormula Fam.EmptyFam [RSort,RSort] :=
  let σ := [RSort,RSort]
  have : NeZero σ.length := Nat.instNeZeroSucc
  σ&0 =' σ&1

-- one dimensional module
/-- An rmod-sentence saying that the structure as a module has rank at least 1 -/
noncomputable def rk_ge_1 : rmod.Sentence :=
  let σ := [MSort,RSort]
  have : NeZero σ.length := Nat.instNeZeroSucc
  ∃' ∀' ((((σ&1) •' (σ&0))
    =' Constants.term zeroMFunc) ⟹
     ( ((σ&1) ='(Constants.term zeroRFunc))))

-- two-dimensional module
noncomputable def eq_zero_implies_coeff_zero :
  rmod.BoundedFormula Fam.EmptyFam [MSort,MSort,RSort,RSort] :=
  let ξ := [MSort,MSort,RSort,RSort]
  have : NeZero ξ.length := Nat.instNeZeroSucc
  ((((ξ&2) •' (ξ&0)) +ₘ ((ξ&3) •' (ξ&1)))
    =' Constants.term zeroMFunc) ⟹
    ((ξ&2 =' Constants.term zeroRFunc) ⊓ (ξ&3 =' Constants.term zeroRFunc))

/-- An rmod-sentence saying that the structure as a module has rank at least 2 -/
noncomputable def rk_ge_2 : rmod.Sentence :=
  ∃' ∃' ∀' ∀' eq_zero_implies_coeff_zero

/-- An LRMod-sentence saying that the structure is a rank 1 module -/
noncomputable def rk_eq_1 : rmod.Sentence :=
  rk_ge_1 ⊓  ∼ rk_ge_2

noncomputable def has_non_zero_MSort : rmod.Sentence :=
  let σ := [MSort]
  have : NeZero σ.length := Nat.instNeZeroSucc
  ∃' (∼ ((σ&0) =' Constants.term zeroMFunc))

open MSStructure
example (h : (0 : ℝ) = (1 : ℝ)) : False := zero_ne_one h

/-- ℝ as a 1-D vector space has a non-zero element in the MSort -/
theorem R_has_non_zero_MSort : RR ⊨ has_non_zero_MSort := by
  unfold has_non_zero_MSort Sentence.Realize Formula.Realize BoundedFormula.Realize
  have : NeZero [MSort].length := Nat.instNeZeroSucc
  simp
  have : RR MSort = ℝ := rfl
  use (1 : ℝ)
  rw [constantMap]
  have : funMap zeroMFunc (default: SortedTuple [] RR)= (0 : ℝ) := by rfl
  rw [this]
  norm_num

noncomputable def dim_1_dif : rmod.Sentence :=
  let σ := [MSort,MSort,RSort]
  have : NeZero σ.length := Nat.instNeZeroSucc
  ∃' ∀' ∃'(((σ&2) •' (σ&0))=' (σ&1))

/-- 1 as a vector spans ℝ as a 1-D module over itself -/
theorem One_spans_R : RR ⊨ dim_1_dif := by
  have : NeZero [MSort,MSort,RSort].length := Nat.instNeZeroSucc
  unfold dim_1_dif Sentence.Realize Formula.Realize
  simp
  use 1
  intro x
  use (x : RR RSort)
  have coe_eq : RR RSort = RR MSort := rfl
  rw [SortedTuple.eval₂₁,SortedTuple.eval₂₂]
  simp [fromList', toMap]

theorem R_has_dim_ge_1 :  RR ⊨ rk_ge_1 := by
  unfold rk_ge_1 Sentence.Realize Formula.Realize
  have : NeZero [MSort,RSort].length := Nat.instNeZeroSucc
  simp
  use 1
  intro k
  rw [eval₂₁,eval₂₂]
  simp [fromList', toMap]
  intro h
  exact h

/-- A theorem stating that ℂ as a ℝ-module has dimension at least 2 -/
theorem C_has_dim_ge_2 : RC ⊨ rk_ge_2 := by
  have : NeZero [MSort, MSort, RSort, RSort].length := Nat.instNeZeroSucc
  unfold rk_ge_2 eq_zero_implies_coeff_zero Sentence.Realize
    Formula.Realize BoundedFormula.Realize
  simp
  use 1
  let i := Complex.I
  use (i : ℂ)
  have i_re : (i).re = 0 := rfl
  have i_im : (i).im = 1 := rfl
  intro x x₁
  rw [Functions.apply₂]
  simp
  rw [eval₂₁,eval₂₂] at *
  simp [fromList', toMap]
  rw [eval₂₁, eval₂₂] at *
  simp
  rw [eval₂₁,eval₂₂]
  simp [toMap]
  have its_R : RC RSort = ℝ := rfl
  have its_C : RC MSort = ℂ := rfl
  rw [constantMap]
  have : funMap zeroMFunc (default : SortedTuple [] RC) = (0 : ℂ) := rfl
  rw [this]
  rw [constantMap]
  have : funMap zeroRFunc (default : SortedTuple [] RC) = (0 : ℝ) := rfl
  rw [this]
  have re :  ((x : ℝ) + (x₁ : ℝ) * i).re = x := by
    simp
    exact Or.inr i_re
  have im : ((x : ℝ) + (x₁ : ℝ)* i).im = x₁ := by
    simp
    rw [i_im]
    simp
  simp [Complex.ext_iff, re, im]

/- TODO : It would be nice to have some metaprogramming available, so that we could,
in a reasonable way, state the def which takes as input a positive natural and outputs
the sentence rk_ge_n (currently we can't really implicitly talk about "n" free variables)
-/

-- R-torsion
/-- An rmod-sentence saying that the structure has R-torsion -/
noncomputable def has_torsion : rmod.Sentence :=
  let σ := [MSort,RSort]
  let : NeZero σ.length := Nat.instNeZeroSucc
  let torsion_witness := (∼ (σ&1 =' Constants.term zeroRFunc))
    ⊓ (∼ (σ&0 =' Constants.term zeroMFunc)) ⊓ ( ((σ&1) •' (σ&0)) =' Constants.term zeroMFunc)
  ∃' ∃' torsion_witness

/-- An rmod-sentence saying that the R-module is torsion free -/
noncomputable def torsion_free : rmod.Sentence :=
  ∼ (has_torsion)

/-- ℂ as an ℝ-module has no ℝ-torsion -/
theorem C_torsion_free : RC ⊨ torsion_free := by
  have : NeZero [MSort, RSort].length := Nat.instNeZeroSucc
  unfold torsion_free has_torsion
  simp [Sentence.Realize, Formula.Realize]
  intro x x₁ hx₁ hx
  rw [SortedTuple.eval₂₁, SortedTuple.eval₂₂]
  simp [fromList', toMap]
  rw [constantMap]
  have : funMap zeroMFunc (default : SortedTuple [] RC) = (0 : ℂ) := rfl
  rw [this]
  have : RC MSort = ℂ := rfl
  rw [this] at x
  have : RC RSort = ℝ := rfl
  rw [this] at x₁
  simp
  constructor
  · exact hx₁
  · exact hx
end MSLanguage
end MSFirstOrder
