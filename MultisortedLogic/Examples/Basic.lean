import MultisortedLogic.SemanticTactics

namespace MSFirstOrder
namespace Language
open Signature Term Structure

universe u v w z u' v' w' z'

/- We talk about languages with addition, multiplication, zero, etc. via typeclasses.
 The structure of more complicated languages (such as for additive groups) is loosely
 modeled after the algebraic hierarchy in Mathlib. For each operation Language `OpL`,
 there is a corresponding typeclass `CompatibleOpL`. This takes [L.Structure] as
 a parameter, rather than extending it, to prevent multiple instances of L.Structure
 when combining multiple compatible instances  -/

variable {Sorts : Type z} {σ : Signature Sorts} {α : Fam.{u'} Sorts}
  (L : Language Sorts) (M : Fam.{w} Sorts) (s : Sorts) {v : α →ₛ M}

section AddLang
/-- A language containing a symbol for addition. -/
class AddL where
  addFunc : L.Functions (⦃s⦄ ⨯ ⦃s⦄) s

/-- Compatibility between the `AddL` language symbol and the `Add` instance on `M s`. -/
class CompatibleAddL [AddL L s] [Add (M s)] [L.Structure M] : Prop where
  add_eq : ∀ x :  M [^] (⦃s⦄ ⨯ ⦃s⦄), funMap (L := L) AddL.addFunc x = x.1 + x.2

variable {L} {M} {s}

abbrev AddL.addT (t u : L.Term α (⦃s⦄)) [AddL L s] : L.Term α (⦃s⦄) :=
  AddL.addFunc.apply₂ t u

scoped infixl:65 " +ₗ " => AddL.addT

/-- An addition instance on the relevant terms, given an AddL instance -/
instance instAddTerm [AddL L s] :
    ∀ {α : Fam.{u'} Sorts}, Add (L.Term α (⦃s⦄)) where
  add t₁ t₂ := t₁ +ₗ t₂

@[simp]
theorem CompatibleAddL.funMap_eq [AddL L s] [Add (M s)] [L.Structure M] [CompatibleAddL L M s] :
  ∀ x : M [^] (⦃s⦄ ⨯ ⦃s⦄), funMap (L := L) AddL.addFunc x = x.1 + x.2 := CompatibleAddL.add_eq

@[simp]
theorem CompatibleAddL.realize_add' {v : α →ₛ M}
    [AddL L s] [Add (M s)] [L.Structure M] [CompatibleAddL L M s] (x y : L.Term α (⦃s⦄)) :
    (x +ₗ y).realize v = (x.realize v) + (y.realize v) := by
  rw [Term.realize_functions_apply₂, CompatibleAddL.add_eq]

@[simp]
theorem CompatibleAddL.realize_add
    [AddL L s] [Add (M s)] [L.Structure M] [CompatibleAddL L M s]
    (x y : L.Term α (⦃s⦄)) :
    (x + y).realize v = x.realize v + y.realize v := by
  apply realize_add'


inductive AddSymb (s : Sorts) : Signature Sorts → Sorts → Type u where
  | addSymb : AddSymb s (⦃s⦄ ⨯ ⦃s⦄) s

/-- The "canonical" language for addition on a sort s.
  TODO: any AddL admits a morphism from this language -/
def LAdd (s : Sorts) : Language Sorts where
  Functions := AddSymb s
  Relations := Fam.EmptyFam

/-- The addition symbol in the `LAdd` language with the defeq type
  `(LAdd s).Functions (⦃s⦄ ⨯ ⦃s⦄) s` -/
def LAdd.add (s : Sorts) : (LAdd s).Functions (⦃s⦄ ⨯ ⦃s⦄) s := AddSymb.addSymb

instance instAddL : AddL (LAdd s) s where
  addFunc := LAdd.add s

@[reducible]
def LAddOfAdd [Add (M s)] : (LAdd s).Structure M where
  funMap := fun f => match f with
  | .addSymb  => fun x => x.1 + x.2
  RelMap := fun r _ => Empty.elim r

end AddLang

section MulLang

class MulL where
  mulFunc : L.Functions (⦃s⦄ ⨯ ⦃s⦄) s

/-- Compatibility between the `MulL` language symbol and the `Mul` instance on `M s`. -/
class CompatibleMulL [MulL L s] [Mul (M s)] [L.Structure M] : Prop where
  mul_eq : ∀ x : M [^] (⦃s⦄ ⨯ ⦃s⦄), funMap (L := L) MulL.mulFunc x = x.1 * x.2

@[simp]
theorem CompatibleMulL.funMap_eq [MulL L s] [Mul (M s)] [L.Structure M] [CompatibleMulL L M s] :
  ∀ x : M [^] (⦃s⦄ ⨯ ⦃s⦄), funMap (L := L) MulL.mulFunc x = x.1 * x.2 := CompatibleMulL.mul_eq

variable {L} {M} {s}

abbrev MulL.mulT (t u : L.Term α ⦃s⦄) [MulL L s] : L.Term α ⦃s⦄ :=
  MulL.mulFunc.apply₂ t u

scoped infixl:70 " *ₗ " => MulL.mulT

/-- A multiplication instance on the relevant terms, given a MulL instance -/
instance instMulTerm [MulL L s] :
    ∀ {α : Fam.{u'} Sorts}, Mul (L.Term α ⦃s⦄) where
  mul t₁ t₂ := t₁ *ₗ t₂

@[simp]
theorem CompatibleMulL.realize_mul' [MulL L s] [Mul (M s)] [L.Structure M] [CompatibleMulL L M s]
    (x y : L.Term α ⦃s⦄) :
    (x *ₗ y).realize v = (x.realize v) * (y.realize v) := by
  rw [Term.realize_functions_apply₂, CompatibleMulL.mul_eq]


@[simp]
theorem CompatibleMulL.realize_mul [MulL L s] [Mul (M s)] [L.Structure M] [CompatibleMulL L M s]
    (x y : L.Term α ⦃s⦄) :
    (x * y).realize v = x.realize v * y.realize v := by apply realize_mul'

end MulLang

section InvLang

class InvL where
  invFunc : L.Functions ⦃s⦄ s

/-- Compatibility between the `InvL` language symbol and the `Inv` instance on `M s`. -/
class CompatibleInvL [InvL L s] [Inv (M s)] [L.Structure M] : Prop where
  inv_eq : ∀ x : M s, funMap (L := L) InvL.invFunc x = x⁻¹

@[simp]
theorem CompatibleInvL.funMap_eq [InvL L s] [Inv (M s)] [L.Structure M] [CompatibleInvL L M s] :
  ∀ x : M s, funMap (L := L) InvL.invFunc x = x⁻¹ := CompatibleInvL.inv_eq

variable {L} {M} {s}

abbrev InvL.invT (t : L.Term α ⦃s⦄) [InvL L s] : L.Term α ⦃s⦄ :=
  InvL.invFunc.apply₁ t

scoped postfix:max "⁻¹ₗ" => InvL.invT

/-- An inversion instance on the relevant terms, given an InvL instance -/
instance instInvTerm [InvL L s] :
    ∀ {α : Fam.{u'} Sorts}, Inv (L.Term α ⦃s⦄) where
  inv t := t⁻¹ₗ


@[simp]
theorem CompatibleInvL.realize_inv' [InvL L s] [Inv (M s)] [L.Structure M] [CompatibleInvL L M s]
    (x : L.Term α ⦃s⦄) :
    x⁻¹ₗ.realize v = (x.realize v : M s)⁻¹ := by
  rw [Term.realize_functions_apply₁, CompatibleInvL.inv_eq]


@[simp]
theorem CompatibleInvL.realize_inv [InvL L s] [Inv (M s)] [L.Structure M] [CompatibleInvL L M s]
    (x : L.Term α ⦃s⦄) :
    x⁻¹.realize v = (x.realize v : M s)⁻¹ := by
  simp only [Inv.inv, InvL.invT, realize_functions_apply₁, inv_eq]

end InvLang

section NegLang

class NegL where
  negFunc : L.Functions ⦃s⦄ s

/-- Compatibility between the `NegL` language symbol and the `Neg` instance on `M s`. -/
class CompatibleNegL [NegL L s] [Neg (M s)] [L.Structure M] : Prop where
  neg_eq : ∀ x : M s, funMap (L := L) NegL.negFunc x = -x

@[simp]
theorem CompatibleNegL.funMap_apply
  [NegL L s] [Neg (M s)] [L.Structure M] [CompatibleNegL L M s] :
  ∀ x : M s, funMap (L := L) NegL.negFunc x = -x := CompatibleNegL.neg_eq

variable {L} {M} {s}

abbrev NegL.negT (t : L.Term α ⦃s⦄) [NegL L s] : L.Term α ⦃s⦄ :=
  NegL.negFunc.apply₁ t

scoped prefix:75 "-ₗ" => NegL.negT

/-- A negation instance on the relevant terms, given a NegL instance -/
instance instNegTerm [NegL L s] :
    ∀ {α : Fam.{u'} Sorts}, Neg (L.Term α ⦃s⦄) where
  neg t := -ₗt


@[simp]
theorem CompatibleNegL.realize_neg' [NegL L s] [Neg (M s)] [L.Structure M] [CompatibleNegL L M s]
    (x : L.Term α ⦃s⦄) :
    (-ₗx).realize v = -(x.realize v : M s) := by
  rw [Term.realize_functions_apply₁, CompatibleNegL.neg_eq]

@[simp]
theorem CompatibleNegL.realize_neg [NegL L s] [Neg (M s)] [L.Structure M] [CompatibleNegL L M s]
    (x : L.Term α ⦃s⦄) :
    (-x).realize v = -(x.realize v : M s) := by
  simp only [Neg.neg, NegL.negT, realize_functions_apply₁, neg_eq]

end NegLang

section SubLang

class SubL where
  subFunc : L.Functions (⦃s⦄ ⨯ ⦃s⦄) s

/-- Compatibility between the `SubL` language symbol and the `Sub` instance on `M s`. -/
class CompatibleSubL [SubL L s] [Sub (M s)] [L.Structure M] : Prop where
  sub_eq : ∀ x : M [^] (⦃s⦄ ⨯ ⦃s⦄), funMap (L := L) SubL.subFunc x = x.1 - x.2

@[simp]
theorem CompatibleSubL.funMap_eq [SubL L s] [Sub (M s)] [L.Structure M] [CompatibleSubL L M s] :
  ∀ x : M [^] (⦃s⦄ ⨯ ⦃s⦄), funMap (L := L) SubL.subFunc x = x.1 - x.2 := CompatibleSubL.sub_eq

variable {L} {M} {s}

abbrev SubL.subT (t u : L.Term α ⦃s⦄) [SubL L s] : L.Term α ⦃s⦄ :=
  SubL.subFunc.apply₂ t u

scoped infixl:65 " -ₗ " => SubL.subT

/-- A subtraction instance on the relevant terms, given a SubL instance -/
instance instSubTerm [SubL L s] :
    ∀ {α : Fam.{u'} Sorts}, Sub (L.Term α ⦃s⦄) where
  sub t₁ t₂ := t₁ -ₗ t₂

@[simp]
theorem CompatibleSubL.realize_sub' [SubL L s] [Sub (M s)] [L.Structure M] [CompatibleSubL L M s]
    (x y : L.Term α ⦃s⦄) :
    (x -ₗ y).realize v = (x.realize v) - (y.realize v) := by
  rw [Term.realize_functions_apply₂, CompatibleSubL.sub_eq]


@[simp]
theorem CompatibleSubL.realize_sub [SubL L s] [Sub (M s)] [L.Structure M] [CompatibleSubL L M s]
    (x y : L.Term α ⦃s⦄) :
    (x - y).realize v = x.realize v - y.realize v := by apply realize_sub'

end SubLang

section ZeroLang

class ZeroL where
  zeroConst : L.Constants s

/-- Compatibility between the `ZeroL` language symbol and the `Zero` instance on `M s`. -/
class CompatibleZeroL [ZeroL L s] [Zero (M s)] [L.Structure M] : Prop where
  zero_eq : (ZeroL.zeroConst : L.Constants s) = (0 : M s)

@[simp]
theorem CompatibleZeroL.constantMap_eq
    [ZeroL L s] [Zero (M s)] [L.Structure M] [CompatibleZeroL L M s] :
    ↑(ZeroL.zeroConst : L.Constants s) = (0 : M s) := CompatibleZeroL.zero_eq

variable {L} {M} {s}

abbrev ZeroL.zeroT [ZeroL L s] : L.Term α ⦃s⦄ :=
  ZeroL.zeroConst.term

scoped notation "`0" => ZeroL.zeroT

/-- A zero instance on the relevant terms, given a ZeroL instance -/
instance instZeroTerm [ZeroL L s] :
    ∀ {α : Fam.{u'} Sorts}, Zero (L.Term α ⦃s⦄) where
  zero := `0

@[simp]
theorem CompatibleZeroL.realize_zero'
    [ZeroL L s] [Zero (M s)] [L.Structure M] [CompatibleZeroL L M s] :
    (`0 : L.Term α ⦃s⦄).realize v = (0 : M s) := by
  rw [Term.realize_constants, CompatibleZeroL.zero_eq]


@[simp]
theorem CompatibleZeroL.realize_zero
    [ZeroL L s] [Zero (M s)] [L.Structure M] [CompatibleZeroL L M s] :
    Term.realize v (0 : L.Term α ⦃s⦄) = (0 : M s) := by
  have : (0 : L.Term α ⦃s⦄) = `0 := rfl
  rw [this, Term.realize_constants, CompatibleZeroL.zero_eq]

end ZeroLang

section OneLang

class OneL where
  oneConst : L.Constants s

/-- Compatibility between the `OneL` language symbol and the `One` instance on `M s`. -/
class CompatibleOneL (L : Language Sorts) (M : Fam.{w} Sorts) (s : Sorts)
    [OneL L s] [One (M s)] [L.Structure M] : Prop where
  one_eq : (OneL.oneConst : L.Constants s) = (1 : M s)

@[simp]
theorem CompatibleOneL.constantMap_eq
    [OneL L s] [One (M s)] [L.Structure M] [CompatibleOneL L M s] :
    ↑(OneL.oneConst : L.Constants s) = (1: M s) := CompatibleOneL.one_eq

variable {L} {M} {s}

abbrev OneL.oneT [OneL L s] : L.Term α ⦃s⦄ :=
  OneL.oneConst.term

scoped notation "`1" => OneL.oneT

/-- A one instance on the relevant terms, given a OneL instance -/
instance instOneTerm (L : Language Sorts) (s : Sorts) [OneL L s] :
    ∀ {α : Fam.{u'} Sorts}, One (L.Term α ⦃s⦄) where
  one := `1

@[simp]
theorem CompatibleOneL.realize_one'
    [OneL L s] [One (M s)] [L.Structure M] [CompatibleOneL L M s] :
    (`1 : L.Term α ⦃s⦄).realize v = (1 : M s) := by
  rw [Term.realize_constants, CompatibleOneL.one_eq]


@[simp]
theorem CompatibleOneL.realize_one
    [OneL L s] [One (M s)] [L.Structure M] [CompatibleOneL L M s] :
    (1 : L.Term α ⦃s⦄).realize v = (1 : M s) := by
  have : (1 : L.Term α ⦃s⦄) = `1 := rfl
  rw [this, Term.realize_constants, CompatibleOneL.one_eq]

end OneLang

section InftyLang

class InfinityL (L : Language Sorts) (s : Sorts) where
  inftyConst : L.Constants s

/-- Compatibility between the `InfinityL` language symbol and a `Top` instance on `M s`. -/
class CompatibleTopL (L : Language Sorts) (M : Fam.{w} Sorts) (s : Sorts)
    [InfinityL L s] [Top (M s)] [L.Structure M] : Prop where
  infty_eq : (InfinityL.inftyConst : L.Constants s) = (⊤ : M s)

@[simp]
theorem CompatibleTopL.constMap_eq
  [InfinityL L s] [Top (M s)] [L.Structure M] [CompatibleTopL L M s] :
  (InfinityL.inftyConst : L.Constants s) = (⊤ : M s) := CompatibleTopL.infty_eq

variable {L} {M} {s}

abbrev InfinityL.inftyT [InfinityL L s] : L.Term α ⦃s⦄ :=
  InfinityL.inftyConst.term

scoped notation "`∞" => InfinityL.inftyT

instance instTopTerm [InfinityL L s] :
    ∀ {α : Fam.{u'} Sorts}, Top (L.Term α ⦃s⦄) where
  top := `∞

@[simp]
theorem CompatibleTopL.realize_infty'
  [InfinityL L s] [Top (M s)] [L.Structure M] [CompatibleTopL L M s] :
    (`∞ : L.Term α ⦃s⦄).realize v = (⊤ : M s) := by
  rw [Term.realize_constants, CompatibleTopL.infty_eq]

@[simp]
theorem CompatibleTopL.realize_infty
  [InfinityL L s] [Top (M s)] [L.Structure M] [CompatibleTopL L M s] :
    (⊤ : L.Term α ⦃s⦄).realize v = (⊤ : M s) := by
  have : (⊤ : L.Term α ⦃s⦄) = `∞ := rfl
  rw [this, Term.realize_constants, CompatibleTopL.infty_eq]

@[simp]
theorem CompatibleInfinityL.realize_infty'
    [InfinityL L s] [Top (M s)] [L.Structure M] [CompatibleTopL L M s] :
    (`∞ : L.Term α ⦃s⦄).realize v = (⊤ : M s) := by
  rw [Term.realize_constants, CompatibleTopL.infty_eq]

@[simp]
theorem CompatibleInfinityL.realize_infty
    [InfinityL L s] [Top (M s)] [L.Structure M] [CompatibleTopL L M s] :
    Term.realize v (⊤ : L.Term α ⦃s⦄) = (⊤ : M s) := by
  have : (⊤ : L.Term α ⦃s⦄) = `∞ := rfl
  rw [this, Term.realize_constants, CompatibleTopL.infty_eq]


end InftyLang

section OrderLang

/-- An alternative to `OrderL` that uses a formula instead of a relation symbol. -/
class OrderL where
  orderF : L.Formula (⦃s⦄ ⨯ ⦃s⦄).IdxFam

/-- OrderL'.OrderF, but with the defeq type L.BoundedFormula -/
def OrderF' (L : Language Sorts) {s : Sorts} [OrderL L s] :
  L.BoundedFormula (⦃s⦄ ⨯ ⦃s⦄).IdxFam nil  := OrderL.orderF

/-- Compatibility between the `OrderL'` formula and the `LE` instance on `M s`. -/
class CompatibleOrderL [OrderL L s] [LE (M s)] [L.Structure M] : Prop where
  le_eq : ∀ (x : (M [^] (⦃s⦄ ⨯ ⦃s⦄))),
    OrderL.orderF.Realize (L := L) x.get ↔ x.1 ≤ x.2

@[simp]
theorem CompatibleOrderL.realize_iff
    [OrderL L s] [LE (M s)] [L.Structure M] [CompatibleOrderL L M s] :
    ∀ x : M [^] (⦃s⦄ ⨯ ⦃s⦄),
      OrderL.orderF.Realize (L := L) x.get ↔ x.1 ≤ x.2 :=
  CompatibleOrderL.le_eq

variable {L} {M} {s} {xs : M [^] σ}

-- TODO: abstract this pattern
-- TODO: abstract this pattern
/-- Creates a bounded formula asserting that the first term is ≤ the second term
    using the `OrderL'` formula. Analogous to `OrderL.leF`. -/
def OrderL.leF [OrderL L s] (t u : L.Term (α ⊕ₛ σ.IdxFam) ⦃s⦄) :
    L.BoundedFormula α σ :=
  OrderL.orderF.boundedFormula₂ t u

infix:50 " ≤ₗ " => OrderL.leF

@[simp]
theorem compatibleOrderL.realize_le
    [LE (M s)] [OrderL L s] [L.Structure M] [CompatibleOrderL L M s]
    (x y : L.Term (α ⊕ₛ σ.IdxFam) ⦃s⦄) :
    (x ≤ₗ y).Realize v xs ↔
    (x.realize (Fam.sumElim v xs) : M s) ≤ y.realize (Fam.sumElim v xs) := by
  rw [OrderL.leF]
  simp only [BoundedFormula.realize_boundedFormula₂, realize_prod, CompatibleOrderL.realize_iff]

end OrderLang


/-- Additive monoid language on a sort `s`: addition and `0`. -/
class AMonoidL extends
  AddL L s,
  ZeroL L s

class CompatibleAMonoidL
    [AMonoidL L s] [Add (M s)] [Zero (M s)] [L.Structure M] : Prop
    extends
    CompatibleAddL L M s,
    CompatibleZeroL L M s

/-- Additive group language on a sort `s`: additive monoid language plus negation. -/
class AGroupL extends
  AMonoidL L s,
  NegL L s

section AGroupLang

class CompatibleAGroupL
    [AGroupL L s] [Add (M s)] [Neg (M s)] [Zero (M s)] [L.Structure M] : Prop
    extends
      CompatibleAMonoidL L M s,
      CompatibleNegL L M s

end AGroupLang

/-- Multiplicative monoid language on a sort `s`: multiplication and `1`. -/
class MMonoidL extends
  MulL L s,
  OneL L s

section MonoidLang

class CompatibleMMonoidL
    [MMonoidL L s] [Mul (M s)] [One (M s)] [L.Structure M] : Prop
    extends
    CompatibleMulL L M s,
    CompatibleOneL L M s

end MonoidLang

/-- Ordered additive group language on a sort `s`:
  additive group language plus an order relation `≤`. -/
class OAGroupL extends
  AGroupL L s,
  OrderL L s

class CompatibleOAGroupL
    [OAGroupL L s] [Add (M s)] [Neg (M s)] [Zero (M s)] [LE (M s)] [L.Structure M] : Prop
    extends
    CompatibleAGroupL L M s,
    CompatibleOrderL L M s

/-- Ordered multiplicative monoid language on a sort `s`:
  multiplicative monoid language plus an order relation `≤`. -/
class OMMonoidL extends
  MMonoidL L s,
  OrderL L s

/-- Multiplicative group language on a sort `s` -/
class MGroupL extends
  MMonoidL L s

/-- Ordered multiplicative group language on a sort `s`:
  multiplicative group language plus an order relation `≤`. -/
class OMGroupL extends
  MMonoidL L s,
  OrderL L s

/-- Extended ordered additive group language on a sort `s`:
  ordered additive group language plus `∞`. -/
class EOAGroupL extends
  OAGroupL L s,
  InfinityL L s

/-- Ring language on a sort `s`: addition, multiplication, negation, `0`, and `1`. -/
class RingL extends
  AGroupL L s,
  MMonoidL L s

/-- A ring language includes the additive monoid language (add + 0). -/
@[reducible]
def RingL.toinstAMonoidL
    [RingL L s] : AMonoidL L s :=
  { toAddL := (inferInstance : AddL L s)
    toZeroL := (inferInstance : ZeroL L s) }

/-- A ring language includes the additive group language (add + neg + 0). -/
@[reducible]
def RingL.instAGroupL [RingL L s] :
    AGroupL L s :=
  { toAMonoidL := toinstAMonoidL L s
    toNegL := (inferInstance : NegL L s) }

section RingLang

/-- Compatibility between a `RingL` language on `s` and the ring structure on `M s`. -/
class CompatibleRingL
    [RingL L s] [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)] [L.Structure M] :
    Prop extends
      CompatibleAGroupL L M s,
      CompatibleMMonoidL L M s

end RingLang

/-- Ordered ring language on a sort `s`: ring language plus an order relation `≤`. -/
class ORingL extends
  RingL L s,
  OrderL L s

section ORingLang

/-- Compatibility between an ordered ring language and the ordered ring
    structure on `M s`. Packages `CompatibleRingL` with the
    ordering on `M s`. -/
class CompatibleORingL
    [ORingL L s] [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)]
    [LE (M s)] [L.Structure M] : Prop extends
      CompatibleOrderL L M s,
      CompatibleRingL L M s
end ORingLang


end Language
end MSFirstOrder
