/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Semantics

/-!
# Operator languages

Languages with symbols for the usual algebraic operations, or an order, on a sort `s`; the
compatibility of a structure with Lean's operations; and notation for the terms and formulas built
from these symbols.

## Main definitions

* `AddL`, `MulL`, `NegL`, `ZeroL`, `OneL`, `InfinityL`: a symbol for `+`, `*`, `-`, `0`, `1` or `⊤`
  on the sort `s`.
* `OrderL`: an order on the sort `s`, given by a formula in two variables.
* `AMonoidL`, `AGroupL`, `MMonoidL`, `OAGroupL`, `EOAGroupL`, `RingL`, `ORingL`: combinations of
  these.
* `CompatibleAddL L M s`, …, `CompatibleORingL L M s`: the symbols are interpreted in `M` as Lean's
  operations on `M s`.
* `t +ₗ u`, `t *ₗ u`, `-ₗ t`, `` `∞ ``, `t ≤ₗ u`: terms and formulas built from the symbols, in the
  scope `ManySorted`. The constants `0` and `1` are terms through `Zero` and `One` instances.
* `modelAdd L M s`, …, `modelTop L M s`, `modelLE L M s`: the operations, `∞` and the order on
  `M s` read off from a structure, which are compatible with it by `modelRingCompatible`,
  `modelOAGroupCompatible` and `modelTopCompatible`.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

universe u v w z

variable {S : Type z} (L : Language.{u, v} S) (M : S → Type w) (s : S)

/-! ### Operator languages -/

/-- A language with a binary addition symbol on the sort `s`. -/
class AddL where
  /-- The addition symbol. -/
  addFunc : L.Functions (⦃s⦄ ⨯ ⦃s⦄) s

/-- A language with a binary multiplication symbol on the sort `s`. -/
class MulL where
  /-- The multiplication symbol. -/
  mulFunc : L.Functions (⦃s⦄ ⨯ ⦃s⦄) s

/-- A language with a unary negation symbol on the sort `s`. -/
class NegL where
  /-- The negation symbol. -/
  negFunc : L.Functions ⦃s⦄ s

/-- A language with a constant `0` of sort `s`. -/
class ZeroL where
  /-- The zero constant. -/
  zeroConst : L.Constants s

/-- A language with a constant `1` of sort `s`. -/
class OneL where
  /-- The one constant. -/
  oneConst : L.Constants s

/-- A language with a constant `∞` of sort `s`. -/
class InfinityL where
  /-- The infinity constant. -/
  inftyConst : L.Constants s

/-- A language with an order on the sort `s`, given by a formula in two variables. -/
class OrderL where
  /-- The formula `x₀ ≤ x₁`. -/
  orderF : L.Formula (⦃s⦄ ⨯ ⦃s⦄)

/-- Additive monoid language on `s`. -/
class AMonoidL extends AddL L s, ZeroL L s

/-- Additive group language on `s`. -/
class AGroupL extends AMonoidL L s, NegL L s

/-- Multiplicative monoid language on `s`. -/
class MMonoidL extends MulL L s, OneL L s

/-- Ordered additive group language on `s`. -/
class OAGroupL extends AGroupL L s, OrderL L s

/-- Extended ordered additive group language on `s`: an ordered additive group with `∞`. -/
class EOAGroupL extends OAGroupL L s, InfinityL L s

/-- Ring language on `s`: addition, multiplication, negation, `0` and `1`. -/
class RingL extends AGroupL L s, MMonoidL L s

/-- Ordered ring language on `s`: a ring language with an order. -/
class ORingL extends RingL L s, OrderL L s

/-! ### Compatibility with Lean operations -/

variable [L.Structure M]

/-- The addition symbol is interpreted as `+`. -/
class CompatibleAddL [AddL L s] [Add (M s)] : Prop where
  funMap_add : ∀ x : M [^] (⦃s⦄ ⨯ ⦃s⦄), funMap (L := L) AddL.addFunc x = x.1 + x.2

/-- The multiplication symbol is interpreted as `*`. -/
class CompatibleMulL [MulL L s] [Mul (M s)] : Prop where
  funMap_mul : ∀ x : M [^] (⦃s⦄ ⨯ ⦃s⦄), funMap (L := L) MulL.mulFunc x = x.1 * x.2

/-- The negation symbol is interpreted as `-`. -/
class CompatibleNegL [NegL L s] [Neg (M s)] : Prop where
  funMap_neg : ∀ x : M s, funMap (L := L) NegL.negFunc x = -x

/-- The zero constant is interpreted as `0`. -/
class CompatibleZeroL [ZeroL L s] [Zero (M s)] : Prop where
  funMap_zero : funMap (L := L) (M := M) (ZeroL.zeroConst (s := s)) PUnit.unit = 0

/-- The one constant is interpreted as `1`. -/
class CompatibleOneL [OneL L s] [One (M s)] : Prop where
  funMap_one : funMap (L := L) (M := M) (OneL.oneConst (s := s)) PUnit.unit = 1

/-- The infinity constant is interpreted as `⊤`. -/
class CompatibleTopL [InfinityL L s] [Top (M s)] : Prop where
  funMap_infty : funMap (L := L) (M := M) (InfinityL.inftyConst (s := s)) PUnit.unit = ⊤

/-- The order formula is interpreted as `≤`. -/
class CompatibleOrderL [OrderL L s] [LE (M s)] : Prop where
  realize_orderF : ∀ x : M [^] (⦃s⦄ ⨯ ⦃s⦄), (OrderL.orderF (L := L) (s := s)).Realize x ↔ x.1 ≤ x.2

attribute [simp] CompatibleAddL.funMap_add CompatibleMulL.funMap_mul CompatibleNegL.funMap_neg
  CompatibleZeroL.funMap_zero CompatibleOneL.funMap_one CompatibleTopL.funMap_infty
  CompatibleOrderL.realize_orderF

/-- Compatibility of an additive monoid language. -/
class CompatibleAMonoidL [AMonoidL L s] [Add (M s)] [Zero (M s)] : Prop
    extends CompatibleAddL L M s, CompatibleZeroL L M s

/-- Compatibility of an additive group language. -/
class CompatibleAGroupL [AGroupL L s] [Add (M s)] [Neg (M s)] [Zero (M s)] : Prop
    extends CompatibleAMonoidL L M s, CompatibleNegL L M s

/-- Compatibility of a multiplicative monoid language. -/
class CompatibleMMonoidL [MMonoidL L s] [Mul (M s)] [One (M s)] : Prop
    extends CompatibleMulL L M s, CompatibleOneL L M s

/-- Compatibility of an ordered additive group language. -/
class CompatibleOAGroupL [OAGroupL L s] [Add (M s)] [Neg (M s)] [Zero (M s)] [LE (M s)] : Prop
    extends CompatibleAGroupL L M s, CompatibleOrderL L M s

/-- Compatibility of a ring language. -/
class CompatibleRingL [RingL L s] [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)] :
    Prop extends CompatibleAGroupL L M s, CompatibleMMonoidL L M s

/-- Compatibility of an ordered ring language. -/
class CompatibleORingL [ORingL L s] [Add (M s)] [Mul (M s)] [Neg (M s)] [Zero (M s)] [One (M s)]
    [LE (M s)] : Prop extends CompatibleRingL L M s, CompatibleOrderL L M s

/-! ### Term and formula notation -/

section Notation

variable {L M s} {Γ σ : Arity S}

/-- The sum of two terms. -/
abbrev AddL.addT [AddL L s] (t₁ t₂ : L.Term Γ ⦃s⦄) : L.Term Γ ⦃s⦄ :=
  .func AddL.addFunc (.prod t₁ t₂)

/-- The product of two terms. -/
abbrev MulL.mulT [MulL L s] (t₁ t₂ : L.Term Γ ⦃s⦄) : L.Term Γ ⦃s⦄ :=
  .func MulL.mulFunc (.prod t₁ t₂)

/-- The negation of a term. -/
abbrev NegL.negT [NegL L s] (t : L.Term Γ ⦃s⦄) : L.Term Γ ⦃s⦄ := .func NegL.negFunc t

/-- The infinity constant as a term. -/
abbrev InfinityL.inftyT [InfinityL L s] : L.Term Γ ⦃s⦄ := .func InfinityL.inftyConst .nil

@[inherit_doc] scoped[ManySorted] infixl:65 " +ₗ " => ManySorted.Language.AddL.addT
@[inherit_doc] scoped[ManySorted] infixl:70 " *ₗ " => ManySorted.Language.MulL.mulT
@[inherit_doc] scoped[ManySorted] prefix:75 "-ₗ" => ManySorted.Language.NegL.negT
@[inherit_doc] scoped[ManySorted] notation "`∞" => ManySorted.Language.InfinityL.inftyT

instance [ZeroL L s] : Zero (L.Term Γ ⦃s⦄) := ⟨.func ZeroL.zeroConst .nil⟩

instance [OneL L s] : One (L.Term Γ ⦃s⦄) := ⟨.func OneL.oneConst .nil⟩

@[simp]
theorem realize_zero [ZeroL L s] [Zero (M s)] [CompatibleZeroL L M s]
    (xs : M [^] Γ) : (0 : L.Term Γ ⦃s⦄).realize xs = (0 : M s) :=
  CompatibleZeroL.funMap_zero

@[simp]
theorem realize_one [OneL L s] [One (M s)] [CompatibleOneL L M s]
    (xs : M [^] Γ) : (1 : L.Term Γ ⦃s⦄).realize xs = (1 : M s) :=
  CompatibleOneL.funMap_one

/-- `t ≤ₗ u`: the order formula applied to two terms. -/
def OrderL.leF [OrderL L s] (t u : L.Term σ ⦃s⦄) : L.Formula σ :=
  OrderL.orderF.subst (.prod t u)

@[inherit_doc] scoped[ManySorted] infix:50 " ≤ₗ " => ManySorted.Language.OrderL.leF

@[simp]
theorem realize_leF [OrderL L s] [LE (M s)] [CompatibleOrderL L M s]
    (t u : L.Term σ ⦃s⦄) (xs : M [^] σ) :
    (t ≤ₗ u).Realize xs ↔ t.realize xs ≤ u.realize xs := by
  simp [OrderL.leF]

end Notation

/-! ### Operations read off from a structure -/

section ModelAlgebra

/-- Addition on sort `s`, read off from the structure. -/
@[reducible] def modelAdd [AddL L s] : Add (M s) :=
  ⟨fun a b => funMap (L := L) AddL.addFunc ((a, b) : M [^] (⦃s⦄ ⨯ ⦃s⦄))⟩

/-- Multiplication on sort `s`, read off from the structure. -/
@[reducible] def modelMul [MulL L s] : Mul (M s) :=
  ⟨fun a b => funMap (L := L) MulL.mulFunc ((a, b) : M [^] (⦃s⦄ ⨯ ⦃s⦄))⟩

/-- Negation on sort `s`, read off from the structure. -/
@[reducible] def modelNeg [NegL L s] : Neg (M s) := ⟨fun a => funMap (L := L) NegL.negFunc a⟩

/-- Zero on sort `s`, read off from the structure. -/
@[reducible] def modelZero [ZeroL L s] : Zero (M s) :=
  ⟨funMap (L := L) (M := M) (ZeroL.zeroConst (s := s)) PUnit.unit⟩

/-- One on sort `s`, read off from the structure. -/
@[reducible] def modelOne [OneL L s] : One (M s) :=
  ⟨funMap (L := L) (M := M) (OneL.oneConst (s := s)) PUnit.unit⟩

/-- The top element `∞` on sort `s`, read off from the structure. -/
@[reducible] def modelTop [InfinityL L s] : Top (M s) :=
  ⟨funMap (L := L) (M := M) (InfinityL.inftyConst (s := s)) PUnit.unit⟩

/-- The order on sort `s`, read off from the structure. -/
@[reducible] def modelLE [OrderL L s] : LE (M s) :=
  ⟨fun a b => (OrderL.orderF (L := L) (s := s)).Realize ((a, b) : M [^] (⦃s⦄ ⨯ ⦃s⦄))⟩

/-- The ring operations read off from the structure are compatible with it. -/
theorem modelRingCompatible [RingL L s] :
    letI := modelAdd L M s
    letI := modelMul L M s
    letI := modelNeg L M s
    letI := modelZero L M s
    letI := modelOne L M s
    CompatibleRingL L M s :=
  letI := modelAdd L M s
  letI := modelMul L M s
  letI := modelNeg L M s
  letI := modelZero L M s
  letI := modelOne L M s
  { funMap_add := fun _ => rfl, funMap_mul := fun _ => rfl, funMap_neg := fun _ => rfl,
    funMap_zero := rfl, funMap_one := rfl }

/-- The group operations and the order read off from the structure are compatible with it. -/
theorem modelOAGroupCompatible [OAGroupL L s] :
    letI := modelAdd L M s
    letI := modelNeg L M s
    letI := modelZero L M s
    letI := modelLE L M s
    CompatibleOAGroupL L M s :=
  letI := modelAdd L M s
  letI := modelNeg L M s
  letI := modelZero L M s
  letI := modelLE L M s
  { funMap_add := fun _ => rfl, funMap_neg := fun _ => rfl, funMap_zero := rfl,
    realize_orderF := fun _ => Iff.rfl }

/-- The `∞` read off from the structure is compatible with it. -/
theorem modelTopCompatible [InfinityL L s] :
    letI := modelTop L M s
    CompatibleTopL L M s :=
  letI := modelTop L M s
  { funMap_infty := rfl }

end ModelAlgebra

end ManySorted.Language
