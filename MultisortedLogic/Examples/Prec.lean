import Mathlib.Order.Basic

class Prec (α : Type*) where
  prec : α → α → Prop

infix:50 " ≼ " => Prec.prec

/- Claude-generated code that may be relevant later
namespace Prec
class IsPreorder (α : Type*) extends Prec α where
  prec_refl : ∀ a : α, a ≼ a
  prec_trans : ∀ {a b c : α}, a ≼ b → b ≼ c → a ≼ c

-- Make these available as simp lemmas and with nicer names
section BasicLemmas
variable [IsPreorder α] {a b c d : α}

@[refl, simp]
theorem prec_refl (a : α) : a ≼ a := IsPreorder.prec_refl a

theorem Prec.rfl : a ≼ a := prec_refl a

@[trans]
theorem prec_trans (hab : a ≼ b) (hbc : b ≼ c) : a ≼ c :=
  IsPreorder.prec_trans hab hbc

theorem prec_trans' (hbc : b ≼ c) (hab : a ≼ b) : a ≼ c :=
  prec_trans hab hbc

instance : Trans (α := α) (· ≼ ·) (· ≼ ·) (· ≼ ·) where
  trans := prec_trans

end BasicLemmas

-- Strict version of the relation
class IsStrictPreorder (α : Type*) extends Prec α where
  prec_irrefl : ∀ a : α, ¬(a ≼ a)  -- Note: this contradicts IsPreorder, pick one
  prec_trans : ∀ {a b c : α}, a ≼ b → b ≼ c → a ≼ c

-- Or define strict version separately
def StrictPrec [Prec α] (a b : α) : Prop := a ≼ b ∧ ¬(b ≼ a)

infix:50 " ≺ " => StrictPrec

section StrictLemmas
variable [IsPreorder α] {a b c : α}

theorem StrictPrec.prec (h : a ≺ b) : a ≼ b := h.1

theorem StrictPrec.not_prec (h : a ≺ b) : ¬(b ≼ a) := h.2

theorem StrictPrec.irrefl (a : α) : ¬(a ≺ a) := fun ⟨_, h⟩ => h (prec_refl a)

theorem StrictPrec.asymm (h : a ≺ b) : ¬(b ≺ a) := fun ⟨hba, _⟩ => h.2 hba

theorem StrictPrec.trans_prec (hab : a ≺ b) (hbc : b ≼ c) : a ≺ c := by
  constructor
  · exact prec_trans hab.1 hbc
  · intro hca
    exact hab.2 (prec_trans hbc hca)

theorem Prec.trans_strict (hab : a ≼ b) (hbc : b ≺ c) : a ≺ c := by
  constructor
  · exact prec_trans hab hbc.1
  · intro hca
    exact hbc.2 (prec_trans hca hab)

theorem StrictPrec.trans (hab : a ≺ b) (hbc : b ≺ c) : a ≺ c :=
  hab.trans_prec hbc.1

instance : Trans (α := α) (· ≺ ·) (· ≺ ·) (· ≺ ·) where
  trans := StrictPrec.trans

instance : Trans (α := α) (· ≺ ·) (· ≼ ·) (· ≺ ·) where
  trans := StrictPrec.trans_prec

instance : Trans (α := α) (· ≼ ·) (· ≺ ·) (· ≺ ·) where
  trans := Prec.trans_strict

end StrictLemmas

-- Equivalence relation induced by the preorder
def PrecEquiv [Prec α] (a b : α) : Prop := a ≼ b ∧ b ≼ a

infix:50 " ≈ᵖ " => PrecEquiv

section EquivLemmas
variable [IsPreorder α] {a b c : α}

@[refl, simp]
theorem PrecEquiv.refl (a : α) : a ≈ᵖ a := ⟨prec_refl a, prec_refl a⟩

@[symm]
theorem PrecEquiv.symm (h : a ≈ᵖ b) : b ≈ᵖ a := ⟨h.2, h.1⟩

@[trans]
theorem PrecEquiv.trans (hab : a ≈ᵖ b) (hbc : b ≈ᵖ c) : a ≈ᵖ c :=
  ⟨prec_trans hab.1 hbc.1, prec_trans hbc.2 hab.2⟩

theorem PrecEquiv.prec (h : a ≈ᵖ b) : a ≼ b := h.1

theorem PrecEquiv.prec' (h : a ≈ᵖ b) : b ≼ a := h.2

-- The equivalence classes form a partial order (stated abstractly)
theorem prec_antisymm_of_equiv (h1 : a ≼ b) (h2 : b ≼ a) : a ≈ᵖ a := PrecEquiv.refl a

end EquivLemmas

-- Decidability
class DecidablePrec (α : Type*) [Prec α] where
  decidable : DecidableRel (Prec.prec (α := α))

instance [Prec α] [DecidablePrec α] : DecidableRel (Prec.prec (α := α)) :=
  DecidablePrec.decidable

-- Min/Max operations (require decidability or linearity)
section MinMax
variable [Prec α] [DecidablePrec α]

def precMin (a b : α) : α := if a ≼ b then a else b
def precMax (a b : α) : α := if a ≼ b then b else a

end MinMax

-- Monotonicity
def PrecMono [Prec α] [Prec β] (f : α → β) : Prop :=
  ∀ {a b}, a ≼ b → f a ≼ f b

def StrictPrecMono [Prec α] [Prec β] (f : α → β) : Prop :=
  ∀ {a b}, a ≺ b → f a ≺ f b

section MonoLemmas
variable [IsPreorder α] [IsPreorder β] {f : α → β}

theorem PrecMono.comp {g : β → γ} [IsPreorder γ]
    (hg : PrecMono g) (hf : PrecMono f) : PrecMono (g ∘ f) :=
  fun hab => hg (hf hab)

theorem PrecMono.id : PrecMono (id : α → α) := fun h => h

end MonoLemmas

-- Connecting to the standard LE class
/-- Every `Preorder` gives rise to an `IsPreorder` -/
instance [Preorder α] : @IsPreorder α ⟨(· ≤ ·)⟩ where
  prec_refl := le_refl
  prec_trans := fun h1 h2 => le_trans h1 h2

/-- Create an `IsPreorder` from a relation with the right properties -/
def IsPreorder.mk' {α : Type*} (r : α → α → Prop)
    (refl : ∀ a, r a a)
    (trans : ∀ {a b c}, r a b → r b c → r a c) :
    @IsPreorder α ⟨r⟩ where
  prec_refl := refl
  prec_trans := trans

-/
