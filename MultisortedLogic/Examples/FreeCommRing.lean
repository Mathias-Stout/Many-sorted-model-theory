import Mathlib.RingTheory.FreeCommRing
import MultisortedLogic.Examples.Ring

/-!
# Making a term in the language of rings from an element of the FreeCommRing

This file defines the function `MSFirstOrder.Ring.termOfFreeCommRing` which constructs a
`Language.ring.Term α` from an element of `FreeCommRing α`.

The theorem `MSFirstOrder.Ring.realize_termOfFreeCommRing` shows that the term constructed when
realized in a ring `R` is equal to the lift of the element of `FreeCommRing α` to `R`.
-/

section

namespace MSFirstOrder
open Language Term

universe u v w z u' v' w' z'
variable {Sorts : Type z}
variable {L : Language Sorts}
variable {M : Fam Sorts}
variable {α : Sorts → Type u'}
variable {σ : Signature Sorts}
variable {s : Sorts}

variable [RingL L s] [Ring (M s)] [L.Structure M] [CompatibleRingL L M s]

section

inductive PolyTerm (β : Type _)


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

end
-/
/-
/-- Make a `Language.ring.Term α` from an element of `FreeCommRing α` -/
noncomputable def termOfFreeCommRing (p : FreeCommRing (α s)) : Language.ring.Term α ⦃s⦄ :=
  Classical.choose (exists_term_realize_eq_freeCommRing p)

variable {R : Type*} [CommRing R] [CompatibleRing R]

@[simp]
theorem realize_termOfFreeCommRing (p : FreeCommRing α) (v : α → R) :
    (termOfFreeCommRing p).realize v = FreeCommRing.lift v p := by
  rw [termOfFreeCommRing]
  conv_rhs => rw [← Classical.choose_spec (exists_term_realize_eq_freeCommRing p)]
  induction Classical.choose (exists_term_realize_eq_freeCommRing p) with
  | var _ => simp?
  | func f a ih =>
    cases f <;>
    simp? [ih]

end Ring
-/
end
end MSFirstOrder
end
