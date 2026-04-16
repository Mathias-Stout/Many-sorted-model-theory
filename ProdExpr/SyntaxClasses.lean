import ProdExpr.Syntax
import Mathlib.Data.List.Basic

universe u v w z u' v' w'

namespace MSFirstOrder

namespace MSLanguage

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
variable {M : Fam.{w} Sorts} {α : Fam.{u'} Sorts} {β : Fam.{v'} Sorts} {γ : Fam Sorts}

section quant_notation

namespace BoundedFormula

open MSFirstOrder.MSLanguage.Term Signature

-- ==========================================================
-- 1. Variable Indexing
-- ==========================================================

/--
Typeclass to resolve a numeric index `n` into a specific `Idx`.
This class is only meant to apply to "stack-shaped" Signatures
of the form `(⦃s⦄ × ...) ⨯ ⦃t⦄) ⨯ ⦃s⦄`
-/
class VarIndex (σ : Signature Sorts) (n : ℕ) (s : outParam Sorts) where
  get : σ.Idx s

-- Case 0: Base Case (Index 0 in a singleton context)
-- This allows variables to be found at the very bottom of the stack.
@[simp]
instance instVarIndexBase {s : Sorts} :
    VarIndex (.of s) 0 s where
  get := .var

-- Case 1: Index 0 matches the top of the stack (right-most element)
@[simp]
instance instVarIndexZero {σ : Signature Sorts} {s : Sorts} :
    VarIndex (σ ⨯ (.of s)) 0 s where
  get := .right .var

-- Case 2: Recursion (look deeper into the stack)
@[simp]
instance instVarIndexSucc {σ τ : Signature Sorts} {n : ℕ} {s : Sorts}
    [h : VarIndex σ n s] :
    VarIndex (σ ⨯ τ) (n + 1) s where
  get := .left h.get

namespace deBruijnVar

-- Syntax for variables: #0, #1
scoped syntax:max "#" term:max : term

scoped macro_rules
| `(# $n) => `(Term.var _ (Sum.inr (VarIndex.get (n := $n))))

end deBruijnVar

open scoped deBruijnVar
-- ==========================================================
-- 2. Polymorphic Quantification
-- ==========================================================

variable {s : Sorts}

/--
Typeclass for overloading quantifiers.
Arguments:
- `p`: The value being quantified (`Sorts` or `Signature Sorts`).
- `Outer`: The signature outside the quantifier.
- `Inner`: The signature inside the quantifier (Output Parameter).
-/
class Quantifiable {P : Type w} (p : P) (Outer : Signature Sorts)
                            (Inner : outParam (Signature Sorts)) where
  mkAll : L.BoundedFormula α Inner → L.BoundedFormula α Outer
  mkEx  : L.BoundedFormula α Inner → L.BoundedFormula α Outer

-- Handles ∀' s where the result is a Sentence (removes .of s context)
-- Automatically handles the casting of formulas to append a .nil on
-- the left.
@[simp]
instance (priority := 2000) instSortQuantRoot {s : Sorts} :
    Quantifiable (L:=L) (α:=α) s .nil (.of s) where
  mkAll φ :=
    let φ_casted := φ.reindex (SigEquiv.nilLeft (.of s)).symm
    BoundedFormula.all (.of s) φ_casted
  mkEx φ :=
    let φ_casted := φ.reindex (SigEquiv.nilLeft (.of s)).symm
    BoundedFormula.ex (.of s) φ_casted

/--
Handles ∀' s inside a product (adds .of s to the stack)
This is separate from ProdQuant so that we can
implement custom notation here that allows us to
write `∀' s φ` instead of `∀' (.of s) φ`
-/
@[simp]
instance instSortQuant {σ : Signature Sorts} {s : Sorts} :
    Quantifiable (L:=L) (α:=α) s σ (σ ⨯ (.of s)) where
  mkAll φ := BoundedFormula.all (.of s) φ
  mkEx  φ := BoundedFormula.ex (.of s) φ

-- Handles ∀' τ (Signature)
@[simp]
instance instProdQuant {σ : Signature Sorts} {τ : Signature Sorts} :
    Quantifiable (L:=L) (α:=α) τ σ (σ ⨯ τ) where
  mkAll φ := BoundedFormula.all τ φ
  mkEx  φ := BoundedFormula.ex τ φ

-- ==========================================================
-- 3. Syntax Helpers # Notation
-- ==========================================================

/--
Helper function that takes `p` explicitly.
We use explicit application (@) to pass all implicit arguments manually.
This prevents "type mismatch" and inference errors.
-/
@[inline, simp]
def mkAll_helper {P : Type w} (p : P) {Outer Inner : Signature Sorts}
    [inst : Quantifiable (L := L) (α := α) p Outer Inner]
    (φ : L.BoundedFormula α Inner) : L.BoundedFormula α Outer :=
  @Quantifiable.mkAll _ L α _ p Outer Inner inst φ

@[inline, simp]
def mkEx_helper {P : Type w} (p : P) {Outer Inner : Signature Sorts}
    [inst : Quantifiable (L := L) (α := α) p Outer Inner]
    (φ : L.BoundedFormula α Inner) : L.BoundedFormula α Outer :=
  @Quantifiable.mkEx _ L α _ p Outer Inner inst φ

scoped[MSFirstOrder] notation:110 (name := poly_forall) "∀'" p:max φ:110 =>
  MSFirstOrder.MSLanguage.BoundedFormula.Quantifiable.mkAll p φ

scoped[MSFirstOrder] notation:110 (name := poly_exists) "∃'" p:max φ:110 =>
  MSFirstOrder.MSLanguage.BoundedFormula.Quantifiable.mkEx p φ

/--
`∀*[ s1, s2, ... ] φ`
Expands to `∀' s1 (∀' s2 ... φ)`
-/
syntax "∀*[" term,* "]" term : term
macro_rules
  | `(∀*[ ] $phi) => `($phi)
  | `(∀*[ $s ] $phi) => `(∀' $s $phi)
  | `(∀*[ $s, $rest,* ] $phi) => `(∀' $s (∀*[ $rest,* ] $phi))

/--
`∃⨯[ s1, s2, ... ] φ`
Expands to `∃' s1 (∃' s2 ... φ)`
-/
syntax "∃*[" term,* "]" term : term
macro_rules
  | `(∃*[ ] $phi) => `($phi)
  | `(∃*[ $s ] $phi) => `(∃' $s $phi)
  | `(∃*[ $s, $rest,* ] $phi) => `(∃' $s (∃*[ $rest,* ] $phi))

end BoundedFormula
end quant_notation

open BoundedFormula Signature

namespace Relations

open Signature Idx

open scoped deBruijnVar

variable {s : Sorts}
variable (r : L.Relations (⦃s⦄ ⨯ ⦃s⦄))

/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.Sentence :=
  ∀' s (r.boundedFormula₂ #0 #0)

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.Sentence :=
  ∀' s (r.boundedFormula₂ #0 #0).not

/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.Sentence :=
  ∀*[s, s] (r.boundedFormula₂ #0 #1 ⟹ r.boundedFormula₂ #1 #0)

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.Sentence :=
  ∀*[s, s] (r.boundedFormula₂ #0 #1 ⟹ r.boundedFormula₂ #1 #0  ⟹ Term.bdEqual #0 #1)

/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.Sentence :=
  ∀*[s, s, s] (r.boundedFormula₂ #0 #1 ⟹ r.boundedFormula₂ #1 #2 ⟹ r.boundedFormula₂ #0 #2)

/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.Sentence :=
  ∀*[s, s] (r.boundedFormula₂ #0 #1 ⊔ r.boundedFormula₂ #1 #0)

end Relations

end MSLanguage

end MSFirstOrder
