# About

The first goal of this repository is to formalize a framework for many-sorted logic in Lean4.
We aim to extend the current one-sorted definitions and theorems in [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html), with the goal of developing a stable base for formalizing more advanced results, in particular around the model theory of valued fields.

## Feedback welcome!

We very much appreciate any feedback and comments, especially on the fundamental definitions `MSLanguage`, `MSStructure`, `Term`, `BoundedFormula`.
Feel free to add any comments to this [Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Many-sorted.20model.20theory) thread, which already includes some great suggestions. The goal is to find definitions which are convenient both for foundational development as well as actually doing model theory.

You can also contact us directly via our institutional emails: [Aaron Crighton](mailto:acrighto@fields.utoronto.ca), [John Nicholson](mailto:nichoj6@mcmaster.ca), [Mathias Stout](mailto:stoutm1@mcmaster.ca).


## Contributing

As our end goal is to make formalization more accessible to the wider model theory community, we welcome any interested contributors.
In that spirit, all definitions are still very much susceptible to change.
Fixes, small upgrades and partial reworks are all welcome, but there is currently no public blueprint.

## Repository structure

This repository generalizes the one-sorted setup for first-order logic currently in Mathlib to many sorts. Files with similar names to the existing Mathlib files indicate similar, but more general developments.

The Examples folder contains the statements of some basic `L`-theories for various first-order languages `L` and links them back to the corresponding Mathlib objects.

## About many-sorted first-order logic

In one-sorted first-order logic, one considers a language `L` which contains function and relation symbols that are used to talk about a single set `M`. An example is given by the group language `L_group = {*,1,(·)⁻¹}`. This language is naturally interpreted in any group `G`, where the purely syntactic symbols from `L_group` gain meaning as actual functions `*_G, 1_G, (·)⁻¹_G`.

Many-sorted logic is useful to talk about structures that are made up of many different interacting sets or 'sorts' (Note: this notion of sorts is independent of Lean's notion of `Sort`). A particularly relevant example is that of valued fields. Their model theory is often studied in a three-sorted setting with sorts `VF, RF, VG` for respectively the valued field, residue field and value group. A language `L` on these three sorts might include a function symbol for the valuation `v`, with domain `VF` and target `VG`.

As a note to those familiar with many-sorted logic: an important reason for developing a proper multi-sorted logic framework is the need to handle infinitely many sorts at once for more advanced results on e.g. elimination of imaginaries down the line.

## Some notes on the current definitions

The basic definitions of Languages and structures here were influenced by this [Lean Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Many-sorted.20model.20theory), in particular by the suggestion of Adam Topaz.

### Signature (of function symbols and formulas)

The key idea behind encoding the signature of function and relation symbols is that they will be interpreted as actual functions on an (inhomogeneous) product of types.
Hence, they should reflect the fact that the product of types is not associative: `(X x Y) x Z ≠ X x (Y x Z)` (though there is a canonical isomorphism).

Concretely, we have the following definitions in `Signature.lean`
````lean4
inductive Signature (S : Type u) where
  | nil  : Signature S
  | of   : S → Signature S
  | prod : Signature S → Signature S → Signature S
````

````lean4
@[reducible]
def Signature.Interpret {S : Type u} (X : Fam.{v} S) : Signature S → Type v
  | 0         => PUnit
  | .of s     => X s
  | prod a b  => Interpret X a × Interpret X b

notation:80 X " [^] " σ:81 => MSFirstOrder.Signature.Interpret X σ
````

### Many-sorted languages and structures

A many-sorted language then consists of a collection of (possibly empty) function and relation symbols for each signature. Again, note that the use of the word 'sort' in model theory is orthogonal to Lean's `Sort`.

````lean4
structure Language (S : Type z) where
  Functions : Signature S → S → Type u
  Relations : Signature S → Type v
````

The notion of a structure is a class on a dependent type over the sorts `S` of the language. It carries interpretations of all of the function and relation symbols, on the correct cartesian product of types.

````lean4
class Structure {S} (L : Language S) (M : Fam.{w} S) where
  funMap : ∀ {σ t}, L.Functions σ t → M [^] σ → M t := by
      exact fun {σ} => fun {t} => isEmptyElim
  RelMap : ∀ {σ}, L.Relations σ → (M [^] σ)  → Prop := by
      exact fun {σ} => isEmptyElim
````

### Terms and formulas

The next step is the inductive definition of terms. Note that we immediately define tuples of terms as basic syntactic objects. This helps eliminate tedious casts that would otherwise be associated to plugging in dependent tuples of terms into other terms.

````lean4
inductive Term (L : Language.{u, v, z} Sorts) (α : Fam.{u'} Sorts) :
    Signature Sorts → Type max z u' u where
| var (s : Sorts) : α s → L.Term α (of s)
| func {σ : Signature Sorts} {t : Sorts} (f : L.Functions σ t) (r : L.Term α σ) : L.Term α (.of t)
| prod {σ τ : Signature Sorts} : L.Term α σ → L.Term α τ → L.Term α (σ ⨯ τ)
| nil : L.Term α .nil
````

Finally, formulas are built up inductively as in the first-order case. As in Mathlib, there are two families of variables around: one dependent family of names `α` and one family of indexed variables which act like de Bruijn indices. Intuitively, a `L.BoundedFormula α σ` corresponds to the semantic notion of an `α`-definable set in the Cartesian product `M [^] σ` (see `Signature.Intepret` above).

````lean4
/-- A bounded formula for a many-sorted language `L`, with free variables in `α`. -/
inductive BoundedFormula (α : Fam.{u'} Sorts) : Signature Sorts → Type (max u v z u')
  | falsum {σ} : BoundedFormula α σ
  | equal {σ τ}  (t₁ t₂ : L.Term (α ⊕ₛ σ.IdxFam) τ) : BoundedFormula α σ
  | rel {σ σ'} (R : L.Relations σ') (ts : (L.Term (α ⊕ₛ σ.IdxFam) σ')) :  BoundedFormula α σ
  /-- The logical implication of two bounded formulas-/
  | imp {σ} (f₁ f₂ : BoundedFormula α σ) :  BoundedFormula α σ
  /-- Adds a universal quantifier to a bounded formula-/
  | all {σ} (τ) (f : BoundedFormula α (σ ⨯ τ)) :  BoundedFormula α σ
````

## References

The files `Basic.lean`, `LanguageMap.lean`, `Syntax.lean` and `Semantics.lean` in both folders are based on the files with the same name from [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html#FirstOrder.Language.Structure), authored by Aaron Anderson, Jesse Michael Han and Floris van Doorn. First versions of this appeared in the Flypitch project:

- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*](https://flypitch.github.io/papers/)
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*](https://flypitch.github.io/papers/)
