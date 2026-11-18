# About

The first goal of this repository is to formalize a framework for many-sorted logic in Lean4.
We extend the current one-sorted definitions and theorems in [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html), providing a suitable API for formalizing more advanced results, in particular around the model theory of valued fields. As a proof of concept, this repository contains autoformalized proofs of quantifier elimination for three theories, each built on the quantifier-elimination criteria of the library:

- `ACF_hasQERelTo_empty` ([Algebra/ACF/QE.lean](MultisortedLogic/Algebra/ACF/QE.lean)): algebraically closed fields, in the language of rings;
- `DOAG_hasQERelTo_empty` ([Algebra/DOAG/QE.lean](MultisortedLogic/Algebra/DOAG/QE.lean)): nontrivial divisible ordered abelian groups, in the language of ordered abelian groups;
- `ACVF_hasQERelTo_empty` ([Algebra/ACVF/QE.lean](MultisortedLogic/Algebra/ACVF/QE.lean)): algebraically closed fields with a nontrivial valuation, in the three-sorted leading-term language with sorts `K`, `RV` and `Γ`, following the notes of [Silvain Rideau-Kikuchi](https://www.math.ens.psl.eu/~rideau/teaching/val/vf.pdf).

In the near future, we plan to integrate this with Mathlib, where relevant, and formalize relative quantifier elimination in Henselian valued fields.

## Feedback welcome!

We very much appreciate any feedback and comments, especially on the fundamental definitions `Language`, `Structure`, `Term`, `Formula`.
Feel free to add any comments to this [Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Many-sorted.20model.20theory) thread, which already includes some great suggestions. The goal is to find definitions which are convenient both for foundational development as well as actually doing model theory.

You can also contact us directly via our institutional emails: [Aaron Crighton](mailto:acrighto@fields.utoronto.ca), [John Nicholson](mailto:nichoj6@mcmaster.ca), [Mathias Stout](mailto:stoutm1@mcmaster.ca), [Jonas van der Schaaf](mailto:jonas.vanderschaaf@uni-muenster.de).


## Contributing

As our end goal is to make formalization more accessible to the wider model theory community, we welcome any interested contributors.
In that spirit, all definitions are still very much susceptible to change.
Fixes, small upgrades and partial reworks are all welcome.
In particular, suggestions on how to incorporate metaprogramming to improve the end-user experience are very welcome.

## Repository structure

Part of this repository generalizes the one-sorted setup for first-order logic currently in Mathlib to many sorts. Files with similar names to the existing Mathlib files indicate similar, but more general developments.

The top-level folder [MultisortedLogic](MultisortedLogic/) contains our basic development of many-sorted first-order logic, as well as basic model-theoretic results, including [Łoś's Theorem](MultisortedLogic/Ultraproducts.lean), the [Löwenheim–Skolem theorems](MultisortedLogic/LowenheimSkolem.lean), and the [Compactness Theorem](MultisortedLogic/Satisfiability.lean).
These developments are inspired by their corresponding one-sorted analogues in Mathlib.

Additionally, we formalized embedding tests for relative quantifier elimination: the definitions and the one-sort syntactic criterion are in [QuantifierElimination](MultisortedLogic/QuantifierElimination.lean), separation and the tuple-extension criteria in [Separation](MultisortedLogic/Separation.lean), partial maps in [PartialMaps](MultisortedLogic/PartialMaps.lean), and the embedding test with its variants on substructures in [EmbeddingTest](MultisortedLogic/EmbeddingTest.lean).

The folder [Algebra](MultisortedLogic/Algebra/) applies this framework to algebra. It contains operator languages for the usual algebraic operations and orders ([Basic](MultisortedLogic/Algebra/Basic.lean)), the theories of groups, rings, fields and orders, and the three quantifier-elimination developments: [ACF](MultisortedLogic/Algebra/ACF/), [DOAG](MultisortedLogic/Algebra/DOAG/) and [ACVF](MultisortedLogic/Algebra/ACVF/).
The module documentation of [Algebra/ACVF/QE.lean](MultisortedLogic/Algebra/ACVF/QE.lean) is a guide to the proof for ACVF.

The folder [AlgebraicBackground](MultisortedLogic/AlgebraicBackground/) contains the algebra these proofs use, with no model theory: lemmas about fields, ordered groups and the leading-term structure `RV` of a valued field.

## About many-sorted first-order logic

In one-sorted first-order logic, one considers a language `L` which contains function and relation symbols that are used to talk about a single set `M`. An example is given by the language of groups `L_group = {*,1,(·)⁻¹}`. This language is naturally interpreted in any group `G`, where the purely syntactic symbols from `L_group` gain meaning as actual functions `*_G, 1_G, (·)⁻¹_G`.

Many-sorted logic is useful to talk about structures that are made up of many different interacting sets or 'sorts' (Note: this notion of sorts is independent of Lean's notion of `Sort`). A particularly relevant example is that of valued fields. Their model theory is often studied in a three-sorted setting with sorts `VF, RF, VG` for respectively the valued field, residue field and value group. A language `L` on these three sorts might include a function symbol for the valuation `v`, with domain `VF` and target `VG`.

As a note to those familiar with many-sorted logic: an important reason for developing a proper many-sorted logic framework is the need to handle infinitely many sorts at once for more advanced results which we plan to tackle in the future, e.g. elimination of imaginaries in ACVF.

## Some notes on the current definitions

The basic definitions of Languages and structures here were influenced by this [Lean Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Many-sorted.20model.20theory), in particular by the suggestion of Adam Topaz.

### Arity (of function symbols and formulas)

Function and relation symbols in a many-sorted language are purely syntactic objects, which simply record the domain/range their interpretations in a concrete structure should have.
We encode their domains by a custom inductive type called `Arity`, which records the product of sorts their interpretations will operate on.
As a mathematical structure, `Arity` is a non-associative magma, which reflects the fact that the product of types is not associative: `(X × Y) × Z ≠ X × (Y × Z)` (though there is a canonical isomorphism).

Concretely, we have the following definitions in `Basic.lean`, which encodes an 'arity' of a function or relation symbol on (model-theoretic) sorts `S`.
````lean4
inductive Arity (S : Type z) where
  /-- The empty product. -/
  | nil : Arity S
  /-- A single sort. -/
  | of : S → Arity S
  /-- The product of two arities. -/
  | prod : Arity S → Arity S → Arity S
````

Every `Arity` can be interpreted as a product of types.

````lean4
/-- `M [^] σ` is the product of the carriers `M s` over the sorts of `σ`, bracketed like `σ`.
For a single sort it is `M s` itself. -/
@[reducible] def Interpret (M : S → Type w) : Arity S → Type w
  | ⦃⦄ => PUnit
  | ⦃s⦄ => M s
  | σ ⨯ τ => Interpret M σ × Interpret M τ

notation:80 M " [^] " σ:81 => ManySorted.Arity.Interpret M σ
````

Any `σ : Arity` can be viewed as a binary tree with leaves labeled by the set of sorts `S`. Given a specific sort `s : S`, `σ.Idx s` represents all the leaves that have label `s`.

````lean4
/-- `σ.Idx s` is the type of positions of sort `s` in the arity `σ`. Short for 'Index'. -/
inductive Idx : Arity S → S → Type z
  /-- The unique position of `⦃s⦄`. -/
  | var {s : S} : Idx ⦃s⦄ s
  /-- A position in the left factor of a product. -/
  | left {σ τ : Arity S} {s : S} : Idx σ s → Idx (σ ⨯ τ) s
  /-- A position in the right factor of a product. -/
  | right {σ τ : Arity S} {s : S} : Idx τ s → Idx (σ ⨯ τ) s
````

### Many-sorted languages and structures

A many-sorted language then consists of (possibly empty) collections of function and relation symbols, one for each `Arity`, and target sort (in the case of functions). Again, note that the use of the word 'sort' in model theory is orthogonal to Lean's `Sort`.

````lean4
structure Language (S : Type z) where
  /-- The function symbols `σ → t`. -/
  Functions : Arity S → S → Type u
  /-- The relation symbols on `σ`. -/
  Relations : Arity S → Type v
````

A structure `M` for a language `L` is encoded as a class on a dependent type over the sorts `S` of the language. It carries interpretations of all of the function and relation symbols, on the correct Cartesian product of types.

````lean4
/-- An `L`-structure on a family of carriers `M`. -/
class Structure (M : S → Type w) where
  /-- The interpretation of a function symbol. -/
  funMap : ∀ {σ t}, L.Functions σ t → M [^] σ → M t
  /-- The interpretation of a relation symbol. -/
  RelMap : ∀ {σ}, L.Relations σ → M [^] σ → Prop
````

### Terms and formulas

Before we can define the notion of first-order formulas in a language `L`, we must first define `L`-terms.
Note that we immediately define tuples of terms as basic syntactic objects. This helps eliminate tedious casts that would otherwise be associated to plugging in dependent tuples of terms into other terms.

````lean4
/-- `L.Term Γ σ` is the type of tuples of terms of shape `σ` that take in arguments of shape `Γ`.
A single term of sort `s` is an `L.Term Γ ⦃s⦄`. -/
inductive Term (Γ : Arity S) : Arity S → Type (max z u)
  /-- Picking out a single variable (position) in the tuple `Γ`. -/
  | var {s : S} (i : Γ.Idx s) : Term Γ ⦃s⦄
  /-- A function symbol applied to a tuple of terms. -/
  | func {σ : Arity S} {t : S} (f : L.Functions σ t) (ts : Term Γ σ) : Term Γ ⦃t⦄
  /-- The empty tuple. -/
  | nil : Term Γ ⦃⦄
  /-- The pairing of two tuples. -/
  | prod {σ τ : Arity S} (t₁ : Term Γ σ) (t₂ : Term Γ τ) : Term Γ (σ ⨯ τ)
````

Formulas are built up inductively, similarly to the one-sorted development in Mathlib.
There is one major difference: Mathlib's formulas have two types of variables, named variables from a type `α` and positional variables indexed by de Bruijn indices.

Our definition of formulas only uses positional (indexed) variables, which keeps the basic definitions minimal.
Free named variables are a layer built on top of this. A formula in named variables, with names from `α : S → Type*`, is a positional formula with variables of shape `ctx : Arity S`, together with an assignment `names : ∀ s, ctx.Idx s → α s`; see `BoundedFormula L α σ` in [Named.lean](MultisortedLogic/Named.lean).
Parameters are handled separately: a formula with parameters from `α` is an `L[[α]]`-formula, where `L[[α]]` denotes the expansion of `L` by constant symbols for the objects of `α`; see [Parameters.lean](MultisortedLogic/Parameters.lean).

````lean4
/-- `L.Formula σ` is the type of formulas in context `σ`: their variables are the positions of `σ`, and quantifiers extend the context on the right. -/
inductive Formula : Arity S → Type (max z u v)
  /-- Falsum. -/
  | falsum {σ : Arity S} : Formula σ
  /-- Equality of two tuples of terms of the same shape. -/
  | equal {σ τ : Arity S} (t₁ t₂ : L.Term σ τ) : Formula σ
  /-- A relation symbol applied to a tuple of terms. -/
  | rel {σ τ : Arity S} (R : L.Relations τ) (ts : L.Term σ τ) : Formula σ
  /-- Implication. -/
  | imp {σ : Arity S} (φ ψ : Formula σ) : Formula σ
  /-- Universal quantification over a block of variables of shape `τ`. -/
  | all {σ : Arity S} (τ : Arity S) (φ : Formula (σ ⨯ τ)) : Formula σ
````

## References

The development of quantifier elimination for algebraically closed valued fields (in `Algebra/ACVF/` and `AlgebraicBackground/RV.lean`, with the main theorem and a guide to the proof in [`Algebra/ACVF/QE.lean`](MultisortedLogic/Algebra/ACVF/QE.lean)) follows Silvain Rideau-Kikuchi's lecture notes:

- [S. Rideau-Kikuchi, *Model theory of valued fields*](https://www.math.ens.psl.eu/~rideau/teaching/val/vf.pdf)

Many files were originally based on files of [Mathlib's model theory library](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html), by Aaron Anderson, Jesse Michael Han, Floris van Doorn, Gabin Kolly and Chris Hughes. Each of these files names its Mathlib counterpart and that file's authors in a "References" section of its module documentation. Among them, `Basic.lean`, `LanguageMap.lean`, `Syntax.lean` and `Semantics.lean` are based on the Mathlib files of the same name by Aaron Anderson, Jesse Michael Han and Floris van Doorn, first versions of which appeared in the Flypitch project:

- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*](https://flypitch.github.io/papers/)
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*](https://flypitch.github.io/papers/)

We have also benefited from discussions on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Many-sorted.20model.20theory) and personal discussions with Aaron Anderson and Silvain Rideau-Kikuchi.

## AI disclosure statement

A first version of this repository was made by humans, with limited AI assistance.
The quantifier elimination results were auto-formalized on top of our quantifier-elimination criteria to stress-test the framework.

The current version is the result of an AI-powered refactor of the existing framework. Notably, it eliminated the need for various custom structures for dependent families.

The main models used in these processes were Claude Opus (4.8-5.5) and Claude Fable 5.
