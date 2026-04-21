# About

The first goal of this repository is to formalize a framework for many-sorted logic in Lean4.
We aim to extend the current one-sorted definitions and theorems currently in [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html), with the goal of developing a stable base for formalizing more advanced results, in particular around the model theory of valued fields.

## Feedback welcome!

We very much appreciate any feedback and comments, especially on the fundamental definitions `MSLanguage`, `MSStructure`, `Term`, `BoundedFormula`.
Feel free to add any comments to this [Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Many-sorted.20model.20theory) thread, which already includes some great suggestions. The goal is to find definitions which are convenient both for foundational development as well as actually doing model theory.

You can also contact us directly via our institutional emails: [Aaron Crighton](mailto:acrighto@fields.utoronto.ca), [John Nicholson](mailto:nichoj6@mcmaster.ca), [Mathias Stout](mailto:stoutm1@mcmaster.ca).


## Contributing

As our end goal is to make formalization more accessible to the wider model theory community, we welcome any interested contributors.
However, in that spirit, all definitions are still very much susceptible to change.
Fixes, small upgrades and partial reworks are all welcome, but there is currently no blueprint towards building more advanced results, although there are some concrete plans for the near future: see `CONTRIBUTING.md`.

## Repository structure

**Note:** As of Apr. 21st 2026, the old `MultisortedLogic` approach as described below has been removed from this repo. The more modern approach, which was originally suggested by Adam Topaz, is the approach which can be found under the MulitsortedLogic folder.

This repository consists of two main folders, `MultisortedLogic` and `ProdExpr`.
The folder `MultisortedLogic` contains a more naive first approach on which the `ProdExpr` folder iterates, based on a suggestion by Adam Topaz.

The main differences between both approaches are explained below.

### MultisortedLogic

This approach can be summarized as taking the existing Mathlib definitions and generalizing them to a dependent setting.

A many sorted language `L` over a type `Sorts` consists of a collection of function and relation symbols for each `List Sorts`. Here the type `Sorts` represents the different model-theoretic sorts of the language, a notion entirely orthogonal to Lean's `Sort u`.

Terms and formulas are built up as usual by a set of inductive rules. In particular, a term in a family of variables (names) `\alpha : Sorts \to Type*` and is formalized as follows

```lean4
inductive Term (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') : Sorts → Type max z u' u
    -- A term landing in `t : Sort` is either a variable symbol
 | var t : (α t) → L.Term α t
    -- Or the application of a function symbol to a family of existing terms,
    -- if that family has the correct output sorts
 | func (σ : List (Sorts)) t : ∀ (_ : L.Functions σ t),
    ((i : Fin σ.length) → L.Term α (σ.get i)) → L.Term α t
```

This corresponds rather directly to the informal construction. Moreover, type correctness corresponds to syntactic well-formedness: an object of type `Term` is always a well-formed term in the sense of first-order logic.
However, by passing a dependent type `((i : Fin σ.length) → L.Term α (σ.get i))`, casts over the list of required sorts `σ` quickly start to accumulate and become unwieldy, even when doing basic constructions.


### ProdExpr

The two fundamental differences with the `MultisortedLogic` were suggested by Adam Topaz on Zulip, and are as follows

First, instead of describing the signature of function and relation symbols by lists, we use a type `ProdExpr`, representing a nonassociative "product expression" over a type `S`.

````lean4
inductive ProdExpr (S : Type u) where
  | nil  : ProdExpr S
  | of   : S → ProdExpr S
  | prod : ProdExpr S → ProdExpr S → ProdExpr S
````

A first-order structure over `Sorts : Type*` associates to each such possible expression a product of types.

````lean4
def ProdExpr.Interpret {S : Type u} (X : S → Type v) : ProdExpr S → Type v
  | .nil       => PUnit
  | .of s      => X s
  | .prod a b  => Interpret X a × Interpret X b
````

The nonassociativity of `ProdExpr` reflects that their resulting interpretations are only associative up to isomorphism.

Instead of defining a term with "output" `t : Sort`, we now directly define tuples of terms with "output signature" `σ : ProdExpr Sorts`:

````lean4
inductive Term (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') :
    ProdExpr Sorts → Type max z u' u where
-- Variables of type `s : S` give terms of type `s : S`.
| var (s : Sorts) : α s → L.Term α (.of s)
-- If we have a term of type `s : ProdExpr S` and a function in the language to `t : S`, then
-- applying the function results in a term of type `t : S`.
| func {σ : ProdExpr Sorts} {t : Sorts} (f : L.Functions σ t) (r : L.Term α σ) : L.Term α (.of t)
-- If we have terms of type `s` and `t` then combining them results in a term of type `s.prod t`.
| prod {σ τ : ProdExpr Sorts} : L.Term α σ → L.Term α τ → L.Term α (σ.prod τ)
| nil : L.Term α .nil
````

Thus a tuple of terms `Term L α σ` remembers how it is constructed, due to the nonassociative nature of `σ`, leading to less casts and generally clearer code, at the costs of a host of easy but slightly tedious lemmas around `ProdExpr` in `Signature.lean` and `SortedTuple.lean`.

## References

The files `Basic.Lean`, `LanguageMap.lean`, `Syntax.lean` and `Semantics.lean` in both folders are based on the files with the same name from [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html#FirstOrder.Language.Structure), authored by Aaron Anderson, Jesse Michael Han and Floris van Doorn. First versions of this appeared in the Flypitch project:

- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*](https://flypitch.github.io/papers/)
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*](https://flypitch.github.io/papers/)
