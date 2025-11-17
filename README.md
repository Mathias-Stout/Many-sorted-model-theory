# About

The first goal of this repository is to formalize a framework for many-sorted logic in Lean4.
We aim to extend the current one-sorted definitions and theorems currently in [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html), with the aim of developing a stable base for formalizing more advanced results, with model theory of valued fields in particular.

## Feedback welcome!

We very much appreciate any feedback and comments, especially on the fundamental definitions `MSLanguage`, `MSStructure`, `Term`, `BoundedFormula`, and the current way dependent vectors are used and implemented in `SortedTuple` (more explanation below).
Feel free to add any comments them to this [Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Many-sorted.20model.20theory) thread, which already includes some great suggestions. The goal is to find definitions which are convenient both for foundational development as well as actually doing model theory. 

You can also contact us directly via our institutional emails: [Aaron Crighton](acrighto@fields.utoronto.ca), [John Nicholson](nichoj6@mcmaster.ca), [Mathias Stout](stoutm1@mcmaster.ca).


## Contributing

As our end goal is to make formalization more accessible to the wider model theory community, we welcome any interested contributors. 
However, as noted above, all definitions are still very much susceptible to change. 
Fixes, small upgrades and partial reworks are all welcome, but there is currently no blueprint towards building more advanced results, although there are some concrete plans for the near future: see `CONTRIBUTING.md`.

- Examining more concrete examples (cf. `Examples.lean`).
- Building an API to compare and transfer results about the one-sorted `Language` to `MSLanguage Unit`.
- Introducing the notion of a map between languages on different sorts, and recovering the many-sorted compactness theorem from the one-sorted one by using a suitable map `MSLanguage Sorts -> MSLanguage Unit`.
- Developing relative quantifier elimination tests.


## Repository structure

This repository is structured as follows:

- `Basic.lean`, `LanguageMap.lean`, `Syntax.lean`, `Semantics.lean` contain many-sorted analogues of the one-sorted definitions and theorems in Mathlib. The generalizations of these theorems provides a first basic test for the viability of the fundamental definitions.

- `Fam.lean` contains general lemmas about families `S -> Type*`, where `S` is a fixed base type. Several lemmas on e.g. function decomposition and disjoint sums are given, generalizing their non-dependent counterparts.

- `SortedTuple.lean` contains the definition of a 'sorted tuple', essentially representing a dependent vector. In more detail, given some `σ : List S`, and a dependent type `α : S -> Type*`, `SortedTuple σ α` represents a vector whose i-th entry has type `α σ[i]` (the set `S` will usually be the set of model-theoretic sorts). For more details and further comments, see below.

- `Examples.lean` contains a mix of examples of statements about modules and vector spaces to both test the soundness and usability of the current definitions.

## Implementation notes

Below are descriptions of the current main definitions and their motivation, as well as some challenges related to the chosen formalization. We assume a basic familiarity with (many-sorted) model theory, as can be found in most textbooks on the subject. In particular the word 'sort' is used in the model-theoretic sense, and not in the sense of the type `Sort` in Lean.

### MSLanguage

Mathematically, a many-sorted language on sorts $S$ consists of, for each tuple $(s_1,\ldots, s_n) \in S^n$ and each $s \in S$, a set 
- $\mathcal{F}_{(s_1,\ldots,s_n;s)}$, of *function symbols*,
- $\mathcal{R}_{(s_1,\ldots, s_n)}$, of *relation symbols*.

This notion is formalized as follows
```lean4
structure MSLanguage (Sorts : Type z) where
Functions : List Sorts → Sorts → Type u
Relations : List Sorts → Type v
```

Alternatively, one could consider sets of function and relation symbols for each *multiset* $\{s_1,\ldots,s_n\}$, rather than ordered tuples $(s_1,\ldots,s_n)$. Mathematically, this amounts to making a choice between indexing the sets of functions and relations by the elements of the free *commutative* monoid on $S$, or the free monoid on $S$. The latter is more natural when considering maps between languages that have different numbers of sorts.

The choice for `List S` in the formalization above is motivated by the fact that in lean `FreeMonoid = List`.
The type `(n : ℕ) → Fin n → Sorts` could be a valid alternative.

### MSStructure

Mathematically, a many-sorted structure for some language $\mathcal{L}$ on a set of sorts $S$ consists of the following data:

- A family of sets $(M_s)_{s \in S}$
- For each $n \in \mathbb{N}$, each tuple $(s_1,\ldots,s_n) \in S^n$ and $s \in S$ 
    - functions $f^M \colon M_{s_1} \times \ldots M_{s_n} \to M_s$ for each symbol $f \in \mathcal{F}_{(s_1,\ldots,s_n;s)}$
    - n-ary relations $R^M \subseteq M_{s_1} \times \ldots M_{s_n}$ for each symbol $R \in \mathcal{R}_{(s_1,\ldots,s_n)}$

This is notion is formalized as follows:

```lean4
class MSStructure {Sorts} (L : MSLanguage Sorts) (M: Sorts → Type w) where
funMap : ∀ {σ t}, L.Functions σ t → SortedTuple σ M → M t := by
    exact fun {σ} => fun {t} => isEmptyElim
RelMap : ∀ {σ}, L.Relations σ → SortedTuple σ M → Prop := by
    exact fun {σ} => isEmptyElim
```

The dependent type `SortedTuple [s1,...,sn] M` represents a tuple $(s_1,\ldots,s_n) \in M_{s_1} \times \ldots \times M_{s_n}$. See also the comments on `SortedTuple` below.

### Term

Fix a family of variable symbols $V = (V_s)_{s \in S}$.
A term $t$ in a language $\mathcal{L}$ of type $s$ and variables $V$ is either 

 - a variable symbol $x \in V_s$
 - an application of function symbol $f \in \mathcal{F}_{(s_1,\ldots,s_n;s)}$ to terms $t_1,\ldots,t_n$, respectively of type $s_1, \ldots, s_n$.

This notion is formalized as follows:

```lean4
inductive Term (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') : Sorts → Type max z u' u
 | var t : (α t) → L.Term α t
 | func (σ : List (Sorts)) t : ∀ (_ : L.Functions σ t),
    ((i : Fin σ.length) → L.Term α (σ.get i)) → L.Term α t
```

The type `((i : Fin σ.length) → L.Term α (σ.get i))` is used instead of `SortedTuple σ α`, as Lean does not accept the use of 'nested inductive datatypes' in the latter case.

### BoundedFormula

The type `BoundedFormula` is similar to the one-sorted case and represents a formula 'under construction'. It has two types of variables: free variables indexed by a dependent type `α : Sort → Type* ` and 'bounded variables' indexed by a list of sorts `σ` (which act like modified de Bruijn indices + labels: see also the one-sorted case).
After quantifying away all bounded variables, one obtains a `Formula` .

```lean4
/--Turn a list into a family of types over the base `S`-/
def toFam {S : Type*} (σ : List S) : S → Type := fun s => {n : Fin σ.length // σ.get n = s}

/--Dependent direct sum. -/
notation:30 f " ⊕ₛ " g => fun s => (f s) ⊕ (g s)

variable {Sorts : Type z} (L : MSLanguage.{u, v, z} Sorts)

inductive BoundedFormula (α : Sorts → Type u') : List Sorts → Type (max u v z u')
  | falsum {σ} : BoundedFormula α σ
  | equal {σ t}
    -- note: only terms with the exact same signatures can be set equal to each other
      (t₁ t₂ : L.Term (α ⊕ₛ σ.toFam) t) :
      BoundedFormula α σ
  | rel {σ σ'}
      (R : L.Relations σ')
      (ts : (i : Fin σ'.length) →  (L.Term (α ⊕ₛ σ.toFam) (σ'.get i))) :
      BoundedFormula α σ
  /-- The logical implication of two bounded formulas-/
  | imp {σ}
      (f₁ f₂ : BoundedFormula α σ) :
      BoundedFormula α σ
  /-- Adds a universal quantifier to a bounded formula-/
  | all {σ s}
      (f : BoundedFormula α (σ ++ [s])) :
      BoundedFormula α σ

abbrev Formula (L:MSLanguage.{u,v,z} Sorts) (α : Sorts → Type u') := BoundedFormula L α []
```

Some notes:

- When applying the rule `rel` to create a new `BoundedFormula` by applying a relation symbol to a tuple of terms, this tuple of terms is represented concretely as an object of type `(ts : (i : Fin σ'.length) →  (L.Term (α ⊕ₛ σ.toFam)` rather than `SortedTuple σ' (L.Term (α ⊕ₛ σ.toFam)` to avoid errors related to 'nested inductive datatypes'.

- The universal quantifier quantifies away the last bounded variable, rather than the first. This is to remain morally consistent with the one-sorted code in Mathlib, where bounded variables are represented by `Fin n` and the universal quantifier quantifies away the variable indexed by `(n-1 : Fin n)`.
    - In isolation, it would have been more convenient to replace the constructor `all` by 
    ```lean4
    all {σ s} (f : BoundedFormula α (s :: σ)) : BoundedFormula α σ`
    ``` 

### SortedTuple

SortedTuples represent 'dependent vectors'.
More precisely, given a base type `S : Type*`, a list `σ : List S` and a dependent type `α → Type*`, a `SortedTuple σ α` is a vector of length `σ.length` whose `i`-th entry has type `σ[i]`. 
The primary use of this structure is to be an intermediate point for the various possible formalizations of the concept of a 'dependent vector' (see below).

It is currently implemented as a `List (Sigma α)` whose projection onto the first components is `σ`.

```lean4
universe u v

variable {S : Type u}

@[ext]
structure SortedTuple (σ : List S) (α : S → Type v) where
  toList : List (Sigma α)
  signature_eq : toList.map Sigma.fst = σ
```

More importantly, one has functions to convert between a `SortedTuple σ α` and objects of the following types:

- A list of Sigma types: `List (Sigma α)` (see `toList`, `fromList`)
- A Pi type/dependent map: `(i : Fin σ.length) → α (σ.get i) ` (see `toMap`, `fromMap`)
- A family of maps over a base type: `(s : S) → σ.toFam s → α s` (see definition of `toFam` above, also see `toFMap`, `fromFMap`)

The structure `SortedTuple` has proven useful in converting between these representations in a principled way. 
However, there are still challenges to address:

- Proving that operations defined using one representation act in a specific way on a different representation can be cumbersome (see e.g. the implementation and sorries surrounding `map` and `extend`)
- Unfolding and simplification is not as smooth as for non-dependent vectors: compare the proofs in the `Examples.lean` file to those in Mathlib's ModelTheory\Algebra\Ring\Basic.lean and ModelTheory\Algebra\Field\Basic.lean. Finding the right auxiliary results/metaprogramming/alternative definitions to make most of these proofs immediate is the first main goal, before building more advanced results on possibly unstable foundations. 
- The name 'sorted tuple' is inspired by our specific use case, though 'dependent vectors' might be a better and more general name. We expect that definitions and lemmas related to these objects might also be present in other projects, and we appreciate any pointers.
- It is entirely plausible that all of the definitions mentioned in this readme can be improved. Feel free to add to the discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Many-sorted.20model.20theory). We are interested in comparing these different ideas and especially appreciate any comments that indicate precisely how alternative approaches can fix current issues (without breaking too many other things). 


## References

The files `Basic.Lean`, `LanguageMap.lean`, `Syntax.lean` and `Semantics.lean` are based on the files with the same name from [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html#FirstOrder.Language.Structure), authored by Aaron Anderson, Jesse Michael Han and Floris van Doorn. First versions of this appeared in the Flypitch project:

- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*](https://flypitch.github.io/papers/)
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*](https://flypitch.github.io/papers/)

