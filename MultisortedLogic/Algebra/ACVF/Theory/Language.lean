/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Algebra.Basic
public import MultisortedLogic.LanguageMap

/-!
# The three-sorted leading-term language `L_RV`

This file sets up the three-sorted language in which algebraically closed valued fields admit
*full* quantifier elimination. The development of `ACVF` in this library follows Silvain
Rideau-Kikuchi's lecture notes *Model theory of valued fields*, §2.1 (see the references below).
The language `L_RV` has

1. a sort `K` with the ring language `{0, 1, +, -, *}`,
2. a sort `RV` with the ring language `{0, 1, +, -, *}` and an inverse `⁻¹`,
3. a sort `Γ` with the ordered abelian group language `{0, +, -, ≤}` expanded by `∞`,
4. a map `val : RV → Γ`,
5. a map `rv : K → RV`.

A valued field `(K, v)` becomes an `L_RV`-structure by interpreting `K` as the field, `RV` as
the leading-term structure `K^× / (1 + 𝔪) ∪ {0}` and `Γ` as the value group with `∞`. On `RV`
the multiplication is the quotient multiplication, `0 = rv 0`, and the addition is the addition
of the residue field `k = v⁻¹(0) ∪ {0}` extended by `0`; the negation descends from `K`.

## Main definitions

* `Language.RVSort` : the three sorts.
* `Language.RVFunc`, `Language.RVRel` : the function and relation symbols.
* `Language.rvLang` : the language `L_RV` itself.
* `Language.rvT`, `Language.valT` : the two maps at the level of terms.
* `Language.invT` : the inverse of the `RV` sort at the level of terms.
* `Language.instRingLKWithConstants` : the ring language of `K` in `rvLang[[α]]`, for formulas
  with parameters.

## The inverse on `RV`

The `RV` sort is a group with zero, and the language has to say so. Without an inverse the
*full* leading-term addition `⊕` — the leading term of a sum — is definable only with a
quantifier ("scale into the residue fiber"), and `ACVFTheory` then fails to eliminate
quantifiers. With the inverse, `⊕` is quantifier-free.

## References

* Silvain Rideau-Kikuchi, *Model theory of valued fields*, lecture notes, version of
  September 17, 2024. <https://www.math.ens.psl.eu/~rideau/teaching/val/vf.pdf>

Numbered references in this library are to that version. The proof of its Proposition 2.1.10,
the ACVF embedding lemma, proceeds in steps headed by what they establish, such as
`K(C) = K(M)`; those steps are cited by their headings.
-/

@[expose] public section

namespace ManySorted.Language

open Arity

universe u

/-- The three sorts of the leading-term language: the valued field, the leading-term structure
and the value group with `∞`. -/
inductive RVSort
  | K
  | RV
  | Γ
  deriving DecidableEq

open RVSort

/-- The function symbols of `L_RV`: the ring language on `K` and on `RV`, the ordered abelian
group language with `∞` on `Γ`, and the two maps `rv : K → RV` and `val : RV → Γ`. -/
inductive RVFunc : Arity RVSort → RVSort → Type
  | zeroK : RVFunc ⦃⦄ K
  | oneK : RVFunc ⦃⦄ K
  | negK : RVFunc ⦃K⦄ K
  | addK : RVFunc (⦃K⦄ ⨯ ⦃K⦄) K
  | mulK : RVFunc (⦃K⦄ ⨯ ⦃K⦄) K
  | zeroRV : RVFunc ⦃⦄ RV
  | oneRV : RVFunc ⦃⦄ RV
  | negRV : RVFunc ⦃RV⦄ RV
  | addRV : RVFunc (⦃RV⦄ ⨯ ⦃RV⦄) RV
  | mulRV : RVFunc (⦃RV⦄ ⨯ ⦃RV⦄) RV
  | invRV : RVFunc ⦃RV⦄ RV
  | zeroΓ : RVFunc ⦃⦄ Γ
  | negΓ : RVFunc ⦃Γ⦄ Γ
  | addΓ : RVFunc (⦃Γ⦄ ⨯ ⦃Γ⦄) Γ
  | inftyΓ : RVFunc ⦃⦄ Γ
  | rv : RVFunc ⦃K⦄ RV
  | val : RVFunc ⦃RV⦄ Γ
  deriving DecidableEq

/-- The only relation symbol of `L_RV` is the order on `Γ`. -/
inductive RVRel : Arity RVSort → Type
  | leΓ : RVRel (⦃Γ⦄ ⨯ ⦃Γ⦄)

/-- The three-sorted leading-term language `L_RV`. -/
def rvLang : Language.{0, 0} RVSort where
  Functions := RVFunc
  Relations := RVRel

instance instRingLK : RingL rvLang K where
  addFunc := .addK
  mulFunc := .mulK
  negFunc := .negK
  zeroConst := .zeroK
  oneConst := .oneK

instance instRingLRV : RingL rvLang RV where
  addFunc := .addRV
  mulFunc := .mulRV
  negFunc := .negRV
  zeroConst := .zeroRV
  oneConst := .oneRV

instance instEOAGroupLΓ : EOAGroupL rvLang Γ where
  addFunc := .addΓ
  negFunc := .negΓ
  zeroConst := .zeroΓ
  orderF := .rel (L := rvLang) RVRel.leΓ (.prod (.var (.left .var)) (.var (.right .var)))
  inftyConst := .inftyΓ

/-- The ring language of the field sort, in `rvLang[[α]]`: formulas with parameters use the
symbols of `rvLang` through `Sum.inl`. -/
instance instRingLKWithConstants {α : RVSort → Type*} : RingL rvLang[[α]] K where
  addFunc := Sum.inl AddL.addFunc
  mulFunc := Sum.inl MulL.mulFunc
  negFunc := Sum.inl NegL.negFunc
  zeroConst := Sum.inl ZeroL.zeroConst
  oneConst := Sum.inl OneL.oneConst

/-- The leading-term map `rv : K → RV`, at the level of terms. -/
abbrev rvT {σ : Arity RVSort} (t : rvLang.Term σ ⦃K⦄) : rvLang.Term σ ⦃RV⦄ :=
  .func (L := rvLang) RVFunc.rv t

/-- The inverse of the leading-term sort, at the level of terms. -/
abbrev invT {σ : Arity RVSort} (t : rvLang.Term σ ⦃RV⦄) : rvLang.Term σ ⦃RV⦄ :=
  .func (L := rvLang) RVFunc.invRV t

/-- The valuation `val : RV → Γ`, at the level of terms. -/
abbrev valT {σ : Arity RVSort} (t : rvLang.Term σ ⦃RV⦄) : rvLang.Term σ ⦃Γ⦄ :=
  .func (L := rvLang) RVFunc.val t

end ManySorted.Language
