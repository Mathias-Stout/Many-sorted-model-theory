import MultisortedLogic.Semantics

namespace MSFirstOrder

universe u v w u' v' z


variable {Sorts : Type z} {L : Language.{u, v, z} Sorts} {L' : Language Sorts}
variable {M : Fam.{w} Sorts} {N : Fam Sorts} {P : Fam Sorts}
variable [i : L.Structure M] [L.Structure N] [L.Structure P]
variable {α : Fam.{u'} Sorts} {β : Sorts → Type v'} {γ : Fam Sorts}
variable {s : Sorts} {t : Sorts}

open Lean Lean.Parser.Tactic

/--
`semantic_blast` aggressively simplifies semantic statements about realization from their
syntactic form to a semantic form about the underlying structure.
-/
syntax "semantic_blast" : tactic

macro_rules
  | `(tactic| semantic_blast) =>
    `(tactic| simp only [
      --Syntactic helpers for quanfication
      MSFirstOrder.Language.BoundedFormula.Quantifiable.mkAll,
      MSFirstOrder.Language.BoundedFormula.Quantifiable.mkEx,
      MSFirstOrder.Signature.SigMap.extend_right,
      --Instances
      MSFirstOrder.Language.BoundedFormula.instSortQuantRoot,
      MSFirstOrder.Language.BoundedFormula.instSortQuant,
      MSFirstOrder.Language.BoundedFormula.instProdQuant,
      --Realization simps for Sentences
      MSFirstOrder.Language.Sentence.Realize,
      MSFirstOrder.Language.Sentence.realize_bot,
      MSFirstOrder.Language.Sentence.realize_top,
      MSFirstOrder.Language.Sentence.realize_inf,
      MSFirstOrder.Language.Sentence.realize_sup,
      MSFirstOrder.Language.Sentence.realize_imp,
      MSFirstOrder.Language.Sentence.realize_iff,
      MSFirstOrder.Language.Sentence.realize_not,
      --Realization simps for Formulas
      MSFirstOrder.Language.Formula.Realize,
      MSFirstOrder.Language.BoundedFormula.Realize,
      MSFirstOrder.Language.BoundedFormula.realize_bot,
      MSFirstOrder.Language.BoundedFormula.realize_top,
      MSFirstOrder.Language.BoundedFormula.realize_inf,
      MSFirstOrder.Language.BoundedFormula.realize_imp,
      MSFirstOrder.Language.BoundedFormula.realize_not,
      MSFirstOrder.Language.BoundedFormula.realize_sup,
      MSFirstOrder.Language.BoundedFormula.realize_iff,
      MSFirstOrder.Language.BoundedFormula.realize_bdEqual,
      --Quantifier simps
      MSFirstOrder.Language.BoundedFormula.realize_all,
      MSFirstOrder.Language.BoundedFormula.realize_ex,
      MSFirstOrder.Language.BoundedFormula.realize_rel,
      MSFirstOrder.Language.BoundedFormula.realize_rel₁,
      MSFirstOrder.Language.BoundedFormula.realize_rel₂,
      --Casting simps
      MSFirstOrder.Language.Term.realize_comap,
      MSFirstOrder.Signature.Interpret.comap,
      --Tuple and index simps
      MSFirstOrder.Signature.Interpret.fromGet,
      MSFirstOrder.Signature.Interpret.get,
      MSFirstOrder.Language.BoundedFormula.instVarIndexBase,
      MSFirstOrder.Language.BoundedFormula.instVarIndexZero,
      MSFirstOrder.Language.BoundedFormula.instVarIndexSucc,
      MSFirstOrder.Language.BoundedFormula.VarIndex.get,
      MSFirstOrder.Signature.Interpret.reduce_nil,
      MSFirstOrder.Signature.nilLeft_symm_apply,
      MSFirstOrder.Signature.get_right_var,
      MSFirstOrder.Language.Constants.term,
      MSFirstOrder.Language.constantMap,
      Sum.elim_inr,
      Sum.elim_inl,
      PUnit.default_eq_unit,
      --Term.realize simps:
      MSFirstOrder.Language.Term.realize_var,
      MSFirstOrder.Signature.SigEquiv.symm,
      MSFirstOrder.Language.Term.realize_functions_apply₂,
      MSFirstOrder.Language.Term.realize_functions_apply₁,
      MSFirstOrder.Language.Term.realize_func,
      MSFirstOrder.Language.Term.realize_prod,
      MSFirstOrder.Language.Term.realize_varterm,
      MSFirstOrder.Language.Term.realize_function_term,
      --Lean logical simplifiers (for double negations, etc)
      imp_false,
      not_forall,
      not_not,
      not_exists,
      forall_eq_or_imp,
      imp_self,
      implies_true,
      exists_prop,
      not_or,
      not_and
    ]; try { simp? ; simp? };
    )

syntax "blast_then_simp" : tactic

macro_rules
  | `(tactic| blast_then_simp) =>
   `(tactic| semantic_blast; try{simp?})


namespace Language.BoundedFormula
open Signature

variable {ξ η : Signature Sorts} {φ ψ : L.BoundedFormula α ξ} {θ : L.BoundedFormula α (ξ ⨯ η)}
variable {v : Fam.FamMap α M} {xs : ξ.Interpret M} {i}

--Push negation through ∃'
theorem realize_not_ex_general {s : Sorts} {φ : L.BoundedFormula α (ξ ⨯ (.of s))} :
    (∼(∃' s φ)).Realize v xs ↔ (∀' s (∼φ)).Realize v xs := by
  semantic_blast

--Push negation through ∀'
theorem realize_not_all_general [L.Structure M] {s : Sorts}
    {φ : L.BoundedFormula α (ξ ⨯ (.of s))} :
    (∼(∀' s φ)).Realize v xs ↔ (∃' s (∼φ)).Realize v xs := by
    semantic_blast

--De Morgan: Push negation through ⊓
theorem realize_not_and_general {φ ψ : L.BoundedFormula α ξ} :
    (∼(φ ⊓ ψ)).Realize v xs ↔ (∼φ ⊔ ∼ψ).Realize v xs := by
  simp only [realize_not, realize_inf, realize_sup, not_and_or]

--De Morgan: Push negation through ⊔
theorem realize_not_or_general {φ ψ : L.BoundedFormula α ξ} :
    (∼(φ ⊔ ψ)).Realize v xs ↔ (∼φ ⊓ ∼ψ).Realize v xs := by
  simp only [realize_not, realize_inf, realize_sup, not_or]

--Double Negation
theorem realize_not_not_general {φ : L.BoundedFormula α ξ} :
    (∼(∼φ)).Realize v xs ↔ φ.Realize v xs := by
  simp only [realize_not, Classical.not_not]

end BoundedFormula
end Language

open Language.BoundedFormula
syntax "quant_blast" : tactic

macro_rules
  | `(tactic| quant_blast) =>
    `(tactic| simp only [
      --Syntactic helpers for quanfication
      MSFirstOrder.Language.BoundedFormula.instSortQuantRoot,
      MSFirstOrder.Language.BoundedFormula.instSortQuant,
      MSFirstOrder.Language.BoundedFormula.instProdQuant,
      MSFirstOrder.Language.BoundedFormula.Quantifiable.mkAll,
      MSFirstOrder.Language.BoundedFormula.Quantifiable.mkEx,
      MSFirstOrder.Language.BoundedFormula.realize_all,
      MSFirstOrder.Language.BoundedFormula.realize_ex,
      MSFirstOrder.Language.BoundedFormula.realize_comap,
      MSFirstOrder.Signature.Interpret.comap,
            --Instances
    ])

syntax "formula_blast" : tactic
macro_rules
  | `(tactic| formula_blast) =>
    `(tactic| simp only [
      --Realization simps for Sentences
      MSFirstOrder.Language.Sentence.realize_bot,
      MSFirstOrder.Language.Sentence.realize_top,
      MSFirstOrder.Language.Sentence.realize_inf,
      MSFirstOrder.Language.Sentence.realize_sup,
      MSFirstOrder.Language.Sentence.realize_imp,
      MSFirstOrder.Language.Sentence.realize_iff,
      MSFirstOrder.Language.Sentence.realize_not,
      MSFirstOrder.Language.Sentence.Realize,
      --Realization simps for Formulas
      --MSFirstOrder.Language.Formula.Realize,
      MSFirstOrder.Language.BoundedFormula.Realize,
      MSFirstOrder.Language.BoundedFormula.realize_bot,
      MSFirstOrder.Language.BoundedFormula.realize_top,
      MSFirstOrder.Language.BoundedFormula.realize_inf,
      MSFirstOrder.Language.BoundedFormula.realize_imp,
      MSFirstOrder.Language.BoundedFormula.realize_not,
      MSFirstOrder.Language.BoundedFormula.realize_sup,
      MSFirstOrder.Language.BoundedFormula.realize_iff,
      MSFirstOrder.Language.BoundedFormula.realize_bdEqual,
      --Quantifier simps
      MSFirstOrder.Language.BoundedFormula.realize_rel,
      MSFirstOrder.Language.BoundedFormula.realize_rel₁,
      MSFirstOrder.Language.BoundedFormula.realize_rel₂,
    ])
syntax "tuple_blast" : tactic
macro_rules
  | `(tactic| tuple_blast) =>
    `(tactic| simp only [
      --Tuple and index simps
      MSFirstOrder.Signature.Interpret.fromGet,
      MSFirstOrder.Signature.Interpret.get,
      MSFirstOrder.Language.BoundedFormula.instVarIndexBase,
      MSFirstOrder.Language.BoundedFormula.instVarIndexZero,
      MSFirstOrder.Language.BoundedFormula.instVarIndexSucc,
      MSFirstOrder.Language.BoundedFormula.VarIndex.get,
      MSFirstOrder.Signature.Interpret.reduce_nil,
      MSFirstOrder.Signature.nilLeft_symm_apply,
      MSFirstOrder.Signature.get_right_var,
      MSFirstOrder.Language.Constants.term,
      MSFirstOrder.Language.constantMap,
      Sum.elim_inr,
      Sum.elim_inl,
      PUnit.default_eq_unit]
    )

syntax "term_blast" : tactic
macro_rules
  | `(tactic| term_blast) =>
    `(tactic| simp only [
      --Term.realize simps:
      MSFirstOrder.Language.Term.realize_var,
      Fam.sumElim,
      MSFirstOrder.Signature.SigEquiv.symm,
      MSFirstOrder.Language.Term.realize_functions_apply₂,
      MSFirstOrder.Language.Term.realize_func,
      MSFirstOrder.Language.Term.realize_prod,
      MSFirstOrder.Language.Term.realize_varterm,
      MSFirstOrder.Language.Term.realize_function_term,
    ])

syntax "logic_blast" : tactic
macro_rules
  | `(tactic| logic_blast) =>
    `(tactic| simp only [
      --Lean logical simplifiers (for double negations, etc)
      imp_false,
      not_forall,
      not_not,
      not_exists,
      forall_eq_or_imp,
      imp_self,
      implies_true,
      exists_prop,
      not_or,
      not_and
    ]
    )

syntax "blast" : tactic

macro_rules
  | `(tactic| blast) =>
    `(tactic| repeat
              quant_blast; repeat formula_blast; repeat term_blast; repeat
              logic_blast; repeat tuple_blast; repeat simp?)


syntax "push_quant" : tactic

macro_rules
  | `(tactic| push_quant) =>
    `(tactic| simp only [
      --Simps to peel away quantifier syntactic sugar
      MSFirstOrder.Language.BoundedFormula.instSortQuantRoot,
      MSFirstOrder.Language.BoundedFormula.instSortQuant,
      MSFirstOrder.Language.BoundedFormula.instProdQuant,
      MSFirstOrder.Language.BoundedFormula.Quantifiable.mkAll,
      MSFirstOrder.Language.BoundedFormula.Quantifiable.mkEx,
      --Quantifier swap simps
      realize_not_ex_general,
      realize_not_all_general,
      --Logic swap simps
      realize_not_and_general,
      realize_not_or_general,
      realize_not_not_general,
      --To allow simping past realize statements
      MSFirstOrder.Language.Sentence.Realize,
      MSFirstOrder.Language.Formula.Realize,
      --Lean logical simplifiers (for double negations, etc)
      imp_false,
      not_forall,
      not_not,
      not_exists,
      imp_self,
      implies_true
    ]; )

end MSFirstOrder
