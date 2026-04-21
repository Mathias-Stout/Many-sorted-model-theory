import ProdExpr.Semantics
namespace MSFirstOrder

universe u v w u' v' z


variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
variable {M : Fam.{w} Sorts} {N : Fam Sorts} {P : Fam Sorts}
variable [i : L.MSStructure M] [L.MSStructure N] [L.MSStructure P]
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
      MSFirstOrder.MSLanguage.BoundedFormula.Quantifiable.mkAll,
      MSFirstOrder.MSLanguage.BoundedFormula.Quantifiable.mkEx,
      MSFirstOrder.Signature.SigMap.extend_right,
      --Instances
      MSFirstOrder.MSLanguage.BoundedFormula.instSortQuantRoot,
      MSFirstOrder.MSLanguage.BoundedFormula.instSortQuant,
      MSFirstOrder.MSLanguage.BoundedFormula.instProdQuant,
      --Realization simps for Sentences
      MSFirstOrder.MSLanguage.Sentence.Realize,
      MSFirstOrder.MSLanguage.Sentence.realize_bot,
      MSFirstOrder.MSLanguage.Sentence.realize_top,
      MSFirstOrder.MSLanguage.Sentence.realize_inf,
      MSFirstOrder.MSLanguage.Sentence.realize_sup,
      MSFirstOrder.MSLanguage.Sentence.realize_imp,
      MSFirstOrder.MSLanguage.Sentence.realize_iff,
      MSFirstOrder.MSLanguage.Sentence.realize_not,
      --Realization simps for Formulas
      MSFirstOrder.MSLanguage.Formula.Realize,
      MSFirstOrder.MSLanguage.BoundedFormula.Realize,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_bot,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_top,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_inf,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_imp,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_not,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_sup,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_iff,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_bdEqual,
      --Quantifier simps
      MSFirstOrder.MSLanguage.BoundedFormula.realize_all,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_ex,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_rel,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_rel₁,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_rel₂,
      --Casting simps
      MSFirstOrder.MSLanguage.Term.realize_comap,
      MSFirstOrder.Signature.Interpret.comap,
      --Tuple and index simps
      MSFirstOrder.Signature.Interpret.fromGet,
      MSFirstOrder.Signature.Interpret.get,
      MSFirstOrder.MSLanguage.BoundedFormula.instVarIndexBase,
      MSFirstOrder.MSLanguage.BoundedFormula.instVarIndexZero,
      MSFirstOrder.MSLanguage.BoundedFormula.instVarIndexSucc,
      MSFirstOrder.MSLanguage.BoundedFormula.VarIndex.get,
      MSFirstOrder.Signature.Interpret.reduce_nil,
      MSFirstOrder.Signature.nilLeft_symm_apply,
      MSFirstOrder.Signature.get_right_var,
      MSFirstOrder.MSLanguage.Constants.term,
      MSFirstOrder.MSLanguage.constantMap,
      Sum.elim_inr,
      Sum.elim_inl,
      PUnit.default_eq_unit,
      --Term.realize simps:
      MSFirstOrder.MSLanguage.Term.realize_var,
      MSFirstOrder.Signature.SigEquiv.symm,
      MSFirstOrder.MSLanguage.Term.realize_functions_apply₂,
      MSFirstOrder.MSLanguage.Term.realize_functions_apply₁,
      MSFirstOrder.MSLanguage.Term.realize_func,
      MSFirstOrder.MSLanguage.Term.realize_prod,
      MSFirstOrder.MSLanguage.Term.realize_varterm,
      MSFirstOrder.MSLanguage.Term.realize_function_term,
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


namespace MSLanguage.BoundedFormula
open Signature

variable {ξ η : Signature Sorts} {φ ψ : L.BoundedFormula α ξ} {θ : L.BoundedFormula α (ξ ⨯ η)}
variable {v : Fam.FamMap α M} {xs : ξ.Interpret M} {i}

--Push negation through ∃'
theorem realize_not_ex_general {s : Sorts} {φ : L.BoundedFormula α (ξ ⨯ (.of s))} :
    (∼(∃' s φ)).Realize v xs ↔ (∀' s (∼φ)).Realize v xs := by
  semantic_blast

--Push negation through ∀'
theorem realize_not_all_general [L.MSStructure M] {s : Sorts}
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
end MSLanguage

open MSLanguage.BoundedFormula
syntax "quant_blast" : tactic

macro_rules
  | `(tactic| quant_blast) =>
    `(tactic| simp only [
      --Syntactic helpers for quanfication
      MSFirstOrder.MSLanguage.BoundedFormula.instSortQuantRoot,
      MSFirstOrder.MSLanguage.BoundedFormula.instSortQuant,
      MSFirstOrder.MSLanguage.BoundedFormula.instProdQuant,
      MSFirstOrder.MSLanguage.BoundedFormula.Quantifiable.mkAll,
      MSFirstOrder.MSLanguage.BoundedFormula.Quantifiable.mkEx,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_all,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_ex,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_comap,
      MSFirstOrder.Signature.Interpret.comap,
            --Instances
    ])

syntax "formula_blast" : tactic
macro_rules
  | `(tactic| formula_blast) =>
    `(tactic| simp only [
      --Realization simps for Sentences
      MSFirstOrder.MSLanguage.Sentence.realize_bot,
      MSFirstOrder.MSLanguage.Sentence.realize_top,
      MSFirstOrder.MSLanguage.Sentence.realize_inf,
      MSFirstOrder.MSLanguage.Sentence.realize_sup,
      MSFirstOrder.MSLanguage.Sentence.realize_imp,
      MSFirstOrder.MSLanguage.Sentence.realize_iff,
      MSFirstOrder.MSLanguage.Sentence.realize_not,
      MSFirstOrder.MSLanguage.Sentence.Realize,
      --Realization simps for Formulas
      --MSFirstOrder.MSLanguage.Formula.Realize,
      MSFirstOrder.MSLanguage.BoundedFormula.Realize,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_bot,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_top,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_inf,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_imp,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_not,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_sup,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_iff,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_bdEqual,
      --Quantifier simps
      MSFirstOrder.MSLanguage.BoundedFormula.realize_rel,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_rel₁,
      MSFirstOrder.MSLanguage.BoundedFormula.realize_rel₂,
    ])
syntax "tuple_blast" : tactic
macro_rules
  | `(tactic| tuple_blast) =>
    `(tactic| simp only [
      --Tuple and index simps
      MSFirstOrder.Signature.Interpret.fromGet,
      MSFirstOrder.Signature.Interpret.get,
      MSFirstOrder.MSLanguage.BoundedFormula.instVarIndexBase,
      MSFirstOrder.MSLanguage.BoundedFormula.instVarIndexZero,
      MSFirstOrder.MSLanguage.BoundedFormula.instVarIndexSucc,
      MSFirstOrder.MSLanguage.BoundedFormula.VarIndex.get,
      MSFirstOrder.Signature.Interpret.reduce_nil,
      MSFirstOrder.Signature.nilLeft_symm_apply,
      MSFirstOrder.Signature.get_right_var,
      MSFirstOrder.MSLanguage.Constants.term,
      MSFirstOrder.MSLanguage.constantMap,
      Sum.elim_inr,
      Sum.elim_inl,
      PUnit.default_eq_unit]
    )

syntax "term_blast" : tactic
macro_rules
  | `(tactic| term_blast) =>
    `(tactic| simp only [
      --Term.realize simps:
      MSFirstOrder.MSLanguage.Term.realize_var,
      Fam.sumElim,
      MSFirstOrder.Signature.SigEquiv.symm,
      MSFirstOrder.MSLanguage.Term.realize_functions_apply₂,
      MSFirstOrder.MSLanguage.Term.realize_func,
      MSFirstOrder.MSLanguage.Term.realize_prod,
      MSFirstOrder.MSLanguage.Term.realize_varterm,
      MSFirstOrder.MSLanguage.Term.realize_function_term,
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
    `(tactic| repeat quant_blast; repeat formula_blast; repeat term_blast; repeat logic_blast; repeat tuple_blast; repeat simp?)


syntax "push_quant" : tactic

macro_rules
  | `(tactic| push_quant) =>
    `(tactic| simp only [
      --Simps to peel away quantifier syntactic sugar
      MSFirstOrder.MSLanguage.BoundedFormula.instSortQuantRoot,
      MSFirstOrder.MSLanguage.BoundedFormula.instSortQuant,
      MSFirstOrder.MSLanguage.BoundedFormula.instProdQuant,
      MSFirstOrder.MSLanguage.BoundedFormula.Quantifiable.mkAll,
      MSFirstOrder.MSLanguage.BoundedFormula.Quantifiable.mkEx,
      --Quantifier swap simps
      realize_not_ex_general,
      realize_not_all_general,
      --Logic swap simps
      realize_not_and_general,
      realize_not_or_general,
      realize_not_not_general,
      --To allow simping past realize statements
      MSFirstOrder.MSLanguage.Sentence.Realize,
      MSFirstOrder.MSLanguage.Formula.Realize,
      --Lean logical simplifiers (for double negations, etc)
      imp_false,
      not_forall,
      not_not,
      not_exists,
      imp_self,
      implies_true
    ]; )

end MSFirstOrder
