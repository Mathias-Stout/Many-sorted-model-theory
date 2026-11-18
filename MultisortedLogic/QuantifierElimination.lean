/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Complexity
public import MultisortedLogic.Semantics

/-!
# Quantifier elimination relative to a set of sorts

A theory `T` has quantifier elimination relative to a set of sorts `R` when every formula is
equivalent modulo `T` to one that quantifies only over blocks of sorts in `R`.

## Main declarations

`Arity.FromSorts` and `Formula.IsQFRelTo` are in `Complexity.lean`, and the transfer of such
formulas along embeddings is in `Semantics.lean`.

* `Theory.SemanticallyEquivalent`, with its congruence lemmas.
* `Theory.HasQERelTo T R`, and `Theory.hasQERelTo_of_sortElim`: eliminating one existential over
  one sort outside `R` suffices.
* `Theory.HasQERelTo.realize_embedding`: under quantifier elimination relative to `R`, an
  embedding of models of `T` that is onto on the sorts of `R` is elementary.

The semantic criteria for `HasQERelTo` are in `Separation.lean` (tuple extension) and
`EmbeddingTest.lean` (extension of partial maps).
-/

@[expose] public section

universe u v z

namespace ManySorted

namespace Language

open Arity Structure

variable {S : Type z} {L : Language.{u, v} S} {R R' : Set S}

namespace Theory

variable {T : L.Theory} {σ τ : Arity S}

/-- `φ` and `ψ` are equivalent in every model of `T`. -/
def SemanticallyEquivalent (T : L.Theory) (φ ψ : L.Formula σ) : Prop := T ⊨ᵇ (φ ⇔ ψ)

namespace SemanticallyEquivalent

theorem iff_forall {φ ψ : L.Formula σ} :
    T.SemanticallyEquivalent φ ψ ↔ ∀ (N : S → Type (max u v z)) [L.Structure N]
      [∀ s, Nonempty (N s)] [N ⊨ T] (xs : N [^] σ), (φ.Realize xs ↔ ψ.Realize xs) := by
  simp only [SemanticallyEquivalent, ModelsFormula, Formula.realize_iff]

theorem realize_iff {φ ψ : L.Formula σ} (h : T.SemanticallyEquivalent φ ψ)
    {N : S → Type (max u v z)} [L.Structure N] [∀ s, Nonempty (N s)] [N ⊨ T] (xs : N [^] σ) :
    φ.Realize xs ↔ ψ.Realize xs :=
  iff_forall.1 h N xs

/-- An equivalence that holds in every structure holds modulo any theory. -/
theorem of_forall {φ ψ : L.Formula σ}
    (h : ∀ (N : S → Type (max u v z)) [L.Structure N] (xs : N [^] σ),
      (φ.Realize xs ↔ ψ.Realize xs)) :
    T.SemanticallyEquivalent φ ψ :=
  iff_forall.2 fun N _ _ _ xs => h N xs

@[refl] theorem refl (φ : L.Formula σ) : T.SemanticallyEquivalent φ φ :=
  of_forall fun _ _ _ => Iff.rfl

@[symm] theorem symm {φ ψ : L.Formula σ} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent ψ φ :=
  iff_forall.2 fun _ _ _ _ xs => (h.realize_iff xs).symm

@[trans] theorem trans {φ ψ χ : L.Formula σ} (h₁ : T.SemanticallyEquivalent φ ψ)
    (h₂ : T.SemanticallyEquivalent ψ χ) : T.SemanticallyEquivalent φ χ :=
  iff_forall.2 fun _ _ _ _ xs => (h₁.realize_iff xs).trans (h₂.realize_iff xs)

theorem imp {φ₁ φ₂ ψ₁ ψ₂ : L.Formula σ} (h₁ : T.SemanticallyEquivalent φ₁ ψ₁)
    (h₂ : T.SemanticallyEquivalent φ₂ ψ₂) :
    T.SemanticallyEquivalent (φ₁.imp φ₂) (ψ₁.imp ψ₂) :=
  iff_forall.2 fun _ _ _ _ xs => by
    simp only [Formula.realize_imp, h₁.realize_iff xs, h₂.realize_iff xs]

theorem not {φ ψ : L.Formula σ} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent φ.not ψ.not :=
  h.imp (refl _)

theorem all {φ ψ : L.Formula (σ ⨯ τ)} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent (Formula.all τ φ) (Formula.all τ ψ) :=
  iff_forall.2 fun _ _ _ _ xs => by
    simp only [Formula.realize_all, h.realize_iff]

theorem ex {φ ψ : L.Formula (σ ⨯ τ)} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent (φ.ex τ) (ψ.ex τ) :=
  h.not.all.not

theorem all_iff_not_ex_not (φ : L.Formula (σ ⨯ τ)) :
    T.SemanticallyEquivalent (Formula.all τ φ) (φ.not.ex τ).not :=
  of_forall fun _ _ _ => by simp

/-- An existential over the empty block does nothing. -/
theorem ex_nil (φ : L.Formula (σ ⨯ ⦃⦄)) :
    T.SemanticallyEquivalent (φ.ex ⦃⦄) (φ.relabel Idx.nilRight) :=
  of_forall fun _ _ _ => by simp [Unique.exists_iff]

/-- An existential over a product block is two nested existentials. -/
theorem ex_prod {τ₁ τ₂ : Arity S} (φ : L.Formula (σ ⨯ (τ₁ ⨯ τ₂))) :
    T.SemanticallyEquivalent (φ.ex (τ₁ ⨯ τ₂)) (((φ.relabel Idx.assoc).ex τ₂).ex τ₁) :=
  of_forall fun _ _ _ => by simp [Prod.exists]

end SemanticallyEquivalent

/-- `T` has quantifier elimination relative to `R`: every formula is `T`-equivalent to one that is
quantifier-free relative to `R`. -/
def HasQERelTo (T : L.Theory) (R : Set S) : Prop :=
  ∀ (σ : Arity S) (φ : L.Formula σ), ∃ ψ : L.Formula σ, ψ.IsQFRelTo R ∧ T.SemanticallyEquivalent φ ψ

theorem HasQERelTo.mono (h : T.HasQERelTo R) (hR : R ⊆ R') : T.HasQERelTo R' := fun σ φ =>
  let ⟨ψ, hψ, e⟩ := h σ φ
  ⟨ψ, hψ.mono hR, e⟩

/-- A single existential quantifier over a sort outside `R` can be eliminated in favour of
quantifiers over `R`. -/
def SortElim (T : L.Theory) (R : Set S) : Prop :=
  ∀ s ∉ R, ∀ (σ : Arity S) (φ : L.Formula (σ ⨯ ⦃s⦄)), φ.IsQFRelTo R →
    ∃ ψ : L.Formula σ, ψ.IsQFRelTo R ∧ T.SemanticallyEquivalent (φ.ex ⦃s⦄) ψ

/-- To eliminate every existential quantifier in favour of quantifiers over `R`, it suffices to
eliminate a single outer existential quantifier over a sort outside `R`. -/
theorem SortElim.ex_block (h : T.SortElim R) :
    ∀ (τ σ : Arity S) (φ : L.Formula (σ ⨯ τ)), φ.IsQFRelTo R →
      ∃ ψ : L.Formula σ, ψ.IsQFRelTo R ∧ T.SemanticallyEquivalent (φ.ex τ) ψ
  | .nil, _, φ, hφ => ⟨_, hφ.relabel _, .ex_nil φ⟩
  | .of s, σ, φ, hφ => by
    by_cases hs : s ∈ R
    · exact ⟨φ.ex ⦃s⦄, hφ.ex (.of hs), .refl _⟩
    · exact h s hs σ φ hφ
  | .prod τ₁ τ₂, σ, φ, hφ => by
    obtain ⟨χ, hχ, e₂⟩ := h.ex_block τ₂ (σ ⨯ τ₁) (φ.relabel Idx.assoc) (hφ.relabel _)
    obtain ⟨ζ, hζ, e₁⟩ := h.ex_block τ₁ σ χ hχ
    exact ⟨ζ, hζ, (SemanticallyEquivalent.ex_prod φ).trans (e₂.ex.trans e₁)⟩

/-- **One-sort QE criterion.** If an existential over a single sort outside `R`, in front of a
formula quantifier-free relative to `R`, can always be eliminated, then `T` has quantifier
elimination relative to `R`. -/
theorem hasQERelTo_of_sortElim (h : T.SortElim R) : T.HasQERelTo R := by
  intro σ φ
  induction φ with
  | falsum => exact ⟨_, .falsum, .refl _⟩
  | equal t₁ t₂ => exact ⟨_, .of_isAtomic (.equal t₁ t₂), .refl _⟩
  | rel r ts => exact ⟨_, .of_isAtomic (.rel r ts), .refl _⟩
  | imp φ ψ ih₁ ih₂ =>
    obtain ⟨φ', hφ', e₁⟩ := ih₁
    obtain ⟨ψ', hψ', e₂⟩ := ih₂
    exact ⟨_, .imp hφ' hψ', e₁.imp e₂⟩
  | all τ φ ih =>
    obtain ⟨χ, hχ, e⟩ := ih
    obtain ⟨ζ, hζ, e'⟩ := h.ex_block τ _ χ.not hχ.not
    exact ⟨ζ.not, hζ.not, e.all.trans ((SemanticallyEquivalent.all_iff_not_ex_not χ).trans e'.not)⟩

end Theory

/-! ### Semantic consequences -/

/-- Under quantifier elimination relative to `R`, an embedding of models of `T` that is onto on
the sorts of `R` is elementary. -/
theorem Theory.HasQERelTo.realize_embedding {T : L.Theory} (hQE : T.HasQERelTo R)
    {M N : S → Type (max u v z)} [L.Structure M] [L.Structure N] [∀ s, Nonempty (M s)]
    [∀ s, Nonempty (N s)] [M ⊨ T] [N ⊨ T]
    (g : M ↪[L] N) (hsurj : ∀ s ∈ R, Function.Surjective (g s)) {σ : Arity S}
    (φ : L.Formula σ) (xs : M [^] σ) : φ.Realize (xs.map g) ↔ φ.Realize xs := by
  obtain ⟨ψ, hψ, e⟩ := hQE σ φ
  rw [e.realize_iff, e.realize_iff]
  exact StrongHomClass.realize_of_isQFRelTo g g.injective hsurj hψ xs

end Language

end ManySorted
