/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Crighton, Mathias Stout
-/
module

public import MultisortedLogic.LanguageMap
public import Mathlib.Data.W.Cardinal
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Encodings and cardinality bounds

Arities, tuples, terms and formulas are finite trees, and this file encodes each of them
injectively as a tree of `Arity C` for a type of labels `C`. A single bound then counts them all:
`#(Arity C) ≤ max ℵ₀ #C`, through Mathlib's bound on W-types.

## Main definitions

* `Language.Symbols`, `Language.card`: the symbols of a language and their number, with
  `Language.card_sum` and `Language.card_withConstants`.
* `Arity.Interpret.encode`: a tuple as a tree labelled by its entries.
* `Language.Term.encode`, `Language.Formula.encode`: terms and formulas as trees labelled by sorts,
  symbols and a few tags.

## Main results

* `Arity.card_le`: `#(Arity C) ≤ max ℵ₀ #C`.
* `Arity.Interpret.encode_injective`, `Language.Term.encode_injective`,
  `Language.Formula.encode_injective`: the encodings are injective.
* `Language.Formula.card_sigma_le`: `#(Σ σ, L.Formula σ) ≤ max ℵ₀ (#S + L.card)`, with lifts.

## Implementation notes

The trees are encoded directly, and injectivity is proved by induction, so no decoder is
needed.

## References

This file was originally based on `Mathlib/ModelTheory/Encoding.lean`, by Aaron Anderson.
-/

@[expose] public section

universe u v w z u' v' u''

namespace ManySorted

open Cardinal

/-! ### Trees -/

namespace Arity

variable {S : Type z} {C : Type*}

/-- The branching type of the W-type that `Arity C` embeds into: the leaves `nil` (`none`) and
`of c` (`some c`) have no children, the node `prod` has two. -/
abbrev WBranch (C : Type*) : Option C ⊕ Unit → Type := Sum.elim (fun _ => Empty) fun _ => Bool

instance (a : Option C ⊕ Unit) : Finite (WBranch C a) := by
  rcases a with _ | _ <;> dsimp [WBranch] <;> infer_instance

/-- `Arity C` as a W-type. -/
def toWType : Arity C → WType (WBranch C)
  | nil => ⟨.inl none, Empty.elim⟩
  | of c => ⟨.inl (some c), Empty.elim⟩
  | prod σ τ => ⟨.inr (), fun b => cond b (toWType σ) (toWType τ)⟩

theorem toWType_injective : Function.Injective (toWType (C := C)) := by
  intro σ τ h
  induction σ generalizing τ with
  | nil => cases τ <;> injection h with h <;> first | rfl | simp at h
  | of c => cases τ <;> injection h with h <;> simp_all
  | prod σ₁ σ₂ ih₁ ih₂ =>
    cases τ with
    | prod τ₁ τ₂ =>
      injection h with _ h
      rw [ih₁ (congrFun h true), ih₂ (congrFun h false)]
    | _ => injection h with h; simp at h

/-- **The number of trees**: there are at most `max ℵ₀ #C` trees labelled by `C`. -/
theorem card_le (C : Type u) : #(Arity C) ≤ max ℵ₀ #C := by
  refine (mk_le_of_injective toWType_injective).trans <|
    (WType.cardinalMk_le_max_aleph0_of_finite' (β := WBranch C)).trans ?_
  rw [lift_id', max_comm]
  refine max_le_max le_rfl ?_ |>.trans (max_le (le_max_left _ _) le_rfl)
  rcases finite_or_infinite C with hC | hC
  · exact (mk_le_aleph0 (α := Option C ⊕ Unit)).trans (le_max_left _ _)
  · have : #(Option C ⊕ Unit) = #C + 1 + 1 := by simp [mk_sum, mk_option]
    rw [this, add_one_of_aleph0_le (aleph0_le_mk C), add_one_of_aleph0_le (aleph0_le_mk C)]
    exact le_max_right _ _

/-- Relabel the leaves of a tree. -/
def map {D : Type*} (f : C → D) : Arity C → Arity D
  | nil => nil
  | of c => of (f c)
  | prod σ τ => prod (map f σ) (map f τ)

theorem map_injective {D : Type*} {f : C → D} (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro σ τ h
  induction σ generalizing τ with
  | nil => cases τ <;> first | rfl | simp [map] at h
  | of c =>
    cases τ with
    | of d => simp only [map, of.injEq] at h; rw [hf h]
    | _ => simp [map] at h
  | prod σ₁ σ₂ ih₁ ih₂ =>
    cases τ with
    | prod τ₁ τ₂ => simp only [map, prod.injEq] at h; rw [ih₁ h.1, ih₂ h.2]
    | _ => simp [map] at h

/-! ### Tuples -/

namespace Interpret

variable {A : S → Type w}

/-- A tuple as a tree, each entry labelled by itself together with its sort. -/
def encode : ∀ {σ : Arity S}, A [^] σ → Arity (Σ s, A s)
  | nil, _ => nil
  | of s, x => of ⟨s, x⟩
  | prod _ _, x => prod (encode x.1) (encode x.2)

/-- A tuple, with its shape, is determined by its tree. -/
theorem encode_injective : Function.Injective fun x : Σ σ : Arity S, A [^] σ => encode x.2 := by
  rintro ⟨σ, x⟩ ⟨τ, y⟩ h
  dsimp only at h
  induction σ generalizing τ with
  | nil => cases τ <;> first | rfl | simp [encode] at h
  | of s =>
    cases τ with
    | of t =>
      simp only [encode, of.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      rfl
    | _ => simp [encode] at h
  | prod σ₁ σ₂ ih₁ ih₂ =>
    cases τ with
    | prod τ₁ τ₂ =>
      obtain ⟨x₁, x₂⟩ := x
      obtain ⟨y₁, y₂⟩ := y
      simp only [encode, prod.injEq] at h
      obtain ⟨⟩ := ih₁ x₁ τ₁ y₁ h.1
      obtain ⟨⟩ := ih₂ x₂ τ₂ y₂ h.2
      rfl
    | _ => simp [encode] at h

end Interpret

end Arity

namespace Language

variable {S : Type z} (L : Language.{u, v} S)

/-! ### The symbols of a language -/

/-- The symbols of `L`: its function symbols and its relation symbols, with their arities. -/
abbrev Symbols : Type (max z u v) :=
  (Σ σ : Arity S, Σ t : S, L.Functions σ t) ⊕ (Σ σ : Arity S, L.Relations σ)

/-- The number of symbols of `L`. -/
def card : Cardinal.{max z u v} :=
  #L.Symbols

/-! ### The number of symbols of sums and of constants -/

section Sum

variable {L} {L' : Language.{u', v'} S}

/-- The symbols of a sum of languages are those of the summands. -/
def sumSymbolsEquiv : (L.sum L').Symbols ≃ L.Symbols ⊕ L'.Symbols where
  toFun
    | .inl ⟨σ, t, .inl f⟩ => .inl (.inl ⟨σ, t, f⟩)
    | .inl ⟨σ, t, .inr f⟩ => .inr (.inl ⟨σ, t, f⟩)
    | .inr ⟨σ, .inl R⟩ => .inl (.inr ⟨σ, R⟩)
    | .inr ⟨σ, .inr R⟩ => .inr (.inr ⟨σ, R⟩)
  invFun
    | .inl (.inl ⟨σ, t, f⟩) => .inl ⟨σ, t, .inl f⟩
    | .inr (.inl ⟨σ, t, f⟩) => .inl ⟨σ, t, .inr f⟩
    | .inl (.inr ⟨σ, R⟩) => .inr ⟨σ, .inl R⟩
    | .inr (.inr ⟨σ, R⟩) => .inr ⟨σ, .inr R⟩
  left_inv := by rintro (⟨σ, t, f | f⟩ | ⟨σ, R | R⟩) <;> rfl
  right_inv := by rintro ((⟨σ, t, f⟩ | ⟨σ, R⟩) | (⟨σ, t, f⟩ | ⟨σ, R⟩)) <;> rfl

theorem card_sum : (L.sum L').card = lift.{max u' v'} L.card + lift.{max u v} L'.card := by
  rw [card, mk_congr sumSymbolsEquiv, mk_sum, card, card]
  simp

end Sum

/-- The symbols of `constantsOn α` are the names in `α`. -/
def constantsOnSymbolsEquiv (α : S → Type u'') : (constantsOn α).Symbols ≃ Σ s, α s where
  toFun
    | .inl ⟨_, t, c⟩ => ⟨t, ConstantSymbol.name c⟩
    | .inr ⟨_, R⟩ => (R : Empty).elim
  invFun a := .inl ⟨⦃⦄, a.1, (ConstantSymbol.mk a.2 : ConstantSymbol α a.1 ⦃⦄)⟩
  left_inv := by
    rintro (⟨σ, t, ⟨a⟩⟩ | ⟨σ, R⟩)
    · rfl
    · exact (R : Empty).elim
  right_inv _ := rfl

theorem card_constantsOn (α : S → Type u'') : (constantsOn α).card = #(Σ s, α s) :=
  mk_congr (constantsOnSymbolsEquiv α)

theorem card_withConstants (α : S → Type u'') :
    L[[α]].card = lift.{u''} L.card + lift.{max u v} #(Σ s, α s) := by
  rw [card_sum, card_constantsOn]

/-! ### Labels -/

/-- The labels of the trees encoding terms and formulas: sorts, symbols, and seven tags. The sorts
are lifted to the universe of the symbols. -/
abbrev Label : Type (max z u v) := ULift.{max u v} S ⊕ L.Symbols ⊕ Fin 7

variable {L}

/-- The label of a sort. -/
abbrev Label.sort (s : S) : L.Label := .inl ⟨s⟩

/-- The label of a function symbol. -/
abbrev Label.func {σ : Arity S} {t : S} (f : L.Functions σ t) : L.Label :=
  .inr (.inl (.inl ⟨σ, t, f⟩))

/-- The label of a relation symbol. -/
abbrev Label.rel {σ : Arity S} (R : L.Relations σ) : L.Label := .inr (.inl (.inr ⟨σ, R⟩))

/-- A tag. -/
abbrev Label.tag (k : Fin 7) : L.Label := .inr (.inr k)

variable (L) in
theorem card_label_le :
    #L.Label ≤ max ℵ₀ (lift.{max u v} #S + L.card) := by
  have hκ : ℵ₀ ≤ max ℵ₀ (lift.{max u v} #S + L.card) := le_max_left _ _
  have h : #L.Label = lift.{max u v} #S + (L.card + 7) := by
    simp [Label, card, mk_sum, mk_uLift]
  rw [h]
  exact add_le_of_le hκ (le_max_of_le_right (self_le_add_right _ _)) <|
    add_le_of_le hκ (le_max_of_le_right (self_le_add_left _ _)) <| ofNat_lt_aleph0.le.trans hκ

/-! ### Arities and positions as trees -/

namespace Label

/-- An arity as a tree of sort labels. -/
def ofArity : Arity S → Arity L.Label
  | .nil => .nil
  | .of s => .of (Label.sort s)
  | .prod σ τ => .prod (ofArity σ) (ofArity τ)

theorem ofArity_injective : Function.Injective (ofArity (L := L)) := by
  intro σ τ h
  induction σ generalizing τ with
  | nil => cases τ <;> first | rfl | simp [ofArity] at h
  | of s =>
    cases τ with
    | of t => simp only [ofArity, Arity.of.injEq, Sum.inl.injEq, ULift.up.injEq] at h; rw [h]
    | _ => simp [ofArity] at h
  | prod σ₁ σ₂ ih₁ ih₂ =>
    cases τ with
    | prod τ₁ τ₂ =>
      simp only [ofArity, Arity.prod.injEq] at h
      rw [ih₁ h.1, ih₂ h.2]
    | _ => simp [ofArity] at h

/-- A position as a tree: its path, as a word in the tags `4` (here), `5` (left), `6` (right). -/
def ofIdx : ∀ {σ : ManySorted.Arity S} {s : S}, σ.Idx s → ManySorted.Arity L.Label
  | _, _, .var => .of (Label.tag 4)
  | _, _, .left i => .prod (.of (Label.tag 5)) (ofIdx i)
  | _, _, .right i => .prod (.of (Label.tag 6)) (ofIdx i)

theorem ofIdx_injective {σ : ManySorted.Arity S} {s : S} :
    Function.Injective (ofIdx (L := L) (σ := σ) (s := s)) := by
  intro i j h
  induction i with
  | var => cases j; rfl
  | left i ih =>
    cases j with
    | left j => simp only [ofIdx, ManySorted.Arity.prod.injEq, true_and] at h; rw [ih h]
    | right j => simp [ofIdx] at h
  | right i ih =>
    cases j with
    | left j => simp [ofIdx] at h
    | right j => simp only [ofIdx, ManySorted.Arity.prod.injEq, true_and] at h; rw [ih h]

end Label

/-! ### Terms -/

namespace Term

variable {Γ : ManySorted.Arity S}

/-- A tuple of terms as a tree. A variable is `prod (of s) i` and a function symbol applied to
terms is `prod (of f) ts`; a pair of terms is `prod t₁ t₂`, and no term is a leaf `of _`, so these
are told apart. -/
def encode : ∀ {σ : ManySorted.Arity S}, L.Term Γ σ → ManySorted.Arity L.Label
  | _, .var (s := s) i => .prod (.of (Label.sort s)) (Label.ofIdx i)
  | _, .func f ts => .prod (.of (Label.func f)) (encode ts)
  | _, .nil => .nil
  | _, .prod t₁ t₂ => .prod (encode t₁) (encode t₂)

theorem encode_ne_of {σ : ManySorted.Arity S} (t : L.Term Γ σ) (c : L.Label) :
    t.encode ≠ .of c := by
  cases t <;> simp [encode]

theorem eq_of_encode_eq {σ : ManySorted.Arity S} (t : L.Term Γ σ) :
    ∀ {τ : ManySorted.Arity S} (t' : L.Term Γ τ), t.encode = t'.encode → σ = τ ∧ t ≍ t' := by
  induction t with
  | var i =>
    intro τ t' h
    cases t' with
    | var j =>
      simp only [encode, ManySorted.Arity.prod.injEq, ManySorted.Arity.of.injEq,
        Sum.inl.injEq, ULift.up.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases Label.ofIdx_injective h
      exact ⟨rfl, .rfl⟩
    | func f ts => simp [encode] at h
    | nil => simp [encode] at h
    | prod t₁ t₂ =>
      simp only [encode, ManySorted.Arity.prod.injEq] at h
      exact absurd h.1.symm (encode_ne_of t₁ _)
  | func f ts ih =>
    intro τ t' h
    cases t' with
    | var j => simp [encode] at h
    | func f' ts' =>
      simp only [encode, ManySorted.Arity.prod.injEq, ManySorted.Arity.of.injEq, Sum.inr.injEq,
        Sum.inl.injEq, Sigma.mk.injEq] at h
      obtain ⟨⟨rfl, h₁⟩, h₂⟩ := h
      obtain ⟨rfl, h₁⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h₁)
      cases eq_of_heq h₁
      obtain ⟨-, h₂⟩ := ih ts' h₂
      cases eq_of_heq h₂
      exact ⟨rfl, .rfl⟩
    | nil => simp [encode] at h
    | prod t₁ t₂ =>
      simp only [encode, ManySorted.Arity.prod.injEq] at h
      exact absurd h.1.symm (encode_ne_of t₁ _)
  | nil =>
    intro τ t' h
    cases t' <;> first | exact ⟨rfl, .rfl⟩ | simp [encode] at h
  | prod t₁ t₂ ih₁ ih₂ =>
    intro τ t' h
    cases t' with
    | var j =>
      simp only [encode, ManySorted.Arity.prod.injEq] at h
      exact absurd h.1 (encode_ne_of t₁ _)
    | func f' ts' =>
      simp only [encode, ManySorted.Arity.prod.injEq] at h
      exact absurd h.1 (encode_ne_of t₁ _)
    | nil => simp [encode] at h
    | prod t₁' t₂' =>
      simp only [encode, ManySorted.Arity.prod.injEq] at h
      obtain ⟨rfl, h₁⟩ := ih₁ t₁' h.1
      obtain ⟨rfl, h₂⟩ := ih₂ t₂' h.2
      cases eq_of_heq h₁
      cases eq_of_heq h₂
      exact ⟨rfl, .rfl⟩

/-- A tuple of terms, with its shape, is determined by its tree. -/
theorem encode_injective :
    Function.Injective fun t : Σ σ : ManySorted.Arity S, L.Term Γ σ => t.2.encode := by
  rintro ⟨σ, t⟩ ⟨τ, t'⟩ h
  obtain ⟨rfl, h⟩ := eq_of_encode_eq t t' h
  cases eq_of_heq h
  rfl

end Term

/-! ### Formulas -/

namespace Formula

/-- A formula as a tree. Every formula but `⊥` is `prod (of l) _` for a label `l` that says which
constructor it comes from. -/
def encode : ∀ {σ : ManySorted.Arity S}, L.Formula σ → ManySorted.Arity L.Label
  | _, .falsum => .of (Label.tag 0)
  | _, .equal t₁ t₂ => .prod (.of (Label.tag 1)) (.prod t₁.encode t₂.encode)
  | _, .rel R ts => .prod (.of (Label.rel R)) ts.encode
  | _, .imp φ ψ => .prod (.of (Label.tag 2)) (.prod (encode φ) (encode ψ))
  | _, .all τ φ => .prod (.of (Label.tag 3)) (.prod (Label.ofArity τ) (encode φ))

theorem eq_of_encode_eq {σ : ManySorted.Arity S} (φ ψ : L.Formula σ) (h : φ.encode = ψ.encode) :
    φ = ψ := by
  induction φ with
  | falsum => cases ψ <;> first | rfl | simp [encode] at h
  | equal t₁ t₂ =>
    cases ψ with
    | equal t₁' t₂' =>
      simp only [encode, ManySorted.Arity.prod.injEq, true_and] at h
      obtain ⟨rfl, h₁⟩ := Term.eq_of_encode_eq t₁ t₁' h.1
      cases eq_of_heq h₁
      obtain ⟨-, h₂⟩ := Term.eq_of_encode_eq t₂ t₂' h.2
      cases eq_of_heq h₂
      rfl
    | _ => simp [encode] at h
  | rel R ts =>
    cases ψ with
    | rel R' ts' =>
      simp only [encode, ManySorted.Arity.prod.injEq, ManySorted.Arity.of.injEq, Sum.inr.injEq,
        Sum.inl.injEq, Sigma.mk.injEq] at h
      obtain ⟨⟨rfl, h₁⟩, h₂⟩ := h
      cases eq_of_heq h₁
      obtain ⟨-, h₂⟩ := Term.eq_of_encode_eq ts ts' h₂
      cases eq_of_heq h₂
      rfl
    | _ => simp [encode] at h
  | imp φ₁ φ₂ ih₁ ih₂ =>
    cases ψ with
    | imp ψ₁ ψ₂ =>
      simp only [encode, ManySorted.Arity.prod.injEq, true_and] at h
      rw [ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [encode] at h
  | all τ φ ih =>
    cases ψ with
    | all τ' ψ =>
      simp only [encode, ManySorted.Arity.prod.injEq, true_and] at h
      obtain rfl := Label.ofArity_injective h.1
      rw [ih ψ h.2]
    | _ => simp [encode] at h

/-- A formula, with its context, is determined by the tree of its context and its own tree. -/
theorem encode_injective :
    Function.Injective fun φ : Σ σ : ManySorted.Arity S, L.Formula σ =>
      ManySorted.Arity.prod (Label.ofArity φ.1) φ.2.encode := by
  rintro ⟨σ, φ⟩ ⟨τ, ψ⟩ h
  simp only [ManySorted.Arity.prod.injEq] at h
  obtain rfl := Label.ofArity_injective h.1
  rw [eq_of_encode_eq φ ψ h.2]

variable (L) in
/-- **The number of formulas** is at most `max ℵ₀ (#S + L.card)`. -/
theorem card_sigma_le :
    #(Σ σ : ManySorted.Arity S, L.Formula σ) ≤ max ℵ₀ (lift.{max u v} #S + L.card) := by
  refine (mk_le_of_injective encode_injective).trans <| (ManySorted.Arity.card_le _).trans ?_
  exact max_le (le_max_left _ _) (card_label_le L)

end Formula

end Language

end ManySorted
