/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicholson, Mathias Stout
-/
module

public import MultisortedLogic.Algebra.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Tactic.Abel

/-!
# Terms of the language of ordered abelian groups

The language `Language.oag s` of ordered abelian groups on a sort `s`, and the description of its
terms as integer linear forms in their variables.

## Main definitions

* `Language.oag s`: the language with `0`, `+`, `-` and `≤` on the sort `s`.
* `oagStructure M`: the structure for `Language.oag s` given by the operations and the order on
  `M s`.
* `nsmulT`, `zsmulT`: the multiples of a term by natural numbers and integers.
* `termValues L s xs`: the values at `xs` of the terms of sort `s`, a subgroup of `M s`.

## Main results

* `exists_term_realize_eq_lift`: every integer linear form in the variables of sort `s` is the value
  of a term, in any language with symbols for the group operations on `s`.
* `Term.exists_realize_eq_lift`: conversely, the value of a term of `Language.oag s` is an integer
  linear form in its variables, the same in every abelian group.
* `Term.exists_realize_eq_add_zsmul`: a term in the variables of `σ ⨯ ⦃s⦄` has the value
  `u(x) + k • b` at `(x, b)`, for a term `u` in the variables of `σ` and an integer `k`. This is
  the form in which the quantifier elimination for divisible ordered abelian groups uses terms.
* `oag_embedding_iff`: the embeddings of structures for `Language.oag s` on ordered abelian groups
  are the injective families of maps that are additive and reflect the order on `s`.
-/

@[expose] public section

namespace ManySorted.Language

open Arity Structure

universe u v w w' z

variable {S : Type z}

/-! ### The language of ordered abelian groups -/

/-- The function symbols of the language of ordered abelian groups on the sort `s`: addition,
negation and zero. -/
inductive oagFunc (s : S) : Arity S → S → Type
  | add : oagFunc s (⦃s⦄ ⨯ ⦃s⦄) s
  | neg : oagFunc s ⦃s⦄ s
  | zero : oagFunc s ⦃⦄ s

/-- The relation symbol of the language of ordered abelian groups on the sort `s`: the order. -/
inductive oagRel (s : S) : Arity S → Type
  | le : oagRel s (⦃s⦄ ⨯ ⦃s⦄)

/-- The language of ordered abelian groups on the sort `s`: `0`, `+`, `-` and `≤`. -/
protected abbrev oag (s : S) : Language.{0, 0} S where
  Functions := oagFunc s
  Relations := oagRel s

instance (s : S) : OAGroupL (Language.oag s) s where
  addFunc := .add
  negFunc := .neg
  zeroConst := .zero
  orderF := .rel .le (.prod (.var (.left .var)) (.var (.right .var)))

section Compatible

variable {s : S} {M : S → Type w} [(Language.oag s).Structure M]

/-! In a compatible structure, the symbols of `Language.oag s` are interpreted as the operations and
the order on `M s`. These are the `Compatible*` lemmas for the symbols themselves, which a case
split on a symbol produces. -/

@[simp]
theorem oagFunc.funMap_add [Add (M s)] [CompatibleAddL (Language.oag s) M s]
    (x : M [^] (⦃s⦄ ⨯ ⦃s⦄)) : funMap (L := Language.oag s) oagFunc.add x = x.1 + x.2 :=
  CompatibleAddL.funMap_add x

@[simp]
theorem oagFunc.funMap_neg [Neg (M s)] [CompatibleNegL (Language.oag s) M s] (x : M s) :
    funMap (L := Language.oag s) oagFunc.neg x = -x :=
  CompatibleNegL.funMap_neg x

@[simp]
theorem oagFunc.funMap_zero [Zero (M s)] [CompatibleZeroL (Language.oag s) M s] (x : M [^] ⦃⦄) :
    funMap (L := Language.oag s) (M := M) oagFunc.zero x = 0 :=
  CompatibleZeroL.funMap_zero

@[simp]
theorem oagRel.relMap_le_iff [LE (M s)] [CompatibleOrderL (Language.oag s) M s]
    (x : M [^] (⦃s⦄ ⨯ ⦃s⦄)) : RelMap (L := Language.oag s) oagRel.le x ↔ x.1 ≤ x.2 := by
  have h := CompatibleOrderL.realize_orderF (L := Language.oag s) (M := M) (s := s) x
  exact h

end Compatible

section Structure

variable {s : S} (M : S → Type w) [Add (M s)] [Neg (M s)] [Zero (M s)] [LE (M s)]

/-- The structure for the language of ordered abelian groups on `M` given by the operations and the
order on `M s`. -/
@[reducible] def oagStructure : (Language.oag s).Structure M where
  funMap
    | .add, x => x.1 + x.2
    | .neg, x => -x
    | .zero, _ => 0
  RelMap
    | .le, x => x.1 ≤ x.2

/-- The structure `oagStructure M` is compatible with the operations and the order on `M s`. -/
theorem oagStructure_compatible :
    letI := oagStructure (s := s) M
    CompatibleOAGroupL (Language.oag s) M s :=
  letI := oagStructure (s := s) M
  { funMap_add := fun _ => rfl, funMap_neg := fun _ => rfl, funMap_zero := rfl,
    realize_orderF := fun _ => Iff.rfl }

end Structure

/-! ### Multiples of terms -/

section TermSmul

variable {L : Language.{u, v} S} {s : S} {Γ : Arity S}

/-- The `n`-fold sum `t + ⋯ + t` of a term with itself. -/
def nsmulT [AMonoidL L s] : ℕ → L.Term Γ ⦃s⦄ → L.Term Γ ⦃s⦄
  | 0, _ => 0
  | n + 1, t => nsmulT n t +ₗ t

/-- The integer multiple `k • t` of a term, by iterated addition and negation. -/
def zsmulT [AGroupL L s] : ℤ → L.Term Γ ⦃s⦄ → L.Term Γ ⦃s⦄
  | .ofNat n, t => nsmulT n t
  | .negSucc n, t => -ₗ(nsmulT (n + 1) t)

variable {M : S → Type w} [L.Structure M]

@[simp]
theorem realize_nsmulT [AMonoidL L s] [AddMonoid (M s)] [CompatibleAMonoidL L M s] (n : ℕ)
    (t : L.Term Γ ⦃s⦄) (xs : M [^] Γ) : (nsmulT n t).realize xs = n • t.realize xs := by
  induction n with
  | zero => simp [nsmulT]
  | succ n ih => simp [nsmulT, ih, succ_nsmul]

/-- `nsmulT` realizes as `nsmulRec`, which only needs `0` and `+`. -/
theorem realize_nsmulT_nsmulRec [AMonoidL L s] [Add (M s)] [Zero (M s)]
    [CompatibleAMonoidL L M s] (n : ℕ) (t : L.Term Γ ⦃s⦄) (xs : M [^] Γ) :
    (nsmulT n t).realize xs = nsmulRec n (t.realize xs) := by
  induction n with
  | zero => simp [nsmulT, nsmulRec]
  | succ n ih => simp [nsmulT, nsmulRec, ih]

@[simp]
theorem realize_zsmulT [AGroupL L s] [AddGroup (M s)] [CompatibleAGroupL L M s] (k : ℤ)
    (t : L.Term Γ ⦃s⦄) (xs : M [^] Γ) : (zsmulT k t).realize xs = k • t.realize xs := by
  cases k with
  | ofNat n => simp [zsmulT, natCast_zsmul]
  | negSucc n => simp [zsmulT, negSucc_zsmul]

end TermSmul

/-! ### Values of terms -/

section TermValues

variable {L : Language.{u, v} S} {s : S} {Γ : Arity S} {M : S → Type w} [L.Structure M]
  [AGroupL L s] [AddGroup (M s)] [CompatibleAGroupL L M s]

variable (L s) in
/-- The values at `xs` of the terms of sort `s` in the variables of `xs`, a subgroup of `M s`. -/
def termValues (xs : M [^] Γ) : AddSubgroup (M s) where
  carrier := Set.range fun t : L.Term Γ ⦃s⦄ => t.realize xs
  zero_mem' := ⟨0, realize_zero xs⟩
  add_mem' := by
    rintro _ _ ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
    exact ⟨t₁ +ₗ t₂, by simp⟩
  neg_mem' := by
    rintro _ ⟨t, rfl⟩
    exact ⟨-ₗt, by simp⟩

theorem mem_termValues {xs : M [^] Γ} {a : M s} :
    a ∈ termValues L s xs ↔ ∃ t : L.Term Γ ⦃s⦄, t.realize xs = a :=
  Iff.rfl

theorem realize_mem_termValues (t : L.Term Γ ⦃s⦄) (xs : M [^] Γ) :
    t.realize xs ∈ termValues L s xs :=
  ⟨t, rfl⟩

end TermValues

/-! ### Terms as linear forms -/

section LinearForm

variable {s : S} {Γ : Arity S}

/-- **Linear forms are terms**: every integer linear form in the variables of sort `s` is the value
of a term, in any language with symbols for the group operations on `s`. -/
theorem exists_term_realize_eq_lift {L : Language.{u, v} S} [AGroupL L s]
    (p : FreeAddCommGroup (Γ.Idx s)) :
    ∃ t : L.Term Γ ⦃s⦄, ∀ (M : S → Type w) [L.Structure M] [AddCommGroup (M s)]
      [CompatibleAGroupL L M s] (xs : M [^] Γ),
      t.realize xs = FreeAddCommGroup.lift (xs.get s) p := by
  induction p using FreeAddCommGroup.induction_on with
  | zero => exact ⟨0, fun M _ _ _ xs => by simp⟩
  | of i => exact ⟨.var i, fun M _ _ _ xs => by simp⟩
  | neg i ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨-ₗt, fun M _ _ _ xs => by simp [ht]⟩
  | add p q ihp ihq =>
    obtain ⟨t₁, ht₁⟩ := ihp
    obtain ⟨t₂, ht₂⟩ := ihq
    exact ⟨t₁ +ₗ t₂, fun M _ _ _ xs => by simp [ht₁, ht₂]⟩

/-- The entries of sort `s` of the value of a tuple of terms of `Language.oag s` are integer linear
forms in the variables, the same in every abelian group. -/
theorem Term.exists_get_realize_eq_lift {τ : Arity S} (t : (Language.oag s).Term Γ τ)
    (j : τ.Idx s) :
    ∃ p : FreeAddCommGroup (Γ.Idx s), ∀ (M : S → Type w) [(Language.oag s).Structure M]
      [AddCommGroup (M s)] [CompatibleAGroupL (Language.oag s) M s] (xs : M [^] Γ),
      (t.realize xs).get s j = FreeAddCommGroup.lift (xs.get s) p := by
  induction t with
  | var i =>
    cases j
    exact ⟨.of i, fun M _ _ _ xs => by simp⟩
  | func f ts ih =>
    cases j
    cases f with
    | add =>
      obtain ⟨p, hp⟩ := ih (.left .var)
      obtain ⟨q, hq⟩ := ih (.right .var)
      refine ⟨p + q, fun M _ _ _ xs => ?_⟩
      have hp := hp M xs
      have hq := hq M xs
      simp only [Interpret.get_left, Interpret.get_right, Interpret.get_var] at hp hq
      simp [hp, hq]
    | neg =>
      obtain ⟨p, hp⟩ := ih .var
      refine ⟨-p, fun M _ _ _ xs => ?_⟩
      have hp := hp M xs
      simp only [Interpret.get_var] at hp
      simp [hp]
    | zero => exact ⟨0, fun M _ _ _ xs => by simp⟩
  | nil => cases j
  | prod t₁ t₂ ih₁ ih₂ =>
    cases j with
    | left j =>
      obtain ⟨p, hp⟩ := ih₁ j
      exact ⟨p, fun M _ _ _ xs => by simpa using hp M xs⟩
    | right j =>
      obtain ⟨p, hp⟩ := ih₂ j
      exact ⟨p, fun M _ _ _ xs => by simpa using hp M xs⟩

/-- **Terms are linear forms**: the value of a term of `Language.oag s` is an integer linear form in
its variables, the same in every abelian group. -/
theorem Term.exists_realize_eq_lift (t : (Language.oag s).Term Γ ⦃s⦄) :
    ∃ p : FreeAddCommGroup (Γ.Idx s), ∀ (M : S → Type w) [(Language.oag s).Structure M]
      [AddCommGroup (M s)] [CompatibleAGroupL (Language.oag s) M s] (xs : M [^] Γ),
      t.realize xs = FreeAddCommGroup.lift (xs.get s) p := by
  obtain ⟨p, hp⟩ := t.exists_get_realize_eq_lift .var
  exact ⟨p, fun M _ _ _ xs => by simpa using hp M xs⟩

/-- The images of the variables of `σ ⨯ ⦃s⦄` when the last one is peeled off: a variable of `σ`
is a generator, and the last variable counts toward the coefficient. -/
private def peelVar {σ : Arity S} : (σ ⨯ ⦃s⦄).Idx s → FreeAddCommGroup (σ.Idx s) × ℤ
  | .left i => (.of i, 0)
  | .right _ => (0, 1)

private theorem lift_eq_lift_peelVar {σ : Arity S} {G : Type*} [AddCommGroup G]
    (f : (σ ⨯ ⦃s⦄).Idx s → G) (p : FreeAddCommGroup ((σ ⨯ ⦃s⦄).Idx s)) :
    FreeAddCommGroup.lift f p =
      FreeAddCommGroup.lift (fun i => f (.left i)) (FreeAddCommGroup.lift peelVar p).1 +
        (FreeAddCommGroup.lift peelVar p).2 • f (.right .var) := by
  induction p using FreeAddCommGroup.induction_on with
  | zero => simp
  | of i =>
    cases i with
    | left i => simp [peelVar]
    | right j =>
      cases j
      simp [peelVar]
  | neg i ih => rw [map_neg, map_neg, ih, Prod.fst_neg, Prod.snd_neg, map_neg, neg_zsmul, neg_add]
  | add p q ihp ihq =>
    rw [map_add, map_add, ihp, ihq, Prod.fst_add, Prod.snd_add, map_add, add_zsmul]
    abel

/-- **Peeling off the last variable**: a term of `Language.oag s` in the variables of `σ ⨯ ⦃s⦄` has
the value `u(x) + k • b` at `(x, b)`, for a term `u` in the variables of `σ` and an integer `k`. -/
theorem Term.exists_realize_eq_add_zsmul {σ : Arity S}
    (t : (Language.oag s).Term (σ ⨯ ⦃s⦄) ⦃s⦄) :
    ∃ (u : (Language.oag s).Term σ ⦃s⦄) (k : ℤ), ∀ (M : S → Type w)
      [(Language.oag s).Structure M] [AddCommGroup (M s)] [CompatibleAGroupL (Language.oag s) M s]
      (x : M [^] σ) (b : M s), t.realize ((x, b) : M [^] (σ ⨯ ⦃s⦄)) = u.realize x + k • b := by
  obtain ⟨p, hp⟩ := t.exists_realize_eq_lift
  obtain ⟨u, hu⟩ :=
    exists_term_realize_eq_lift (L := Language.oag s) (FreeAddCommGroup.lift peelVar p).1
  refine ⟨u, (FreeAddCommGroup.lift peelVar p).2, fun M _ _ _ x b => ?_⟩
  rw [hp M, hu M, lift_eq_lift_peelVar]
  rfl

end LinearForm

/-! ### Embeddings -/

section Embedding

variable {s : S} {M : S → Type w} {N : S → Type w'} [(Language.oag s).Structure M]
  [(Language.oag s).Structure N] [AddCommGroup (M s)] [AddCommGroup (N s)] [LE (M s)] [LE (N s)]
  [CompatibleOAGroupL (Language.oag s) M s] [CompatibleOAGroupL (Language.oag s) N s]

/-- An embedding of structures for `Language.oag s` is additive on the sort `s`. -/
theorem Embedding.oag_map_add (e : M ↪[Language.oag s] N) (a b : M s) :
    e s (a + b) = e s a + e s b := by
  simpa using StrongHomClass.map_fun (L := Language.oag s) (M := M) (N := N) e oagFunc.add
    ((a, b) : M [^] (⦃s⦄ ⨯ ⦃s⦄))

/-- An embedding of structures for `Language.oag s` reflects the order on the sort `s`. -/
theorem Embedding.oag_le_iff (e : M ↪[Language.oag s] N) (a b : M s) :
    e s a ≤ e s b ↔ a ≤ b := by
  simpa using StrongHomClass.map_rel (L := Language.oag s) (M := M) (N := N) e oagRel.le
    ((a, b) : M [^] (⦃s⦄ ⨯ ⦃s⦄))

/-- The embedding of structures for `Language.oag s` given by an injective family of maps that is
additive and reflects the order on the sort `s`. -/
def oagEmbeddingOfOrderedGroupHom (f : ∀ s', M s' → N s')
    (hinj : ∀ s', Function.Injective (f s')) (hadd : ∀ a b : M s, f s (a + b) = f s a + f s b)
    (hle : ∀ a b : M s, f s a ≤ f s b ↔ a ≤ b) : M ↪[Language.oag s] N where
  toEmbedding s' := ⟨f s', hinj s'⟩
  map_fun' := by
    have hneg : ∀ a : M s, f s (-a) = -f s a := map_neg (AddMonoidHom.mk' (f s) hadd)
    have hzero : f s 0 = 0 := map_zero (AddMonoidHom.mk' (f s) hadd)
    rintro σ t (_ | _ | _) x
    · simpa using hadd x.1 x.2
    · simpa using hneg x
    · simpa using hzero
  map_rel' := by
    rintro σ ⟨⟩ x
    simpa using hle x.1 x.2

/-- **Embeddings of ordered abelian groups**: the embeddings of structures for `Language.oag s`
are the injective families of maps that are additive and reflect the order on the sort `s`. -/
theorem oag_embedding_iff (f : ∀ s', M s' → N s') :
    (∃ e : M ↪[Language.oag s] N, ⇑e = f) ↔ (∀ s', Function.Injective (f s')) ∧
      (∀ a b : M s, f s (a + b) = f s a + f s b) ∧ ∀ a b : M s, f s a ≤ f s b ↔ a ≤ b := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.injective, e.oag_map_add, e.oag_le_iff⟩
  · rintro ⟨hinj, hadd, hle⟩
    exact ⟨oagEmbeddingOfOrderedGroupHom f hinj hadd hle, rfl⟩

end Embedding

end ManySorted.Language
