import ProdExpr.Semantics
import Mathlib.Computability.Encoding
import Mathlib.Logic.Small.List
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Order


universe u u' v w z

namespace MSFirstOrder

open Cardinal Computability

/-! ## Cardinality of Signature

The cardinality of `Signature S` equals `max ℵ₀ #S`.
- Lower bound: `fromList` is injective, so `#(List S) ≤ #(Signature S)`
- Upper bound: Encode signatures into `List (Fin 3 ⊕ S)`
-/

section signature_encoding
namespace Signature

variable {S : Type z} {σ : Signature S}

def encode : Signature S → List (Fin 3 ⊕ S)
  | .nil => [Sum.inl 0]
  | .of s => [Sum.inr s]
  | .prod σ τ => (Sum.inl 1 :: σ.encode) ++ (Sum.inl 2 :: τ.encode)

def size : Signature S → ℕ
  | .nil => 1
  | .of _ => 1
  | .prod σ τ => 2 + σ.size + τ.size

/-- The length of the encoding. -/
@[simp]
theorem encode_length : (encode σ).length = σ.size := by
  induction σ
  · rfl
  · rfl
  · simp only [encode, Fin.isValue, List.cons_append, List.length_cons, List.length_append, size] ;
    linarith

/--
A prefix parser for `encode`.

Returns `some (σ, rest)` when `l` begins with a valid encoding of `σ` followed by `rest`.

This is fuel-based to make termination obvious: each recursive call decreases the fuel.
-/
def decodeAux : ℕ → List (Fin 3 ⊕ S) → Option (Signature S × List (Fin 3 ⊕ S))
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, (Sum.inl (0 : Fin 3)) :: xs => some (.nil, xs)
  | _ + 1, (Sum.inr s) :: xs => some (.of s, xs)
  | n + 1, (Sum.inl (1 : Fin 3)) :: xs =>
      match decodeAux n xs with
      | some (σ, (Sum.inl (2 : Fin 3)) :: rest') =>
          match decodeAux n rest' with
          | some (τ, rest'') => some (.prod σ τ, rest'')
          | none => none
      | _ => none
  | _ + 1, (Sum.inl (2 : Fin 3)) :: _ => none

/--
Total decoder: succeeds only if the whole list is exactly one encoding.

We use `l.length` as fuel, which is always enough for any successful parse.
-/
def decode : List (Fin 3 ⊕ S) → Option (Signature S)
  | l =>
    match decodeAux (S := S) l.length l with
    | some (σ, []) => some σ
    | _ => none

/-- `decodeAux` consumes exactly the encoding prefix it should, provided enough fuel. -/
theorem decodeAux_encode_append (σ : Signature S) (l : List (Fin 3 ⊕ S)) :
    ∀ n, (encode (S := S) σ ++ l).length ≤ n →
      decodeAux (S := S) n (encode (S := S) σ ++ l) = some (σ, l) := by
  induction σ generalizing l with
  | nil =>
      intro n hn
      cases n with
      | zero => simp only [encode, Fin.isValue, List.cons_append, List.nil_append, List.length_cons,
        nonpos_iff_eq_zero, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false]
        at hn
      | succ n => simp only [encode, Fin.isValue, List.cons_append, List.nil_append, decodeAux]
  | of s =>
      intro n hn
      cases n with
      | zero => simp only [encode, List.cons_append, List.nil_append, List.length_cons,
        nonpos_iff_eq_zero, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false]
          at hn
      | succ n => simp only [encode, List.cons_append, List.nil_append, decodeAux]
  | prod σ τ ihσ ihτ =>
      intro n hn
      cases n with
      | zero => simp only [encode, Fin.isValue, List.cons_append, List.append_assoc,
        List.length_cons, List.length_append, encode_length, nonpos_iff_eq_zero,
        Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false, and_self] at hn
      | succ n =>
          set xs : List (Fin 3 ⊕ S) :=
            (encode (S := S) σ ++ (Sum.inl (2 : Fin 3) :: encode (S := S) τ) ++ l) with hxs
          have hxs_le : xs.length ≤ n := by simp only [encode, Fin.isValue, List.cons_append,
            List.append_assoc, List.length_cons, List.length_append, encode_length,
            add_le_add_iff_right, hxs] at hn ⊢; omega
          have hleft := ihσ (l := (Sum.inl 2 :: encode τ) ++ l) n (by simp_all only
            [List.length_append, encode_length, List.append_assoc, Fin.isValue, List.cons_append,
            List.length_cons, xs])
          have hright := ihτ (l := l) n (by
            simp only [hxs, Fin.isValue, List.append_assoc, List.cons_append, List.length_append,
              encode_length, List.length_cons] at hxs_le ⊢; omega)
          simp_all only [List.length_append, encode_length, encode, Fin.isValue, List.cons_append,
            List.append_assoc, List.length_cons, add_le_add_iff_right, decodeAux]

/-- Exact-fuel corollary: use `length` as fuel. -/
theorem decodeAux_encode_append_exact (σ : Signature S) (l : List (Fin 3 ⊕ S)) :
    decodeAux (encode σ ++ l).length (encode σ ++ l) = some (σ, l) := by
  simpa only [List.length_append, encode_length] using decodeAux_encode_append
    (σ := σ) (l := l) _ (le_rfl)

/-- `decode` is a left inverse of `encode`. -/
@[simp] theorem decode_encode (σ : Signature S) :
    decode (encode σ) = some σ := by
  unfold decode
  let h := decodeAux_encode_append_exact σ []
  simp only [List.append_nil, encode_length] at h
  simp only [encode_length, h]

/-- `encode` is injective (by decoding). -/
theorem encode_injective : Function.Injective (encode (S := S)) := by
  intro σ τ h
  have : decode (S := S) (encode (S := S) σ) = decode (S := S) (encode (S := S) τ) :=
    congrArg (decode (S := S)) h
  have : (some σ : Option (Signature S)) = some τ := by
    simpa only [Option.some.injEq, decode_encode] using this
  exact Option.some.inj this

/-- An encoding of terms as lists. -/
@[simps]
protected def encoding : Encoding (Signature S) where
  Γ := Fin 3 ⊕ S
  encode := encode
  decode l := decode l
  decode_encode t := decode_encode t

private def sig_inj : ℕ → Signature S :=
  fun n => match n with
  | 0 => Signature.nil
  | n + 1 => Signature.prod (sig_inj n) .nil

lemma sig_inj_inj : Function.Injective (sig_inj (S:=S )) := by
  intro x y h
  have : ∀ n, (sig_inj (S:= S) n).size = 3*n + 1 := by
    intro n
    induction n
    case zero => rw[sig_inj, Signature.size]
    case succ n ih =>
      rw[sig_inj, Signature.size, ih, Signature.size]
      omega
  apply congrArg Signature.size at h
  rw[this, this] at h
  linarith

instance : Infinite (Signature S) :=
  Infinite.of_injective sig_inj sig_inj_inj

/-- Cardinality of `Signature S` equals `max ℵ₀ #S` when `S` is nonempty. -/
theorem card_of_signature : #(Signature S) = max ℵ₀ #S := by
  apply le_antisymm
  · -- Upper bound: encode into List (Unit ⊕ S)
    calc #(Signature S) ≤ #(List (Fin 3 ⊕ S)) :=
           mk_le_of_injective (f:= encode (S:= S)) encode_injective
      _ = max #(Fin 3 ⊕ S)  ℵ₀ := mk_list_eq_max_mk_aleph0 _
      _ = max ℵ₀ #S := by
          simp only [mk_sum, mk_fintype, Fintype.card_fin, Nat.cast_ofNat, lift_ofNat, lift_uzero]
          rcases finite_or_infinite S with hfin | hinf
          · -- finite S
            have hS : #S < ℵ₀ := by simp only [mk_lt_aleph0]
            have h3 : (3 : Cardinal) < ℵ₀ := by
              simpa only [Nat.cast_ofNat] using Cardinal.natCast_lt_aleph0
            have hsum : (3 : Cardinal) + #S < ℵ₀ :=
              Cardinal.add_lt_of_lt (c := ℵ₀) (le_rfl) h3 hS
            simp only [max_eq_right (le_of_lt hsum), mk_le_aleph0, sup_of_le_left]
          · -- infinite S
            have h : ℵ₀ ≤ #S := Cardinal.aleph0_le_mk S
            have hsum : (3 : Cardinal) + #S = #S := by
              simpa only [Nat.cast_ofNat] using (Cardinal.nat_add_eq (a := #S) (n := 3) h)
            -- LHS becomes max #S ℵ₀, then commute
            simp only [hsum, aleph0_le_mk, sup_of_le_left, sup_of_le_right]
  · by_cases h : IsEmpty S
    case pos =>
      simp only [mk_eq_zero, zero_le, sup_of_le_left]
      apply @aleph0_le_mk _ (Infinite.of_injective (β := ℕ) sig_inj sig_inj_inj)
    -- Lower bound: fromList is injective
    case neg =>
    have  : Nonempty S := not_isEmpty_iff.1 h
    calc max ℵ₀ #S = max #S ℵ₀ := max_comm _ _
      _ = #(List S) := (mk_list_eq_max_mk_aleph0 S).symm
      _ ≤ #(Signature S) := by
        apply mk_le_of_injective (f := fromList)
        intro l l' h
        apply congrArg toList at h
        simp_all only [toList_fromList]

/-- Cardinality bound via injective function into signatures. -/
theorem card_le_of_injective {X S : Type u}
    (f : X → Signature S) (hf : Function.Injective f) :
    #X ≤ max ℵ₀ #S :=
  (mk_le_of_injective hf).trans card_of_signature.le

end Signature
end signature_encoding


namespace MSLanguage


open Cardinal
open Computability List MSStructure Fin Signature

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts}
variable {M : Fam.{w} Sorts} [L.MSStructure M]
variable {α : Fam.{u'} Sorts}
variable {σ : Signature Sorts}

abbrev TCode (L : MSLanguage Sorts) (α : Fam Sorts) :=
  (Σ s, α s) ⊕ ((Σ η s, L.Functions η s))

namespace Term

def TreeEncode : (Sigma (L.Term α)) → Signature (L.TCode α)
  | ⟨ _ , var s  i⟩ =>  of (Sum.inl ⟨s, i⟩)
  | ⟨ _ , .nil ⟩ =>  .nil
  | ⟨ _ , @prod _ _ _ σ₁ σ₂ t₁ t₂⟩ => .prod (TreeEncode ⟨σ₁, t₁⟩)  (TreeEncode ⟨σ₂, t₂⟩)
  | ⟨ _, @func _ _ _ σ s f t⟩  => .prod (of (Sum.inr ⟨ σ,s, f⟩)) (TreeEncode ⟨σ, t⟩)

def TreeDecode [DecidableEq Sorts] : Signature (L.TCode α)  → Option (Σ σ, L.Term α σ)
  | .nil => some ⟨.nil, .nil⟩
  | of (Sum.inl ⟨s, i⟩) => some ⟨of s , var s  i⟩
  | of (Sum.inr _) => none
  | Signature.prod σ τ =>
    match σ with
    | of (Sum.inr ⟨σ,s, f⟩) =>
      match TreeDecode τ with
      | some (⟨η, t⟩) =>
        if h: (σ = η) then
          some ⟨of s, func f (h ▸ t)⟩
        else
          none
      | _ => none
    | σ  =>
      match TreeDecode σ, TreeDecode τ with
      | some (⟨σ₁, t₁⟩),some (⟨σ₂, t₂⟩)   => some (⟨σ₁.prod σ₂, prod t₁ t₂⟩)
      | _, _  => none

lemma TreeDecode_TreeEncode
    [DecidableEq Sorts] :
    ∀ (st : Σ σ, L.Term α σ),
      Term.TreeDecode (Term.TreeEncode st) = some st
  := by
  classical
  intro st
  rcases st with ⟨σ, t⟩
  induction t with
  | nil =>
      simp only [TreeEncode, TreeDecode]
  | var s i =>
      simp only [TreeEncode, TreeDecode]
  | @func σ s f t ih =>
      simp only [TreeEncode, TreeDecode, ih, ↓reduceDIte]
  | @prod σ₁ σ₂ t₁ t₂ ih1 ih2 =>
      cases t₁ <;> simp_all only [TreeEncode, TreeDecode]

/-- TreeEncode never produces `of (Sum.inr _)` at the top level.
    This is key for distinguishing `prod` from `func` encodings. -/
lemma TreeEncode_ne_of_inr (st : Sigma (L.Term α)) (x : Σ η s, L.Functions η s) :
    TreeEncode st ≠ Signature.of (Sum.inr x) := by
  rcases st with ⟨σ, t⟩
  cases t <;> simp only [TreeEncode, ne_eq, of.injEq, reduceCtorEq, not_false_eq_true]

/-- `TreeEncode` is injective (direct proof without DecidableEq). -/
theorem TreeEncode_injective :
    Function.Injective (Term.TreeEncode (L := L) (α := α)) := by
  intro ⟨σ₁, t₁⟩ ⟨σ₂, t₂⟩ h
  induction t₁ generalizing σ₂ t₂ with
  | nil =>
      cases t₂ <;> simp_all only [TreeEncode, reduceCtorEq]
  | var s i =>
      cases t₂ with
      | var s' i' =>
          simp only [TreeEncode, Signature.of.injEq, Sum.inl.injEq, Sigma.mk.injEq] at h
          obtain ⟨rfl, hi⟩ := h
          simp_all only [heq_eq_eq]
      | _ => simp only [TreeEncode, reduceCtorEq] at h
  | @prod σ₁₁ σ₁₂ t₁₁ t₁₂ ih₁ ih₂ =>
      cases t₂ with
      | nil => simp only [TreeEncode, reduceCtorEq] at h
      | var => simp only [TreeEncode, reduceCtorEq] at h
      | @func σ' s f t' =>
          simp only [TreeEncode, Signature.prod.injEq] at h
          exact absurd h.1.symm (by simp_all only [Sigma.mk.injEq,
            TreeEncode_ne_of_inr ⟨σ₁₁, t₁₁⟩ ⟨σ',s, f⟩, false_and])
      | @prod σ₂₁ σ₂₂ t₂₁ t₂₂ =>
          simp only [TreeEncode, Signature.prod.injEq] at h
          have heq₁ := ih₁ σ₂₁ t₂₁ h.1
          have heq₂ := ih₂ σ₂₂ t₂₂ h.2
          simp only [Sigma.mk.injEq] at heq₁ heq₂
          obtain ⟨rfl, h₁⟩ := heq₁
          obtain ⟨rfl, h₂⟩ := heq₂
          simp_all only [Sigma.mk.injEq, heq_eq_eq, true_and]
  | @func σ' s f t ih =>
      cases t₂ with
      | nil => simp only [TreeEncode, reduceCtorEq] at h
      | var => simp only [TreeEncode, reduceCtorEq] at h
      | @prod σ₂₁ σ₂₂ t₂₁ t₂₂ =>
          simp only [TreeEncode, Signature.prod.injEq] at h
          exact absurd h.1 (by
            intro h'';
            let h''' := TreeEncode_ne_of_inr ⟨σ₂₁, t₂₁⟩ ⟨σ',s, f⟩
            rw[←h''] at h'''
            apply h'''
            rfl)
      | @func σ₂' s' f' t' =>
          simp only [TreeEncode, Signature.prod.injEq, Signature.of.injEq, Sum.inr.injEq,
                     Sigma.mk.injEq] at h
          obtain ⟨⟨rfl, rfl, hf⟩, ht⟩ := h
          rw [Sigma.mk.injEq, heq_eq_eq, func.injEq]
          simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using ih σ' t' ht

/-- An encoding of terms as lists. -/
@[simps]
protected def encoding [DecidableEq Sorts] : Encoding (Sigma (L.Term α)) where
  Γ := Fin 3 ⊕ L.TCode α
  encode := Signature.encode ∘ TreeEncode
  decode l := Signature.decode l >>= TreeDecode
  decode_encode t := by simp only [Function.comp_apply, decode_encode, Option.bind_eq_bind,
    Option.bind_some, TreeDecode_TreeEncode]


theorem add_def_ulift (α : Type u) (β : Type v) :
   lift.{v} (#α : Cardinal) + lift.{u} #β = #(α ⊕ β) := by
  classical
  -- lift both into max u v
  have := (Cardinal.add_def (α := ULift.{v} α) (β := ULift.{u} β))
  -- rewrite the lifted cardinals away
  -- and rewrite the lifted sum away via an equivalence
  simp_all only [mk_uLift, mk_sum, lift_id]

theorem add_def_ulift' (α : Type u) (β : Type v) :
   lift.{max v z} (#α : Cardinal) + lift.{max u z} #β = lift.{z} #(α ⊕ β) := by
  classical
  -- lift both into max u v
  have := (Cardinal.add_def (α := ULift.{max z v} α) (β := ULift.{max z u} β))
  -- rewrite the lifted cardinals away
  -- and rewrite the lifted sum away via an equivalence
  simp_all only [mk_uLift, mk_sum, lift_id]
  rw[Term.add_def_ulift]
  simp only [mk_sum, lift_add, lift_lift]


/-- The code type cardinality bound lifts to max with ℵ₀. -/
theorem TCode_card_le :
    max ℵ₀ #(L.TCode α) ≤ max ℵ₀ (max (lift.{max u z, max u' z} #(Σ s, α s))
                                      (lift.{max u' z, max u z} #(Σ η s, L.Functions η s))) := by
  unfold TCode
  rw [mk_sum]
  have h := Cardinal.add_le_max (lift.{max u z} #(Σ s, α s))
            (lift.{max u' z} #(Σ η s, L.Functions η s))
  calc max ℵ₀ (lift.{max u z} #(Σ s, α s) + lift.{max u' z} #(Σ η s, L.Functions η s))
      ≤ max ℵ₀ (max (max (lift.{max u z} #(Σ s, α s))
        (lift.{max u' z} #(Σ η s, L.Functions η s))) ℵ₀) :=
        max_le_max_left _ h
    _ = max ℵ₀ (max (lift.{max u z} #(Σ s, α s)) (lift.{max u' z} #(Σ η s, L.Functions η s))) := by
        simp only [max_comm, le_sup_left, sup_of_le_right]

theorem card_le' :
    #(Sigma (L.Term α)) ≤ max ℵ₀ #(L.TCode α) :=
    Signature.card_le_of_injective TreeEncode TreeEncode_injective

theorem card_le :
    #(Sigma (L.Term α)) ≤ max ℵ₀ (max (lift.{max u z, max u' z} #(Σ s, α s))
                                      (lift.{max u' z, max u z} #(Σ η s, L.Functions η s))) :=
  card_le'.trans TCode_card_le
/-
theorem card_le'' [DecidableEq Sorts] :
  #((σ : Signature Sorts) × (τ : Signature Sorts) × L.Term (fun s ↦ α s ⊕ σ.IdxFam s) τ)
        ≤ max ℵ₀  #(L.TCode α) := by
  apply le_trans (b:=  #((σ : Signature Sorts) × (Sigma (L.Term  (α ⊕ₛ σ.IdxFam)))))
  simp_all only [mk_sigma, ge_iff_le, le_refl]

  apply le_trans (b:=  #((σ : Signature Sorts) × (L.TCode (α ⊕ₛ σ.IdxFam))))
  · have h: ∀ (σ : Signature Sorts), #( Sigma (L.Term fun s ↦ α s ⊕ σ.IdxFam s))
    ≤ max ℵ₀ #( L.TCode fun s ↦ α s ⊕ σ.IdxFam s) := by
      intro σ
      apply card_le'

  ·
-/
end Term



/-! ## Encoding of Bounded Formulas

The cardinality of `Σ σ, L.BoundedFormula α σ` is bounded similarly to terms.
- We encode formulas as `Signature (L.BFCode α)` using a tree-based encoding
- The code type combines: terms (with their bound variable context), relations,
  signatures (for falsum/quantifier markers), and opcodes (for imp/all)
-/

section boundedformula_encoding

/-- The code type for bounded formula encoding.
    Combines:
    - Terms with their bound variable signature context
    - Relations
    - Signatures (for falsum and quantifier sort markers)
    - Opcodes (0 = imp, 1 = all)
-/
abbrev BFCode (L : MSLanguage Sorts) (α : Fam Sorts) :=
  (Σ (σ τ : Signature Sorts), L.Term (α ⊕ₛ σ.IdxFam) τ) ⊕
  ((Σ σ, L.Relations σ) ⊕
  (Signature Sorts ⊕ Fin 2))


namespace BoundedFormula

open Signature MSLanguage

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts}
variable {α : Fam.{u'} Sorts}


/-- Tree-based encoding of bounded formulas into signatures over the code type. -/
def TreeEncode : (Σ σ, L.BoundedFormula α σ) → Signature (L.BFCode α)
  | ⟨σ, .falsum⟩ => .of (Sum.inr (Sum.inr (Sum.inl σ)))
  | ⟨σ, .equal t₁ t₂⟩ => .prod (.of (Sum.inl ⟨σ, _, t₁⟩)) (.of (Sum.inl ⟨σ, _, t₂⟩))
  | ⟨σ, .rel R ts⟩ => .prod (.of (Sum.inr (Sum.inl ⟨_, R⟩))) (.of (Sum.inl ⟨σ, _, ts⟩))
  | ⟨σ, .imp φ₁ φ₂⟩ =>
      .prod (.prod (.of (Sum.inr (Sum.inr (Sum.inr 0)))) (TreeEncode ⟨σ, φ₁⟩))
            (TreeEncode ⟨σ, φ₂⟩)
  | ⟨σ, .all τ φ⟩ =>
      .prod (.of (Sum.inr (Sum.inr (Sum.inl τ))))
            (.prod (.of (Sum.inr (Sum.inr (Sum.inr 1)))) (TreeEncode ⟨σ ⨯ τ, φ⟩))
  termination_by sφ => sφ.2.size

/-- Decoding of signatures back to bounded formulas. -/
def TreeDecode [DecidableEq Sorts] : Signature (L.BFCode α) → Option (Σ σ, L.BoundedFormula α σ)
  -- falsum: encoded as .of (Sum.inr (Sum.inr (Sum.inl σ)))
  | .of (Sum.inr (Sum.inr (Sum.inl σ))) => some ⟨σ, .falsum⟩
  -- equal: encoded as .prod (.of (Sum.inl ⟨σ₁, τ₁, t₁⟩)) (.of (Sum.inl ⟨σ₂, τ₂, t₂⟩))
  | .prod (.of (Sum.inl ⟨σ₁, τ₁, t₁⟩)) (.of (Sum.inl ⟨σ₂, τ₂, t₂⟩)) =>
      if h : σ₁ = σ₂ ∧ τ₁ = τ₂ then
        some ⟨σ₁, .equal t₁ (h.1 ▸ h.2 ▸ t₂)⟩
      else
        none
  -- rel: encoded as .prod (.of (Sum.inr (Sum.inl ⟨σ', R⟩))) (.of (Sum.inl ⟨σ, τ, ts⟩))
  | .prod (.of (Sum.inr (Sum.inl ⟨σ', R⟩))) (.of (Sum.inl ⟨σ, τ, ts⟩)) =>
      if h : σ' = τ then
        some ⟨σ, .rel (h ▸ R) ts⟩
      else
        none
  -- imp: encoded as .prod (.prod (.of (Sum.inr (Sum.inr (Sum.inr 0)))) enc₁) enc₂
  | .prod (.prod (.of (Sum.inr (Sum.inr (Sum.inr 0)))) enc₁) enc₂ =>
      match TreeDecode enc₁, TreeDecode enc₂ with
      | some ⟨σ₁, φ₁⟩, some ⟨σ₂, φ₂⟩ =>
          if h : σ₁ = σ₂ then
            some ⟨σ₁, .imp φ₁ (h ▸ φ₂)⟩
          else
            none
      | _, _ => none
  -- all: encoded as .prod (.of (Sum.inr (Sum.inr (Sum.inl τ))))
  --                       (.prod (.of (Sum.inr (Sum.inr (Sum.inr 1)))) enc)
  | .prod (.of (Sum.inr (Sum.inr (Sum.inl τ)))) (.prod (.of (Sum.inr (Sum.inr (Sum.inr 1)))) enc) =>
      match TreeDecode enc with
      | some ⟨σ', φ⟩ =>
          -- σ' should be σ ⨯ τ, need to extract σ
          match σ' with
          | .prod σ τ' =>
              if h : τ = τ' then
                some ⟨σ, .all τ (h ▸ φ)⟩
              else
                none
          | _ => none
      | none => none
  -- anything else is invalid
  | _ => none

lemma TreeDecode_TreeEncode [DecidableEq Sorts] :
    ∀ (sφ : Σ σ, L.BoundedFormula α σ),
      TreeDecode (TreeEncode sφ) = some sφ := by
  intro ⟨σ, φ⟩
  induction φ with
  | falsum =>
      simp only [TreeEncode, TreeDecode]
  | equal t₁ t₂ =>
      simp only [TreeEncode, TreeDecode, and_self, ↓reduceDIte]
  | rel R ts =>
      simp only [TreeEncode, TreeDecode, ↓reduceDIte]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [TreeEncode, TreeDecode, ih₁, ih₂, ↓reduceDIte]
  | all τ φ ih =>
      simp only [TreeEncode, TreeDecode, ih, ↓reduceDIte]

/-- An encoding of bounded formulas as lists. -/
@[simps]
protected def encoding [DecidableEq Sorts] : Encoding (Σ σ, L.BoundedFormula α σ) where
  Γ := Fin 3 ⊕ L.BFCode α
  encode := Signature.encode ∘ TreeEncode
  decode l := Signature.decode l >>= TreeDecode
  decode_encode φ := by simp only [Function.comp_apply, decode_encode, Option.bind_eq_bind,
    Option.bind_some, TreeDecode_TreeEncode]

/-- TreeEncode is injective. -/
theorem TreeEncode_injective [DecidableEq Sorts] :
    Function.Injective (TreeEncode (L := L) (α := α)) := by
  intro φ₁ φ₂ h
  have := congrArg TreeDecode h
  simp only [TreeDecode_TreeEncode] at this
  exact Option.some.inj this



/-- BFCode is infinite (contains Signature Sorts which is infinite). -/
instance isInf : Infinite (L.BFCode α) := by
  -- Inject Signature Sorts into BFCode via the signature component
  let f : Signature Sorts → L.BFCode α := fun σ => Sum.inr (Sum.inr (Sum.inl σ))
  have hf : Function.Injective f := fun _ _ hxy => by
    simp only [f, Sum.inr.injEq, Sum.inl.injEq] at hxy
    exact hxy
  exact Infinite.of_injective f hf

/-- Cardinality bound for bounded formulas via the BFCode type. -/
theorem card_le'  [DecidableEq Sorts] :
    #(Σ σ, L.BoundedFormula α σ) ≤ #(L.BFCode α) := by
  have := Signature.card_le_of_injective TreeEncode (TreeEncode_injective (L := L) (α := α))
  simp_all only [max_eq_right, Cardinal.aleph0_le_mk ]



/-- Cardinality of BFCode is at least ℵ₀. -/
lemma aleph0_le_BFCode_card : ℵ₀ ≤ #(L.BFCode α) :=
  aleph0_le_mk _

lemma le_add_right' (a b c : Cardinal) (h : a ≤ b) : a ≤ b + c := by
  apply le_add_of_le_add_left (c := 0 )
  <;> simp_all

noncomputable
abbrev K : Cardinal :=
  max ℵ₀ (lift.{max u v u'} #Sorts + (lift.{max u v} #(Σ s, α s)) + (lift.{u'} L.card))

/-- BFCode cardinality is bounded by max ℵ₀ of α and L.card (for countable Sorts). -/
theorem BFCode_card [DecidableEq Sorts] :
    #(L.BFCode α) ≤ max ℵ₀ (lift.{max u v u'} #Sorts + (lift.{max u v} #(Σ s, α s)) + (lift.{u'} L.card)) := by
  classical
  set K : Cardinal := max ℵ₀ (lift.{max u v u'} #Sorts + (lift.{max u v} #(Σ s, α s)) + (lift.{u'} L.card))
  have hK : ℵ₀ ≤ K := le_max_left _ _
  have hSorts : lift.{max u v u'} #Sorts ≤ K := by
    unfold K
    refine le_trans (b:= (lift.{max u v u', z} #Sorts + lift.{max u v, max u' z} #((s : Sorts) × α s) + lift.{u', max (max u v) z} L.card))
              ?_ ?_
    · simp only [mk_sigma, lift_sum, add_assoc, self_le_add_right]
    · simp only [mk_sigma, lift_sum, le_sup_right]

  -- Countable signatures (used throughout the proof)

  unfold BFCode; rw [mk_sum]

  -- Bound the term component
  have hTerm : lift.{v} #(Σ (σ τ : Signature Sorts), L.Term (α ⊕ₛ σ.IdxFam) τ) ≤ K := by
    let f : Signature Sorts → Cardinal := fun σ => #(Σ τ, L.Term (α ⊕ₛ σ.IdxFam) τ)
    have hsum : #(Σ (σ : Signature Sorts), (Σ τ, L.Term (α ⊕ₛ σ.IdxFam) τ)) = Cardinal.sum f := by
      simp [f, mk_sigma]
    have hSig : Cardinal.lift #(Signature Sorts) ≤ max ℵ₀ #Sorts := by simp [card_of_signature]
    have hsum' : Cardinal.sum f ≤ (max ℵ₀ (lift.{(max u u')} #Sorts)) * _root_.iSup f := by
      refine (Cardinal.sum_le_lift_mk_mul_iSup f).trans (mul_le_mul_left ?_ _)
      rw[←lift_le.{(max u u')},lift_max, lift_aleph0, lift_id] at hSig
      exact hSig

    have hsum'' : Cardinal.sum f ≤ max ℵ₀ (lift.{max u u', z} #Sorts + _root_.iSup f):= by
      have := hsum'.trans (Cardinal.mul_le_max_of_aleph0_le_left (by simp only [ge_iff_le,
        le_sup_left]))
      rw[←Cardinal.add_eq_max (by simp only [ge_iff_le, le_sup_left]),
          ←Cardinal.add_eq_max (by simp only [ge_iff_le, le_refl]),
           add_assoc, Cardinal.add_eq_max (by simp only [ge_iff_le, le_refl])] at this
      exact this

    -- Each fiber is bounded by K.
    have hFib : ∀ σ, lift.{v} (f σ) ≤ K := by
      intro σ
      -- Bound the variable part: Σ s, α s ⊕ σ.IdxFam s.
      have hIdx : lift.{max u' z} #(Σ s, σ.IdxFam s) ≤ ℵ₀ := by
        have h:= mk_le_aleph0 (α := ULift.{max u' z} (Σ s, σ.IdxFam s))
        simp_all only [mk_sigma, lift_sum, le_sup_left, le_sup_iff, lift_le_aleph0, lift_id, mk_fintype,
          Fintype.card_ulift, ge_iff_le, natCast_le_aleph0, lift_natCast, K, f]
      have hSigmaSum :
          #(Σ s, α s ⊕ σ.IdxFam s) = lift.{z} #(Σ s, α s) + lift.{max u' z} #(Σ s, σ.IdxFam s) := by
        simpa [Cardinal.mk_sum] using
          (Cardinal.mk_congr (Equiv.sigmaSumDistrib (α := fun s => α s) (β := fun s => σ.IdxFam s)))
      have hVar0 :
          #(Σ s, α s ⊕ σ.IdxFam s) ≤
            max ℵ₀ (lift.{z} #(Σ s, α s)) := by
        have hVar' :
            #(Σ s, α s ⊕ σ.IdxFam s) ≤ max ℵ₀ (lift.{z} #(Σ s, α s))  := by
          -- use the sum decomposition and bound the finite part
          have hSum' : lift.{z} #(Σ s, α s) + lift.{max u' z} #(Σ s, σ.IdxFam s) ≤
              max (max (lift.{z} #(Σ s, α s)) (lift.{max u' z} #(Σ s, σ.IdxFam s))) ℵ₀ :=
            Cardinal.add_le_max _ _
          have hSum'' : lift.{z} #(Σ s, α s) + lift.{max u' z} #(Σ s, σ.IdxFam s) ≤ max ℵ₀ (lift.{z} #(Σ s, α s)) := by
            refine hSum'.trans ?_
            -- max (max A B) ℵ₀ ≤ max ℵ₀ A using B ≤ ℵ₀
            have hB : lift.{max u' z} #(Σ s, σ.IdxFam s) ≤ ℵ₀ := hIdx
            have hA :  (lift.{z} #(Σ s, α s)) ≤ max ℵ₀  (lift.{z} #(Σ s, α s)) := le_max_right _ _
            have hA' : ℵ₀ ≤ max ℵ₀ (lift.{z} #(Σ s, α s)) := le_max_left _ _
            refine max_le_iff.2 ?_
            exact ⟨
              (max_le_iff.2 ⟨hA, hB.trans hA'⟩),
              hA'⟩
          simpa [hSigmaSum] using hSum''
        -- lift the bound
        simpa [Cardinal.lift_aleph0] using (Cardinal.lift_le.2 hVar')

      -- lift the bound into K
      have hVar : lift.{max (max (max u u') v) z} #(Σ s, α s ⊕ σ.IdxFam s) ≤ K := by
        refine (lift_le.{max (max (max u u') v) z}.mpr hVar0).trans ?_
        -- max ℵ₀ (lift #(Σ s, α s)) ≤ K
        have hA : lift.{max (max (max u u') v) z} #(Σ s, α s) ≤
            lift.{max (max (max u u') v) z} #(Σ s, α s) + (lift.{u'} L.card) := by
          -- compare lifts of the same cardinal, then use self_le_add_left
          have hA' :
              lift.{max (max (max u u') v) z} #(Σ s, α s) ≤
                lift.{max (max (max u u') v) z} #(Σ s, α s) := by
            -- lift to a common universe and use reflexivity
            simp only [mk_sigma, lift_sum, le_refl]
          exact hA'.trans (self_le_add_right (lift.{max (max (max u u') v) z} #(Σ s, α s)) (lift.{u'} L.card))
        have hA'': lift.{max (max (max u u') v) z} #(Σ s, α s) ≤ K := by
          simp only [K]
          apply le_trans hA
          apply le_trans _ (le_max_right ℵ₀ _ )
          rw[←lift_le.{max (max (max u u') v) z}]
          simp only [lift_add, lift_lift, add_assoc, mk_sigma, lift_sum, ge_iff_le, self_le_add_left]

        have hA' : max ℵ₀ (lift.{max (max (max u u') v) z} #(Σ s, α s)) ≤ K :=
          max_le_iff.2 ⟨(by simp [hK]), hA''⟩
        simpa using hA'

      -- Bound the function-symbol part by L.card.
      have hFun :
           lift.{max (max (max u u') v) z} #(Σ η s, L.Functions η s) ≤ K := by
        have hFun' : lift.{max (max (max u u') v) z} #(Σ η s, L.Functions η s) ≤ lift.{u'} L.card := by
          -- Inject functions into symbols.
          rw[card_eq_card_functions_add_card_relations]
          rw[lift_add,]
          simp only [←lift_sum]
          have : #((η : Signature Sorts) × (s : Sorts) × L.Functions η s) =
                (Cardinal.sum fun i ↦ Cardinal.sum fun i_1 ↦ #(L.Functions i i_1)) := by
              simp only [mk_sigma]
          rw[this]

          rw[←lift_le.{max (max (max u u') v) z}]
          rw[lift_add]
          simp only[lift_lift]
          simp only [self_le_add_right]

        have hFun'': lift.{max (max (max u u') v) z}  #(Σ η s, L.Functions η s) ≤
            (lift.{max (max (max u u') v) z}  #(Σ s, α s)) + (lift.{u'} L.card) := by
          apply hFun'.trans
          rw[←lift_le.{max (max (max u u') v) z}]
          rw[lift_add]
          simp only[lift_lift]
          simp only [self_le_add_left]
        unfold K
        apply le_max_of_le_right
        rw[←lift_le.{max (max (max u u') v) z}]

        rw[lift_add]
        simp only[lift_lift]
        apply le_trans hFun''
        rw[←lift_le.{max (max (max u u') v) z}] at *
        simp only [lift_add, lift_lift, add_assoc, mk_sigma, lift_sum, ge_iff_le, self_le_add_left]



      -- Now combine the bounds via Term.card_le.
      have hMax :
          max (lift.{max (max (max u u') v) z}  #(Σ s, α s ⊕ σ.IdxFam s))
              (lift.{max (max (max u u') v) z}  #(Σ η s, L.Functions η s)) ≤ K :=
        max_le_iff.2 ⟨hVar, hFun⟩
      have hMax' : max ℵ₀
            (max (lift.{max (max (max u u') v) z}  #(Σ s, α s ⊕ σ.IdxFam s))
                 (lift.{max (max (max u u') v) z}  #(Σ η s, L.Functions η s))) ≤ K :=
        max_le_iff.2 ⟨hK, hMax⟩

      let h:= (Term.card_le (L := L) (α := α ⊕ₛ σ.IdxFam) (Sorts := Sorts))
      rw[←lift_le.{max (max (max u u') v) z}]
      unfold f
      rw[mk_sigma]
      rw[mk_sigma]  at h
      rw[←lift_le.{max (max (max u u') v) z}] at h

      simp only [lift_lift] at *
      apply le_trans h
      simp only [lift_max] at *
      refine (max_le_iff.2 ?_ )
      rw[←lift_le.{max (max (max u u') v) z}] at hK
      simp only [lift_aleph0] at *
      refine ⟨hK, ?_⟩
      refine (max_le_iff.2 ?_ )
      rw[←lift_le.{max (max (max u u') v) z}] at *
      simp only [lift_lift] at *

      refine ⟨hVar, hFun⟩

    -- Conclude for the sum over σ.
    have hiSup : lift.{v} (_root_.iSup f) ≤  K := by
      rw[lift_iSup]

      refine ciSup_le (α:= Cardinal.{max (max (max u u') z) v}) ?_
      intro σ
      exact hFib σ
      use (Cardinal.sum f)
      intro a ha
      rcases ha with ⟨y, hy⟩
      rw[← hy]
      apply Cardinal.le_sum f

    have hMax : max ℵ₀ (lift.{v} ((lift.{max u u', z} #Sorts) + _root_.iSup f)) ≤ K := by
      refine max_le_iff.2 ⟨hK, ?_⟩
      simp only [lift_add, lift_lift]
      rw[←Cardinal.add_eq_left hK (le_refl K)]
      refine add_le_add ?_ ?_
      simp_all only [mk_sigma, lift_id, le_sup_iff]
      simp_all only [mk_sigma, lift_sum, le_sup_left, le_sup_iff, lift_le_aleph0, lift_id, ge_iff_le, K, f]

    -- Rewrite back from sum f.
    have hsum''' : lift.{v} #(Σ (σ : Signature Sorts), (Σ τ, L.Term (α ⊕ₛ σ.IdxFam) τ)) ≤
        lift.{v} (max ℵ₀ (lift.{max u u', z} #Sorts + _root_.iSup f)) := by
      rw[←hsum] at hsum''
      simpa only using (lift_le.2 hsum'')


    refine hsum'''.trans ?_

    simp_all only [mk_sigma, lift_id, le_sup_iff, lift_add, lift_lift, sup_le_iff, true_and,
      lift_sum, lift_max, lift_aleph0, and_self]

  -- Bound the relation/signature/opcode component
  have hRel : lift.{max u u'} #((Σ σ, L.Relations σ) ⊕ (Signature Sorts ⊕ Fin 2)) ≤ K := by
    have hRel''' : lift.{max (max (max u u') v) z} #(Σ σ, L.Relations σ) ≤ K := by
      have hFun' : lift.{max (max (max u u') v) z} #(Σ σ, L.Relations σ) ≤ lift.{u'} L.card := by
        rw [card_eq_card_functions_add_card_relations, lift_add, ← lift_sum, mk_sigma,
            ← lift_le.{max (max (max u u') v) z}, lift_add]
        simp only [lift_lift, self_le_add_left]
      have hRel'' : lift.{max (max (max u u') v) z} #(Σ σ, L.Relations σ) ≤
          (lift.{max (max (max u u') v) z} #(Σ s, α s)) + (lift.{u'} L.card) := by
        refine hFun'.trans ?_
        rw [← lift_le.{max (max (max u u') v) z}, lift_add]
        simp only [lift_lift, self_le_add_left]
      apply le_max_of_le_right
      rw [← lift_le.{max (max (max u u') v) z}, lift_add]; simp only [lift_lift]
      refine hRel''.trans ?_
      rw [← lift_le.{max (max (max u u') v) z}, lift_add, lift_add]
      simp only [lift_lift];
      rw[lift_add, add_assoc]
      simp only [lift_lift];
      simp_all only [mk_sigma, lift_sum, le_sup_left, le_sup_iff, lift_le_aleph0, ge_iff_le, self_le_add_left, K]

    have hFin : #(Fin 2) ≤ ℵ₀ := by
      simpa only [mk_fintype, Fintype.card_fin, Nat.cast_ofNat] using (natCast_lt_aleph0).le

    have hSigFin : #(Signature Sorts ⊕ Fin 2) = #(Signature Sorts) := by
      rw [mk_sum, add_eq_left (by simp_all), ]
      · simp only [lift_uzero]
      · simp_all only [mk_sigma, lift_sum, mk_fintype, Fintype.card_fin, Nat.cast_ofNat,
        card_of_signature, lift_uzero, lift_ofNat]
        simp only [le_sup_iff]
        left
        simpa only [mk_fintype, Fintype.card_fin, Nat.cast_ofNat] using (natCast_lt_aleph0).le

    rw [mk_sum, ← lift_le.{max (max (max u u') v) z}]
    simp only [lift_lift] at *; rw [lift_add]; simp only [lift_lift] at *
    rw [← lift_le.{max (max (max u u') v) z}] at hK; simp only [lift_aleph0] at hK
    rw[hSigFin]
    rw[ ←add_eq_left hK (le_refl _)]
    rw[lift_id]
    rw[card_of_signature] at *
    refine add_le_add ?_ ?_
    · simp_all only [mk_sigma, lift_sum, mk_fintype, Fintype.card_fin, Nat.cast_ofNat, mk_sum,
      lift_uzero, lift_ofNat, lift_id, ge_iff_le]
    · simp_all only [mk_sigma, lift_sum, mk_fintype, Fintype.card_fin, Nat.cast_ofNat, mk_sum,
      lift_uzero, lift_ofNat, lift_id, ge_iff_le]
      rw[←lift_le.{max (max (max u u') v) z}, lift_lift] at hSorts
      simp_all only [lift_id, ge_iff_le, lift_max, lift_aleph0, sup_le_iff, true_and]

  -- Combine the two main components: need to lift to the same universe as K
  rw [← lift_le.{max (max (max u u') v) z}]
  rw [lift_add]
  simp only [lift_lift]
  rw [← lift_le.{max (max (max u u') v) z}] at *
  simp only [lift_aleph0] at hK
  simp only [lift_lift] at *
  rw [lift_add]
  simp only [lift_lift] at *
  refine (add_le_add hTerm hRel).trans ?_

  have : K + K = K := by
    apply Cardinal.add_eq_left
    · simp_all only [lift_id, ge_iff_le, mk_sigma, lift_sum, mk_sum, lift_uzero, mk_fintype,
      Fintype.card_fin, Nat.cast_ofNat, lift_ofNat, lift_add, lift_lift]
    · simp only [ge_iff_le, le_refl]

  simp_all only [lift_id, ge_iff_le, mk_sigma, lift_sum, mk_sum, lift_uzero, mk_fintype,
    Fintype.card_fin, Nat.cast_ofNat, lift_ofNat, lift_add, lift_lift]

  simp


/-- Signatures over a countable type are countable. -/
instance countableSignature {S : Type*} [Countable S] : Countable (Signature S) := by
  haveI : Countable (Fin 3 ⊕ S) := inferInstance
  haveI : Countable (List (Fin 3 ⊕ S)) := inferInstance
  exact Function.Injective.countable Signature.encode_injective

/-- Terms with varying bound variable contexts form a countable type
    when the base types are countable. -/
private instance countableTermSigma
    [Countable Sorts]
    [Countable (Σ s, α s)]
    [DecidableEq Sorts]
    [Countable (Σ η s, L.Functions η s)] :
    Countable (Σ (σ τ : Signature Sorts), L.Term (α ⊕ₛ σ.IdxFam) τ) := by
  -- For each σ, the bound variable indices are finite, hence countable
  haveI (σ : Signature Sorts) : Countable (Σ s, σ.IdxFam s) := inferInstance
  -- (Σ s, α s ⊕ σ.IdxFam s) injects into (Σ s, α s) ⊕ (Σ s, σ.IdxFam s), which is countable
  haveI (σ : Signature Sorts) : Countable (Σ s, α s ⊕ σ.IdxFam s) := by
    apply Function.Injective.countable
      (f := fun ⟨s, x⟩ => match x with
        | Sum.inl a => Sum.inl (⟨s, a⟩ : Σ s, α s)
        | Sum.inr v => Sum.inr (⟨s, v⟩ : Σ s, σ.IdxFam s))
    intro ⟨s₁, x₁⟩ ⟨s₂, x₂⟩ h
    cases x₁ <;> cases x₂ <;> simp_all only [reduceCtorEq, Sum.inl.injEq, Sigma.mk.injEq, true_and]
    all_goals (obtain ⟨rfl, h⟩ := h; simp_all only [heq_eq_eq, and_self])
  -- Combined variable type is countable (same as above, just different notation)
  haveI (σ : Signature Sorts) : Countable (Σ s, (α ⊕ₛ σ.IdxFam) s) := this σ
  -- Code type for terms is countable
  haveI (σ : Signature Sorts) : Countable (MSLanguage.TCode L (α ⊕ₛ σ.IdxFam)) := inferInstance
  -- Signature over code is countable
  haveI (σ : Signature Sorts) : Countable (Signature (MSLanguage.TCode L (α ⊕ₛ σ.IdxFam))) :=
    countableSignature
  -- Terms are countable via TreeEncode
  haveI (σ : Signature Sorts) : Countable (Σ τ, L.Term (α ⊕ₛ σ.IdxFam) τ) := by
    apply Function.Injective.countable (f := MSLanguage.Term.TreeEncode)
    intro t₁ t₂ h
    have := congrArg (MSLanguage.Term.TreeDecode (L := L) (α := α ⊕ₛ σ.IdxFam)) h
    simp only [MSLanguage.Term.TreeDecode_TreeEncode] at this
    exact Option.some.inj this
  -- Sigma over (Signature Sorts) and (Σ τ, Term) - both countable
  exact Countable.of_equiv
    (Σ σ : Signature Sorts, Σ τ : Signature Sorts, L.Term (α ⊕ₛ σ.IdxFam) τ)
    (by rfl)

instance countable
    [Countable Sorts]
    [Countable (Σ s, α s)]
    [Countable (Σ η s, L.Functions η s)]
    [Countable (Σ σ, L.Relations σ)]
    [DecidableEq Sorts] :
    Countable (Σ σ, L.BoundedFormula α σ) := by
  -- BFCode components are countable
  haveI : Countable (Σ (σ τ : Signature Sorts), L.Term (α ⊕ₛ σ.IdxFam) τ) := countableTermSigma
  haveI : Countable ((Σ σ, L.Relations σ) ⊕ (Signature Sorts ⊕ Fin 2)) := inferInstance
  -- BFCode is countable
  haveI : Countable (L.BFCode α) := inferInstance
  -- Signature over BFCode is countable
  haveI : Countable (Signature (L.BFCode α)) := countableSignature
  -- Transfer via injective TreeEncode
  exact Function.Injective.countable TreeEncode_injective

/-- BFCode cardinality equals ℵ₀ when the language and variables are countable. -/
theorem BFCode_card_countable [Countable Sorts] [Countable (Σ s, α s)]
    [Countable (Σ η s, L.Functions η s)] [Countable (Σ σ, L.Relations σ)] [DecidableEq Sorts] :
    #(L.BFCode α) = ℵ₀ := by
  apply le_antisymm
  · -- Upper bound: BFCode is countable
    haveI : Countable (Σ (σ τ : Signature Sorts), L.Term (α ⊕ₛ σ.IdxFam) τ) := countableTermSigma
    haveI : Countable ((Σ σ, L.Relations σ) ⊕ (Signature Sorts ⊕ Fin 2)) := inferInstance
    haveI : Countable (L.BFCode α) := inferInstance
    exact mk_le_aleph0
  · -- Lower bound: contains Signature Sorts which is infinite
    exact aleph0_le_BFCode_card

end BoundedFormula
end boundedformula_encoding

end MSLanguage
end MSFirstOrder
