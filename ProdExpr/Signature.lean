import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic
import ProdExpr.Fam
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

universe u v

namespace MSFirstOrder
open Fam
/--
Non-associative product expressions as recommended by Adam Topaz in zulip chat:
-/
inductive Signature (S : Type u) where
  | nil  : Signature S
  | of   : S → Signature S
  | prod : Signature S → Signature S → Signature S
deriving Repr, DecidableEq

infixl:70 " ⨯ " => Signature.prod

/-- Notation for single-sort signatures: `⦃s⦄` means `Signature.of s`. -/
notation "⦃" s "⦄" => Signature.of s

/-- Notation for the empty/nil signature: `⦃⦄` means `⦃⦄`. -/
notation "⦃⦄" => Signature.nil

@[reducible]
instance instSigZero {S} : Zero (Signature S) :=
  {zero := ⦃⦄}

/-- Mapping suggested by Adam Topaz: -/
@[reducible]
def Signature.Interpret {S : Type u} (X : Fam.{v} S) : Signature S → Type v
  | 0         => PUnit
  | .of s     => X s
  | prod a b  => Interpret X a × Interpret X b

/-
--TODO?
instance : Coe S (Signature S) where
  coe := Signature.of
-/

/--
Notation for Signature.Interpret.
`M[[^]]σ = Signature.Interpret M σ`
-/
notation:80 X " [^] " σ:81 => MSFirstOrder.Signature.Interpret X σ

/-
@[reducible]
instance instInterpretHPow {S : Type u} : HPow (S → Type v) (Signature S) (Type v) :=
  {hPow := Signature.Interpret}
-/

lemma Signature.Interpret.hpow_eq {S : Type u} {σ : Signature S}
    {X : Fam.{v} S} : σ.Interpret X = X [^] σ := rfl

@[reducible]
instance nilExpInhabited {S : Type u} {X : Fam.{v} S} : Inhabited (X[^]⦃⦄) :=
  by
    rw [←Signature.Interpret.hpow_eq, Signature.Interpret]
    apply inferInstance

namespace Signature

/--
The underlying inductive for `IdxFam`. For each `σ : Signature S` and `s : S`,
`Idx σ s` is the type of `s`-typed variable positions in `σ`.
Use `σ.IdxFam : Fam S` for the `Fam`-wrapped version.
-/
inductive Idx {S : Type u} : Signature S → S → Type u where
  | var {s : S} : Idx ⦃s⦄ s
  | left {σ τ : Signature S} {s : S} (v : Idx σ s) : Idx (σ ⨯ τ) s
  | right {σ τ : Signature S} {s : S} (v : Idx τ s) : Idx (σ ⨯ τ) s
deriving Repr

/--
For each `σ : Signature S`, `σ.IdxFam : Fam S` is the family of `s`-typed variable positions in `σ`.
This is the `Fam`-wrapped version of the inductive `Idx`.
-/
abbrev IdxFam {S : Type u} (σ : Signature S) : Fam.{u} S := ⟨Idx σ⟩

variable {S : Type u}

instance instIdxEmpty : ∀ s, IsEmpty (Idx (S:= S) ⦃⦄ s) := by
  intro s
  constructor
  intro a
  cases a

instance instIdxFamEmpty : ∀ s, IsEmpty (IdxFam (S:= S) ⦃⦄ s) := by
  intro s
  constructor
  intro a
  cases a

/-- Helper simp: injectivity of `Idx.left` under sigma packaging. -/
@[simp] lemma Idx.left_injEq {σ τ : Signature S} {s : S}
    {v w : σ.Idx s} : ((v.left : (σ ⨯ τ).Idx s) = w.left ) ↔ (v = w)
    := by
    simp_all only [Idx.left.injEq]

/-- Helper simp: injectivity of `Idx.right` under sigma packaging. -/
@[simp] lemma Idx.right_injEq {σ τ : Signature S} {s : S}
    {v w : σ.Idx s} : ((v.right : (τ ⨯ σ).Idx s) = w.right ) ↔ (v = w)
  := by
  simp_all only [Idx.right.injEq]

@[simp] lemma Idx.left_ne_right {σ τ : Signature S} {s : S}
    (v : σ.IdxFam s) (w : τ.IdxFam s) :
    Idx.left v ≠ Idx.right w := by
  intro h; cases h

@[simp] lemma Idx.right_ne_left {σ τ : Signature S} {s : S}
    (v : τ.IdxFam s) (w : σ.IdxFam s) :
    Idx.right v ≠ Idx.left w := by
  intro h; cases h

section defs

def length : Signature S → ℕ
  | .nil => 0
  | .of _     => 1
  | .prod a b  => a.length + b.length

@[simp] lemma length_nil : (⦃⦄ : Signature S).length = 0 := by rfl

@[simp] lemma length_of (s : S) : ⦃s⦄.length = 1 := by rfl

@[simp] lemma length_prod (σ τ : Signature S) :
  (σ ⨯ τ).length = σ.length + τ.length := by rfl

/-- `IdxFam` for a product splits as a sum of `IdxFam` for the factors. -/
def IdxFam_as_prod (σ τ : Signature S) :
    (σ ⨯ τ).IdxFam ≃ₛ σ.IdxFam ⊕ₛ τ.IdxFam :=
{ toFun := ⟨fun s v =>
    match v with
    | Signature.Idx.left  vσ => Sum.inl vσ
    | Signature.Idx.right vτ => Sum.inr vτ⟩
  , invFun := ⟨fun s v =>
    match v with
    | Sum.inl vσ => Signature.Idx.left vσ
    | Sum.inr vτ => Signature.Idx.right vτ⟩
  , left_inv' := by
      intro s v
      cases v with
      | left vσ  => rfl
      | right vτ => rfl
  , right_inv' := by
      intro s v
      cases v with
      | inl vσ => rfl
      | inr vτ => rfl }

end defs

section to_list

/-- Flatten a `Signature` to a list of sorts. -/
def toList : Signature S → List S
  | .nil       => []
  | .of s      => [s]
  | .prod a b  => a.toList ++ b.toList

/--
Given acc, and an input list L we want to insert L into acc
so that acc comes before L and the resulting item is normalized.
This is done by injesting head to tail, taking each head s and inserting
it as the left factor.
-/
def fromListAux (acc : Signature S) : List S → Signature S
  | []      => acc
  | s :: L  =>
      let acc' :=
        match acc with
        | .nil   => .of s --If accumulating on nil, just replace with ⦃s⦄
        | acc    => acc ⨯ ⦃s⦄ --Otherwise we make ⦃s⦄ the new left product
      fromListAux acc' L

/-- Fold a list of `S` into a left-associated `Signature S`. -/
def fromList (L : List S) : Signature S :=
  fromListAux ⦃⦄ L

lemma toList_fromListAux (acc : Signature S) (l : List S) :
    (fromListAux acc l).toList = acc.toList ++ l := by
  induction l generalizing acc with
  | nil =>
      simp only [fromListAux, List.append_nil]
  | cons s l ih =>
      simp_all only [fromListAux]
      cases acc <;> simp only [toList, List.append_assoc, List.cons_append, List.nil_append]

lemma toList_fromList (l : List S) :
    (fromList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [fromList, toList_fromListAux]; rfl

lemma toList_length (a : Signature S) : a.length = a.toList.length := by
  induction a with
  | of => simp only [length, toList, List.length_cons, List.length_nil, zero_add]
  | prod _ _ ih₁ ih₂ => simp only [length, ih₁, ih₂, toList, List.length_append]
  | nil => simp only [length, toList, List.length_nil]

lemma fromList_length {l : List S} : (fromList l).length = l.length := by
  simp only [toList_length, toList_fromList]

end to_list

section equivalences
/- This section defines the equivalence relation on `Signature S` expressing when
`σ` and `τ` are equivalent up to associativity. It also defines a canonical normalized
representative for each class which trims out all `nil` factors from products and
associates to the right.
-/

/--
Inductive type indexing the basic generating types of associative product equivalences
-/
inductive PEquiv : Signature S → Signature S → Type u where
  | refl  {σ} :
      PEquiv σ σ
  | symm  {σ₁ σ₂} :
      PEquiv σ₁ σ₂ → PEquiv σ₂ σ₁
  | trans {σ₁ σ₂ σ₃} :
      PEquiv σ₁ σ₂ → PEquiv σ₂ σ₃ → PEquiv σ₁ σ₃
  | assocL (a b c) :
      PEquiv (.prod (.prod a b) c) (.prod a (.prod b c))
  | assocR (a b c) :
      PEquiv (.prod a (.prod b c)) (.prod (.prod a b) c)
  | nil_left  (a) :
      PEquiv (.prod .nil a) a
  | nil_right (a) :
      PEquiv (.prod a .nil) a
  | prod_congr_left  {a a' b} :
      PEquiv a a' → PEquiv (.prod a b) (.prod a' b)
  | prod_congr_right {a b b'} :
      PEquiv b b' → PEquiv (.prod a b) (.prod a b')

def PEquiv.prod_congr {a a' b b' : Signature S}
    (h₁ : PEquiv a a') (h₂ : PEquiv b b') :
    PEquiv (.prod a b) (.prod a' b') :=
  PEquiv.trans (PEquiv.prod_congr_left h₁) (PEquiv.prod_congr_right h₂)

open PEquiv

/--
Constructs a PEquiv on an intermediate state of the fromList construction:
-/
def PEquiv_fromListAux (acc : Signature S) (l : List S) :
  PEquiv (.prod acc (fromList l)) (fromListAux acc l) := by
  induction l generalizing acc with
  | nil =>
      rw [fromList, fromListAux, fromListAux]
      exact PEquiv.nil_right acc
  | cons s l ih =>
      cases acc with
      | nil => rw [fromList, fromListAux]; apply PEquiv.nil_left
      | of t =>
          rw [fromList, fromListAux, fromListAux]
          · apply PEquiv.trans _ (ih (⦃t⦄ ⨯ ⦃s⦄))
            let h := PEquiv.assocR (S := S) ⦃t⦄ ⦃s⦄ (nil.fromListAux l)
            apply PEquiv.trans _ h
            apply PEquiv.prod_congr_right
            apply PEquiv.trans _ (ih ⦃s⦄).symm
            exact PEquiv.refl
          · simp only [reduceCtorEq, imp_self]
      | prod a b =>
          rw [fromList, fromListAux]
          have h1 : PEquiv (⦃s⦄ ⨯ fromList l) (fromListAux ⦃s⦄ l) :=
            ih ⦃s⦄
          have h2 := ih ((a ⨯ b) ⨯ ⦃s⦄)
          have h1' := PEquiv.symm h1
          have h_left :
            PEquiv ((a ⨯ b) ⨯ fromListAux ⦃s⦄ l)
                    ((a ⨯ b) ⨯ (⦃s⦄ ⨯ fromList l)) :=
            PEquiv.prod_congr_right h1'
          have h_assoc := PEquiv.assocR (a ⨯ b) ⦃s⦄ (fromList l)
          exact PEquiv.trans h_left (PEquiv.trans h_assoc h2)

lemma fromListAux_append (acc : Signature S) (l₁ l₂ : List S) :
  fromListAux acc (l₁ ++ l₂) =
    fromListAux (fromListAux acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil =>
      simp only [List.nil_append, fromListAux]
  | cons s l ih =>
      cases acc with
      | nil =>
          simp only [List.cons_append, fromListAux, ih]
      | of t =>
          simp only [List.cons_append, fromListAux, ih]
      | prod a b =>
          simp only [List.cons_append, fromListAux, ih]

lemma fromList_append_eq_fromListAux (l₁ l₂ : List S) :
  fromList (l₁ ++ l₂) = fromListAux (fromList l₁) l₂ := by
  unfold fromList
  simpa only using fromListAux_append (acc := ⦃⦄) (l₁ := l₁) (l₂ := l₂)

/--
Helper for showing that `σ ≃ fromList (toList σ)`
-/
def fromList_app (l₁ l₂ : List S) :
  PEquiv (.prod (fromList l₁) (fromList l₂)) (fromList (l₁ ++ l₂)) := by
  have h_eq : fromList (l₁ ++ l₂) = fromListAux (fromList l₁) l₂ :=
    fromList_append_eq_fromListAux (S := S) l₁ l₂
  have h :=
    PEquiv_fromListAux (S := S) (acc := fromList l₁) (l := l₂)
  simpa only [h_eq] using h

/--
The PEquiv witnessing the equivalence between `σ` and `(fromList (toList σ))`
-/
def equivToFromList : (σ : Signature S) → PEquiv σ (fromList (toList σ))
  | .nil =>
      PEquiv.refl
  | .of a => by
    rw [fromList, toList, fromListAux]
    exact PEquiv.refl
  | .prod a b => by
      let ha := equivToFromList a
      let hb := equivToFromList b
      let h₁ : PEquiv (.prod a b)
                       (.prod (fromList (toList a)) b) :=
        PEquiv.prod_congr_left ha
      let h₂ : PEquiv (.prod (fromList (toList a)) b)
                       (.prod (fromList (toList a)) (fromList (toList b))) :=
        PEquiv.prod_congr_right hb
      let h₃ : PEquiv (.prod (fromList (toList a)) (fromList (toList b)))
                       (fromList (toList a ++ toList b)) :=
        fromList_app (toList a) (toList b)
      unfold toList
      exact PEquiv.trans (PEquiv.trans h₁ h₂) h₃

end equivalences

section normalization

def leftAppend {S} : Signature S → Signature S → Signature S
  | acc, .nil        => acc ⨯ ⦃⦄
  | acc, .of s       => acc ⨯ ⦃s⦄
  | acc, .prod σ τ   =>
      let acc' := leftAppend acc σ
      leftAppend acc' τ

/-- Left-associate a `Signature` without trimming `nil`s. -/
def leftAssoc : Signature S → Signature S
  | .nil      => .nil
  | .of s     => ⦃s⦄
  | .prod σ τ => leftAppend (leftAssoc σ) τ

def trimNil : Signature S → Signature S
  | .nil      => .nil
  | .of s     => ⦃s⦄
  | .prod σ τ =>
      match trimNil σ, trimNil τ with
      | .nil, .nil => .nil
      | .nil, τ'   => τ'
      | σ',  .nil  => σ'
      | σ',  τ'    => .prod σ' τ'

lemma toList_leftAppend (acc σ : Signature S) :
  (leftAppend acc σ).toList = acc.toList ++ σ.toList := by
  induction σ generalizing acc with
  | nil =>
      simp only [leftAppend, toList, List.append_nil]
  | of s =>
      simp only [leftAppend, toList]
  | prod σ τ ihσ ihτ =>
      simp only [leftAppend, ihτ, ihσ, List.append_assoc, toList]

lemma toList_leftAssoc (σ : Signature S) :
  (leftAssoc σ).toList = σ.toList := by
  induction σ with
  | nil =>
      simp only [leftAssoc, toList]
  | of s =>
      simp only [leftAssoc, toList]
  | prod σ τ ihσ ihτ =>
      simp only [leftAssoc, toList_leftAppend, ihσ, toList]

def normalize (σ : Signature S) : Signature S := trimNil (leftAssoc σ)

/-- The normalization bundled with a proof of equivalence -/
@[simp]
def normalize_list (σ : Signature S) : Σ σ' : Signature S, PEquiv σ σ' :=
  ⟨fromList (toList σ), equivToFromList σ⟩

variable {S : Type u}

lemma trimNil_prod_of (acc : Signature S) (s : S) :
    trimNil (acc ⨯ ⦃s⦄) = match trimNil acc with
      | .nil => ⦃s⦄
      | a => a ⨯ ⦃s⦄ := by
  rw[trimNil]
  split <;> simp_all only [trimNil, reduceCtorEq, implies_true]

lemma fromListAux_eq_trimNil_leftAppend (acc : Signature S) (σ : Signature S) :
    fromListAux (trimNil acc) (toList σ) = trimNil (leftAppend acc σ) := by
  induction σ generalizing acc with
  | nil =>
      simp only [toList, fromListAux, leftAppend, trimNil]
      split <;> simp_all only [implies_true, imp_false, not_true_eq_false]
  | of s =>
      simp only [toList, fromListAux, leftAppend, trimNil_prod_of]
  | prod x y ihx ihy =>
      rw [toList, leftAppend, fromListAux_append]
      simp_all only

lemma normalize_unique (σ : Signature S) : normalize σ = (fromList (toList σ)) := by
  unfold normalize
  induction σ with
  | nil =>
      rfl
  | of s =>
      rfl
  | prod x y ih_x ih_y =>
      simp only [fromList, toList]
      rw [fromListAux_append]
      have h_fold_x : trimNil (leftAssoc x) = fromListAux ⦃⦄ (toList x) := ih_x
      rw [←h_fold_x]
      rw [fromListAux_eq_trimNil_leftAppend (leftAssoc x) y]
      rfl

open Equiv

def interpretEquiv (X : Fam.{v} S) :
    {σ₁ σ₂ : Signature S} → PEquiv σ₁ σ₂ → Interpret X σ₁ ≃ Interpret X σ₂
  | _, _, .refl      => Equiv.refl _
  | _, _, .symm h    => (interpretEquiv X h).symm
  | _, _, .trans h₁ h₂ =>
      (interpretEquiv X h₁).trans (interpretEquiv X h₂)
  | _, _, .assocL _ _ _ =>
      prodAssoc _ _ _
  | _, _, .assocR _ _ _ =>
      (prodAssoc _ _ _).symm
  | _, _, .nil_left _ =>
      punitProd _
  | _, _, .nil_right _ =>
      prodPUnit _
  | _, _, .prod_congr_left h =>
      prodCongrLeft (fun _ => (interpretEquiv X h))
  | _, _, .prod_congr_right h =>
      prodCongrRight (fun _ => (interpretEquiv X h))

def interpretToInterpretNormalizedEquiv (X : Fam.{v} S) (σ : Signature S) :
    σ.Interpret X ≃ (normalize σ).Interpret X := by
    rw [normalize_unique]
    exact interpretEquiv _ (equivToFromList σ)

end normalization

section finite_family_conversion
/-! ## Finite Family to Signature Conversion

This section provides machinery to convert a finite family `X : Fam S`
into a `Signature S` with an equivalence. Used in Syntax.lean for
quantification over finite families (iAlls, iExs, iExsUnique).

### Algorithm
1. Use classical choice to get `Sigma X ≃ Fin n`
2. Build a list of sorts by enumerating `Fin n`
3. Convert to `Signature` via `fromList`
4. Build sort-respecting equivalence `X ≃ₛ σ.IdxFam`

### Public API
- `getIdxFam`: Get i-th variable with sort info
- `getIdxFam_fst`: Relates to `toList`
- `Idx.toFin`: Inverse direction
- `FinIndSigEquiv`: Explicit bijection
- `famToSignature`: Main construction (noncomputable)
-/

variable {σ : Signature S}
open Idx
private lemma nat_lt_lemma {n m k : ℕ} (hink : m < n + k) (hni : n ≤ m) : m - n < k := by
   have h := Nat.sub_lt_sub_right (a := m) (c:= n) (b := n + k)
   simp_all only [add_tsub_cancel_left, forall_const]

/-- Left injection for product indices -/
private def injLeft (σ τ : Signature S) (i : Fin σ.length) :
    Fin (σ ⨯ τ).length :=
  ⟨i,
    by
      -- `i < σ.length ≤ σ.length + τ.length`
      have hi : (i : Nat) < σ.length := i.is_lt
      exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)⟩

lemma injLeft_Injective {σ τ : Signature S} :
  Function.Injective (injLeft σ τ) := by
  intro v w h
  cases v ;cases w ; simp_all only [Fin.mk.injEq, injLeft]

/-- Right injection for product indices -/
private def injRight (σ τ : Signature S) (j : Fin τ.length) :
    Fin (σ ⨯ τ).length :=
  ⟨σ.length + j,
    by
      have hj : (j : Nat) < τ.length := j.is_lt
      have : σ.length + (j : Nat) < σ.length + τ.length :=
        Nat.add_lt_add_left hj σ.length
      simp only [length, add_lt_add_iff_left, Fin.is_lt]⟩

lemma injRight_Injective {σ τ : Signature S} :
  Function.Injective (injRight σ τ) := by
  intro v w h
  cases v ; cases w ; simp_all only [injRight, Fin.mk.injEq, Nat.add_left_cancel_iff]

/-- List out the associated variables to a given σ -/
def IdxFamList : (σ : Signature S) → List (Sigma σ.IdxFam)
  | nil => []
  | of s => [⟨s, Idx.var⟩]
  | prod σ τ => σ.IdxFamList.map (fun ⟨s, v⟩ => ⟨s, Idx.left v⟩) ++
                τ.IdxFamList.map (fun ⟨s, v⟩ => ⟨s, Idx.right v⟩)

@[simp]
lemma IdxFamList_length : (IdxFamList σ).length = σ.length := by
  induction σ
  case nil => simp only [IdxFamList, List.length_nil, length_nil]
  case of => simp only [IdxFamList, List.length_cons, List.length_nil, zero_add, length_of]
  case prod => simp_all only [IdxFamList, List.length_append, List.length_map]; rfl

lemma IdxFamList_map_fst (σ : Signature S) :
  (σ.IdxFamList.map (fun p => p.1)) = σ.toList := by
  induction σ with
  | nil =>
      simp only [IdxFamList, List.map_nil, toList]
  | of s =>
      simp only [IdxFamList, List.map_cons, List.map_nil, toList]
  | prod σ τ ihσ ihτ =>
      have hσ : σ.IdxFamList.map
        ((fun p : Sigma (σ ⨯ τ).IdxFam ↦ p.fst) ∘ fun x ↦ ⟨x.fst, x.snd.left⟩) = σ.toList
        := by exact ihσ
      have hτ : τ.IdxFamList.map
        ((fun p : Sigma (σ ⨯ τ).IdxFam ↦ p.fst) ∘ fun x ↦ ⟨x.fst, x.snd.right⟩) = τ.toList
        := by exact ihτ
      rw [toList, ←hσ, ←hτ]
      simp only [IdxFamList, List.map_append, List.map_map]

def getIdxFam (σ : Signature S) : Fin σ.length → Sigma σ.IdxFam :=
  fun i => σ.IdxFamList.get (Fin.cast IdxFamList_length.symm i)

@[simp] private lemma getIdxFam_prod_left
  {σ τ : Signature S} (i : Fin (σ ⨯ τ).length) (h : (i : Nat) < σ.length) :
  getIdxFam (σ ⨯ τ) i
    =
    ⟨(getIdxFam σ ⟨(i : Nat), h⟩).1,
      Signature.Idx.left (getIdxFam σ ⟨(i : Nat), h⟩).2⟩ := by
  let j : Fin σ.length := ⟨(i : Nat), h⟩
  have hij : σ.injLeft τ j = i := by
    ext; rfl
  simp_all only [getIdxFam, IdxFamList, List.get_eq_getElem, Fin.val_cast, List.length_map,
    IdxFamList_length, List.getElem_append_left, List.getElem_map, Fin.cast_mk]


@[simp] private lemma getIdxFam_prod_right
  {σ τ : Signature S} (i : Fin (σ ⨯ τ).length) (h : σ.length ≤ (i : Nat)) :
  getIdxFam (σ ⨯ τ) i
    =
    ⟨(getIdxFam τ
        ⟨(i : Nat) - σ.length,
          nat_lt_lemma (n := σ.length) (m := (i : Nat)) (k := τ.length) i.is_lt h⟩).1,
      Signature.Idx.right
        (getIdxFam τ
          ⟨(i : Nat) - σ.length,
            nat_lt_lemma (n := σ.length) (m := (i : Nat)) (k := τ.length) i.is_lt h⟩).2⟩ := by
  let k : Fin τ.length :=
    ⟨(i : Nat) - σ.length,
      nat_lt_lemma (n := σ.length) (m := (i : Nat)) (k := τ.length) i.is_lt h⟩
  have hik : Signature.injRight σ τ k = i := by
    ext
    simp only [injRight, Nat.add_sub_of_le h, Fin.eta, k]
  simp_all only [getIdxFam, IdxFamList, List.get_eq_getElem, Fin.val_cast, List.length_map,
    IdxFamList_length, List.getElem_append_right, List.getElem_map, Fin.cast_mk]


def Idx.toFin : ∀ {σ : Signature S} {s : S}, σ.IdxFam s → Fin σ.length
  | .of _, _, .var      => ⟨0, by simp only [length, zero_lt_one]⟩
  | .prod σ τ, _, .left v  => Signature.injLeft  σ τ (Idx.toFin v)
  | .prod σ τ, _, .right v => Signature.injRight σ τ (Idx.toFin v)

def Idx.toFin_inj {σ : Signature S} {s : S} :
    Function.Injective (toFin (σ := σ) (s := s)) := by
  intro v w h
  induction σ with
  | nil => cases v
  | of s => cases v; cases w; simp only
  | prod η τ ihη ihτ =>
    cases v
    case left v' =>
      cases w
      case left w' =>
        rw [left.injEq]
        apply ihη
        simp_all only [toFin]
        exact injLeft_Injective h
      case right w' =>
        simp_all only [toFin, injLeft, injRight, Fin.mk.injEq, reduceCtorEq]
        let hv' := v'.toFin.2
        let hw' := w'.toFin.2
        linarith
    case right v' =>
      cases w
      case left w' =>
        simp_all only [toFin, injRight, injLeft, Fin.mk.injEq, reduceCtorEq]
        let hv' := v'.toFin.2
        let hw' := w'.toFin.2
        linarith
      case right w' =>
        rw [right.injEq]
        apply ihτ
        simp_all only [toFin]
        exact injRight_Injective h

/-- Inverse direction: `Σ s, σ.IdxFam s → Fin σ.length`. -/
private def getIdxFamInv (σ : Signature S) : Sigma σ.IdxFam → Fin σ.length
  | ⟨_, v⟩ => Idx.toFin v

@[simp] private lemma getIdxFam_toFin {σ : Signature S} {s : S} (v : σ.IdxFam s) :
  getIdxFam σ (Idx.toFin v) = ⟨s, v⟩ := by
  induction σ with
  | nil => cases v
  | of s =>
    cases v
    case of =>
      simp only [getIdxFam, IdxFamList, List.length_cons, List.length_nil, Nat.reduceAdd,
        List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero]
  | prod σ τ ih₁ ih₂ =>
    cases v
    case left w =>
      simp only [getIdxFam, IdxFamList, Idx.toFin, injLeft, Fin.cast_mk, List.get_eq_getElem,
        List.length_map, IdxFamList_length, Fin.is_lt, List.getElem_append_left, List.getElem_map,
        Sigma.mk.injEq]
      have h₁ := ih₁ w
      simp only [getIdxFam, List.get_eq_getElem, Fin.val_cast] at h₁
      rw [h₁]
      simp only [heq_eq_eq, and_self]
    case right w =>
      have h₂ := ih₂ w
      simp only [getIdxFam, IdxFamList, Idx.toFin, injRight, Fin.cast_mk, List.get_eq_getElem,
        List.length_map, IdxFamList_length, le_add_iff_nonneg_right, zero_le,
        List.getElem_append_right, add_tsub_cancel_left, List.getElem_map, Sigma.mk.injEq]
      simp only [getIdxFam, List.get_eq_getElem, Fin.val_cast] at h₂
      apply And.intro
      · simp_all only
      · rw [h₂]


@[simp] private lemma getIdxFamInv_getIdxFam {σ : Signature S} (i : Fin σ.length) :
  σ.getIdxFamInv (getIdxFam σ i) = i := by
  induction σ with
  | nil =>
    cases i
    case mk j h =>
      rw [Signature.length] at h
      simp_all only [not_lt_zero']
  | of s => ext; simp_all only [Fin.val_eq_zero]
  | prod σ τ ih₁ ih₂ =>
    by_cases h : ↑i < σ.length
    case pos =>
      have h₁ := ih₁ ⟨↑i, h⟩
      rw[getIdxFam_prod_left i h]
      rw[getIdxFamInv, Idx.toFin] at *
      rw[h₁, injLeft]
    case neg =>
      let j := ↑i - σ.length
      have hi : ↑i < σ.length + τ.length := by
          rcases i with ⟨i, hi⟩
          simp_all only [not_lt]
          exact hi
      have hj : j < τ.length := by
        change ↑i - σ.length <  τ.length
        rw[not_lt] at h
        exact nat_lt_lemma hi h
      have h₂ := ih₂ ⟨j, hj⟩
      rw[getIdxFam_prod_right i (by simp_all only [not_lt, j]) ]
      unfold j at *
      rw[getIdxFamInv, Idx.toFin] at *
      rw[h₂, injRight]
      rcases i with ⟨i', hi'⟩
      have hh : σ.length + (i' - σ.length) = i' := by
        simp_all only [not_lt, add_tsub_cancel_of_le]
      simp_all only

/-- Explicit equivalence between `Fin σ.length` and `Sigma (σ.IdxFam)` -/
def FinIndSigEquiv (σ : Signature S) : Fin σ.length ≃ Sigma (σ.IdxFam) :=
{ toFun    := getIdxFam σ
  invFun   := getIdxFamInv (σ := σ)
  left_inv := by
    intro i; simp only [getIdxFamInv_getIdxFam]
  right_inv := by
    intro x
    rcases x with ⟨s, v⟩
    simp only [getIdxFamInv, getIdxFam_toFin v]
}

instance instSigmaSigFintype {σ : Signature S} : Fintype (Sigma (σ.IdxFam)) :=
  Fintype.ofEquiv (Fin σ.length) (FinIndSigEquiv (σ := σ))

-- σ.IdxFam s is fintype, since it injects into the finite sigma type
noncomputable instance instSigAtSortFintype {σ : Signature S} {s : S} : Fintype (σ.IdxFam s) :=
  Fintype.ofInjective
    (fun v : σ.IdxFam s => (⟨s, v⟩ : Sigma (σ.IdxFam)))
    (fun _ _ h => by cases h; rfl)

lemma getIdxFam_fst (σ : Signature S) (i : Fin σ.length) :
  (getIdxFam σ i).1 = σ.toList.get (Fin.cast (toList_length σ) i) := by
  simp only [List.get_eq_getElem, ← IdxFamList_map_fst σ,  List.getElem_map]
  rfl

private lemma cast_fin_app {σ : Signature S} {T : Type*} {n : Nat}
    (h : σ.length = n) (g : Fin σ.length → T) (i : Fin n) :
    (h ▸ g) i = g (Fin.cast h.symm i) := by
  cases h
  rfl

@[simp]
private lemma cast_getIdxFam {σ : Signature S} {n : Nat}
    (h : σ.length = n) (i : Fin n) :
    (h ▸ σ.getIdxFam) i = σ.getIdxFam (Fin.cast h.symm i) := by
  cases h
  rfl

@[simp]
lemma cast_FinIndSigEquiv_apply {σ : Signature S} {n : Nat}
    (h : σ.length = n) (i : Fin n) :
    (h ▸ FinIndSigEquiv σ) i = (FinIndSigEquiv σ) (Fin.cast h.symm i) := by
  cases h
  rfl

variable (X : Fam S) [Finite (Sigma X)]
/-- Converts a finite family `X : Fam S` into a `Signature S` together with
a sort-preserving equivalence `X ≃ₛ σ.IdxFam`. The construction:
1. Classically enumerate `Sigma X ≃ Fin n`.
2. Read off sorts to build a signature via `fromList`.
3. Compose with `FinIndSigEquiv` to get `f : Sigma X ≃ Sigma σ.IdxFam`.
4. Show `f` preserves sorts, then extract fiberwise maps for `MSEquiv`. -/
noncomputable def famToSignature : Σ σ : Signature S, X ≃ₛ σ.IdxFam := by
  classical
  -- 1. Classically obtain an enumeration Sigma X ≃ Fin n
  let n := Classical.choose (Finite.exists_equiv_fin (Sigma X))
  let e : Sigma X ≃ Fin n :=
    Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin (Sigma X)))
  -- 2. Build the signature whose sort list is [sort of e⁻¹(0), sort of e⁻¹(1), …]
  let l := List.ofFn (fun i : Fin n => e.symm i)
  let σ := Signature.fromList (l.map Sigma.fst)
  have hl : l.length = n := by simp only [List.length_ofFn, l]
  have hσ : σ.length = n := by simp only [fromList_length, List.length_map, hl, σ]
  -- σ.toList is exactly the sort list we built from
  have hlσ : l.map Sigma.fst = σ.toList := by
    have h : Signature.toList (Signature.fromList (l.map Sigma.fst)) = σ.toList := by
      simp_all only [List.map_ofFn, l, n, e, σ]
    simp only [toList_fromList] at h
    exact h
  refine ⟨σ, ?_⟩
  -- 3. Compose: Sigma X →ᵉ Fin n →ᵉ Sigma σ.IdxFam
  let f := e.trans (hσ ▸ FinIndSigEquiv σ)
  -- 4a. f preserves sorts: (f p).1 = p.1
  --   Unfolds to: the i-th sort in σ = sort of e⁻¹(i), which holds by construction.
  have hfst : ∀ p : Sigma X, (f p).1 = p.1 := by
    intro ⟨s, x⟩
    set i : Fin n := e ⟨s, x⟩
    set i' : Fin σ.length := Fin.cast hσ.symm i
    -- Relate (f ⟨s,x⟩).1 to σ.toList[i']
    have hfi : (f ⟨s, x⟩).1 = σ.toList.get (Fin.cast (toList_length σ) i') := by
      rw [←getIdxFam_fst]
      have : (f ⟨s, x⟩).1 = (σ.getIdxFam i').fst := by
        simp only [Equiv.trans_apply, cast_FinIndSigEquiv_apply, f]
        change (σ.FinIndSigEquiv i').fst = (σ.getIdxFam i').fst
        simp_all only [List.map_ofFn, List.length_ofFn, l, n, e, σ, i', i]
        rfl
      simp_all only [List.map_ofFn, List.length_ofFn, Equiv.trans_apply,
        cast_FinIndSigEquiv_apply, l, n, e, σ, f, i', i]
    -- Then σ.toList[i'] = (l.map fst)[i'] = (e.symm (e ⟨s,x⟩)).1 = s
    rw [hfi]
    simp only [List.get_eq_getElem, ← hlσ,  List.getElem_map]
    simp_all only [List.length_ofFn, Fin.cast, List.get_eq_getElem, List.getElem_ofFn,
      Fin.eta, Equiv.symm_apply_apply, l, i', i]
  -- 4b. f.symm also preserves sorts (follows from hfst + f being an equiv)
  have hfsymm_fst : ∀ v : Sigma σ.IdxFam, (f.symm v).1 = v.1 := by
    intro ⟨s, v⟩
    exact (hfst (f.symm ⟨s, v⟩)).symm.trans (by simp only [Equiv.apply_symm_apply])
  -- 5. Extract fiberwise forward/inverse maps by casting along sort-preservation proofs
  let toFun : X →ₛ σ.IdxFam := ⟨fun s x =>
    (by simp [hfst ⟨s, x⟩] : (f ⟨s, x⟩).fst = s) ▸ (f ⟨s, x⟩).2⟩
  let invFun : σ.IdxFam →ₛ X := ⟨fun s v =>
    (by simp only [hfsymm_fst ⟨s, v⟩] : (f.symm ⟨s, v⟩).1 = s) ▸ (f.symm ⟨s, v⟩).2⟩
  -- Key reconstitution lemmas: packaging fiberwise maps back into sigma pairs
  have h_map : ∀ (s : S) (x : X s), ⟨s, toFun s x⟩ = f ⟨s, x⟩ := by
    intro s x
    simp only [toFun]
    refine Sigma.ext (by simp only [hfst] : _) ?_
    simp_all only [List.length_ofFn, List.map_ofFn, Equiv.trans_apply,
      Fam.FamMap.mk_apply, eqRec_heq_iff_heq, heq_eq_eq, l, n, e, σ, f]
  have h_inv : ∀ (s : S) (v : σ.IdxFam s), ⟨s, invFun s v⟩ = f.symm ⟨s, v⟩ := by
    intro s v
    simp only [invFun]
    refine Sigma.ext (by simp only [hfsymm_fst] : _) ?_
    simp_all only [List.length_ofFn, List.map_ofFn, Equiv.trans_apply, Fam.FamMap.mk_apply,
      cast_FinIndSigEquiv_apply, Equiv.symm_trans_apply, eqRec_heq_iff_heq, heq_eq_eq, l, n, e, σ,
      toFun, f]
  -- 6. Assemble the MSEquiv; inverses follow from f being an equivalence
  exact {
    toFun, invFun
    left_inv' := by
      intro s x
      exact eq_of_heq (Sigma.mk.inj (by rw [h_inv, h_map]; simp only [Equiv.symm_apply_apply])).2
    right_inv' := by
      intro s v
      exact eq_of_heq (Sigma.mk.inj (by rw [h_map, h_inv]; simp only [Equiv.apply_symm_apply])).2
  }

end finite_family_conversion

section variable_maps
/-! ## Variable Mappings

This section defines variable transformations between Signature structures:

### Type Hierarchy
- `SigMap σ τ`: General variable maps (type alias for `σ.IdxFam →ₛ τ.IdxFam`)
- `SigEmbed σ τ`: Injective variable maps (type alias for `MSEmbedding σ.IdxFam τ.IdxFam`)
- `SigEquiv σ τ`: Bijective variable maps (type alias for `MSEquiv σ.IdxFam τ.IdxFam`)

### Relationship to PEquiv
While `PEquiv` describes associative equivalences between Signatures,
`SigEquiv` describes equivalences between variable families up to associative and commutative
equivalence. The function `fromPEquiv : PEquiv σ τ → SigEquiv σ τ`
(defined in the `var_equivs` section) connects these two notions.

### Core Operations
Identity and Extensions:
- `SigMap.Id`, `SigEmbed.Id`, `SigEquiv.Id`: Identity transformations
- `extend_right`: Extend map by identity on right: `(σ → τ) ⇒ (σ ⨯ η → τ ⨯ η)`
- `extend_left`: Extend map by identity on left: `(σ → τ) ⇒ (η ⨯ σ → η ⨯ τ)`
- `incl_left`: Inject left: `σ → σ ⨯ τ`
- `incl_right`: Inject right: `σ → τ ⨯ σ`

Structural Transformations:
- `comm`: Swap factors: `σ ⨯ τ ≃ τ ⨯ σ`
- `assocL`: Left-associate: `((σ ⨯ τ) ⨯ η) ≃ (σ ⨯ (τ ⨯ η))`
- `assocR`: Right-associate: `(σ ⨯ (τ ⨯ η)) ≃ ((σ ⨯ τ) ⨯ η)`
- `nilLeft`: Cancel nil on left: `nil ⨯ σ ≃ σ`
- `nilRight`: Cancel nil on right: `σ ⨯ nil ≃ σ`

### Usage Patterns
- ⨯⨯Syntax.lean⨯⨯: `reindex` operations for terms and formulas, `block_swap` for variable swapping
- ⨯⨯SyntaxClasses.lean⨯⨯: Quantifier casting (e.g., `nilLeft` for `∀' s` notation)
- ⨯⨯Semantics.lean⨯⨯: Structural transformations in realization proofs
-/

/-- A type for dependent mappings on bound variable sets -/
abbrev SigMap (σ τ : Signature S) := σ.IdxFam →ₛ τ.IdxFam

/-- Injective SigMaps -/
abbrev SigEmbed (σ τ : Signature S) := Fam.MSEmbedding σ.IdxFam τ.IdxFam

/-- SigMaps which are Equivs -/
abbrev SigEquiv (σ τ : Signature S) := Fam.MSEquiv σ.IdxFam τ.IdxFam

/-- SigEmbeds are determined by their toFun. -/
@[ext]
lemma varEmbed_ext {σ τ : Signature S} {h h' : SigEmbed σ τ}
    (heq : h.toFun = h'.toFun) : h = h' := by
  ext x x_1 : 3
  simp_all only

/-- SigEquivs are determined by their toFun. -/
@[ext]
lemma varEquiv_ext {σ τ : Signature S} {h h' : SigEquiv σ τ}
    (heq : h.toFun = h'.toFun) : h = h' := by
  ext x x_1 : 3
  simp_all only

/-- Identity variable map -/
abbrev SigMap.Id {σ : Signature S} : SigMap σ σ := FamMap.idₛ

/-- Identity variable embedding -/
@[simp] def SigEmbed.Id {σ : Signature S} : SigEmbed σ σ :=
 { toFun := SigMap.Id,
   inj' := by
     intro t h a₂ a
     subst a
     rfl
 }

/-- Identity variable equivalence -/
@[simp] def SigEquiv.Id {σ : Signature S} : SigEquiv σ σ :=
 {toFun := SigMap.Id ,
  invFun := SigMap.Id,
  left_inv' := by intro s h; rfl,
  right_inv' := by intro s h; rfl
  }

@[simp] lemma SigMap.Id_apply {σ : Signature S} (s : S) (v : σ.IdxFam s) :
  (SigMap.Id s) v = v := rfl

@[simp] lemma SigEmbed.Id_apply {σ : Signature S} (s : S) (v : σ.IdxFam s) :
  (SigEmbed.Id s) v = v := rfl


/-- If we have a varMap from `σ` to `τ`, it can naturally be extended to products
    with `η` by applying the identity on `η`-variables. -/
@[simp]
def SigMap.extend_right {σ τ η : Signature S} (h : SigMap σ τ)
  : SigMap (σ ⨯ η) (τ ⨯ η) :=
   ⟨fun s => fun v =>
      match v with
      | .left w =>
          Idx.left ((h s) w)
      | .right w =>
          Idx.right w⟩

@[simp] lemma SigMap.extend_right_left {σ τ η : Signature S} (h : SigMap σ τ)
    {s : S} (w : σ.IdxFam s) :
    SigMap.extend_right (η := η) h s (Idx.left w) = Idx.left (h s w) := rfl

@[simp] lemma SigMap.extend_right_right {σ τ η : Signature S} (h : SigMap σ τ)
    {s : S} (w : η.IdxFam s) :
    SigMap.extend_right (η := η) h s (Idx.right w) = Idx.right w := rfl

def SigMap.extend_left {σ τ η : Signature S} (h : SigMap σ τ)
  : SigMap (η ⨯ σ) (η ⨯ τ) :=
   ⟨fun s => fun v =>
      match v with
      | .left w  =>
          Idx.left w
      | .right w =>
          Idx.right ((h s) w)⟩

@[simp] lemma SigMap.extend_left_left {σ τ η : Signature S} (h : SigMap σ τ)
    {s : S} (w : η.IdxFam s) :
    SigMap.extend_left (η := η) h s (Idx.left w) = Idx.left w := rfl

@[simp] lemma SigMap.extend_left_right {σ τ η : Signature S} (h : SigMap σ τ)
    {s : S} (w : σ.IdxFam s) :
    SigMap.extend_left (η := η) h s (Idx.right w) = Idx.right (h s w) := rfl

/-- Canonical Extension of SigEmbeds by adding a factor on the right.
    The mapping maps variables on the left by h and variables on the
    right embed in the same position, relative to the right factor. -/
def SigEmbed.extend_right {σ τ η : Signature S} (h : SigEmbed σ τ)
  : SigEmbed (σ ⨯ η) (τ ⨯ η) :=
  { toFun := SigMap.extend_right h
  , inj' := by
      intro s x y hxy
      cases x <;> cases y <;>
        simp only [SigMap.extend_right, FamMap.mk_apply, reduceCtorEq] at hxy
      case left =>
        rw[Idx.left.injEq] at *
        apply h.inj' at hxy
        simp only [hxy];
      case right =>
        rw[Idx.right.injEq] at *
        exact hxy
  }

/-- Canonical Extension of SigEquivs by adding a factor on the right.
    The mapping maps variables on the left by h and variables on the
    right embed in the same position, relative to the right factor. -/
def SigEquiv.extend_right {σ τ η : Signature S} (h : SigEquiv σ τ)
  : SigEquiv (σ ⨯ η) (τ ⨯ η) :=
  { toFun := SigMap.extend_right h,
    invFun := ⟨fun s => fun v =>
      match v with
      |.left w => Idx.left (h.invFun s w)
      |.right w => Idx.right w⟩,
    left_inv' := by
      intro s v
      match v with
      |.left w =>
          have hw : h.invFun s ((FamMapClass.toFamMap h) s w) = w := by
            change h.invFun s (h.toFun s w) = w
            exact h.inv_to s w
          simp [hw]
      |.right w => rfl
    right_inv' := by
      intro s v
      match v with
      |.left w =>
          have hw : (FamMapClass.toFamMap h) s (h.invFun s w) = w := by
            change h.toFun s (h.invFun s w) = w
            exact h.to_inv s w
          simp [hw]
      |.right w => rfl
  }

/-- Canonical Extension of SigEquivs by adding a factor on the left.
    The mapping maps variables on the right by h and variables on the
    left embed in the same position, relative to the right factor. -/
def SigEquiv.extend_left {σ τ η : Signature S} (h : SigEquiv σ τ)
  : SigEquiv (η ⨯ σ) (η ⨯ τ) :=
  { toFun := SigMap.extend_left h,
    invFun := ⟨fun s => fun v =>
      match v with
      |.left w => Idx.left w
      |.right w => Idx.right (h.invFun s w)⟩,
    left_inv' := by
      intro s v
      match v with
      |.left w => rfl
      |.right w =>
          have hw : h.invFun s ((FamMapClass.toFamMap h) s w) = w := by
            change h.invFun s (h.toFun s w) = w
            exact h.inv_to s w
          simp [hw]
    right_inv' := by
      intro s v
      match v with
      |.left w => rfl
      |.right w =>
          have hw : (FamMapClass.toFamMap h) s (h.invFun s w) = w := by
            change h.toFun s (h.invFun s w) = w
            exact h.to_inv s w
          simp [hw]
  }

/-- The Inclusion map `σ.IdxFam → (σ ⨯ τ).IdxFam` -/
abbrev SigMap.incl_left {σ τ : Signature S} : SigMap σ (σ ⨯ τ) :=
  ⟨fun _ => fun v => Idx.left v⟩

/-- The Inclusion map `σ.IdxFam → (τ ⨯ σ).IdxFam` -/
abbrev SigMap.incl_right {σ τ : Signature S} : SigMap σ (τ ⨯ σ) :=
  ⟨fun _ => fun v => Idx.right v⟩

@[simp] lemma SigMap.incl_left_apply {σ τ : Signature S} {s : S} (w : σ.IdxFam s) :
    SigMap.incl_left (σ := σ) (τ := τ) s w = Idx.left w := rfl

@[simp] lemma SigMap.incl_right_apply {σ τ : Signature S} {s : S} (w : σ.IdxFam s) :
    SigMap.incl_right (σ := σ) (τ := τ) s w = Idx.right w := rfl




/-- The Inclusion embedding `σ.IdxFam → (σ ⨯ τ).IdxFam` -/
abbrev SigEmbed.incl_left {σ τ : Signature S} : SigEmbed σ (σ ⨯ τ) :=
  {toFun := SigMap.incl_left,
    inj' := by
    intro t v w h
    cases v <;>
      cases w <;>
        simp_all only [SigMap.incl_left_apply] <;>
        apply  Idx.left_injEq.mp at h <;>
        exact h
  }

/-- The Inclusion map `σ.IdxFam → (τ ⨯ σ).IdxFam` -/
abbrev SigEmbed.incl_right {σ τ : Signature S} : SigEmbed σ (τ ⨯ σ) :=
  {toFun := SigMap.incl_right,
    inj' := by
      intro t v w h
      cases v <;> cases w <;>
      simp_all only [SigMap.incl_right_apply] <;>
      apply  Idx.right_injEq.mp at h <;>
      exact h
  }

@[simp]
lemma SigMap.idExtend {σ : Signature S} (η : Signature S) :
  (Id (σ := σ)).extend_right = Id (σ := σ ⨯ η) := by
  simp_all only [extend_right, Id_apply]
  ext s x : 1
  simp_all only [Fam.FamMap.mk_apply, Id_apply]
  split
  next v vσ => simp_all only
  next v vτ => simp_all only

@[simp]
lemma SigEmbed.idExtend {σ : Signature S} (η : Signature S) :
  (Id (σ := σ)).extend_right = Id (σ := σ ⨯ η) := by
  ext s v
  cases v <;> rfl


@[simp]
lemma SigEquiv.idExtend {σ : Signature S} (η : Signature S) :
  (Id (σ := σ)).extend_right = Id (σ := σ ⨯ η) := by
  ext s v
  cases v <;> rfl

@[simp]
lemma SigMap.extend_right_comp
  {σ τ η ξ : Signature S}
  (hστ : SigMap σ τ) (hτη : SigMap τ η) :
  ∀ s : S,
    SigMap.extend_right (η := ξ) hτη s ∘ (SigMap.extend_right hστ s)
      = SigMap.extend_right (hτη ∘ₛ hστ) s := by
  intro s
  ext v
  cases v with
  | left w =>
    simp_all only [extend_right, Fam.FamMap.mk_apply,  Function.comp_apply, FamMap.comp_apply']
  | right w =>
    simp_all only [extend_right, Fam.FamMap.mk_apply,  Function.comp_apply, FamMap.comp_apply']

@[simp]
lemma SigMap.extend_left_comp
  {σ τ η ξ : Signature S}
  (hστ : SigMap σ τ) (hτη : SigMap τ η) :
  ∀ s : S,
    SigMap.extend_left (η := ξ) hτη s ∘ (SigMap.extend_left hστ s)
      = SigMap.extend_left (hτη ∘ₛ hστ) s := by
  intro s
  ext v
  cases v with
  | left w => simp_all only [Function.comp_apply, extend_left_left]
  | right w => simp_all only [Function.comp_apply, extend_left_right, FamMap.comp_apply']

/-- Rotate IdxFams of shape `τ ⨯ σ` to those of `σ ⨯ τ` -/
def SigMap.comm {σ τ : Signature S} :
    SigMap (τ ⨯ σ) (σ ⨯ τ) :=
⟨fun _ v =>
  match v with
  | Idx.left w  => Idx.right w
  | Idx.right w => Idx.left w⟩

@[simp] lemma SigMap.comm_comm {s : S}
  {σ τ : Signature S} {v : (σ ⨯ τ).IdxFam s} :
  (comm (σ := σ) (τ := τ) s) (comm (σ := τ) (τ := σ) s v) = v := by
  cases v
  case left => rfl
  case right => rfl

@[simp] lemma SigMap.comm_apply_left
  (σ τ : Signature S) {s} (w : τ.IdxFam s) :
  comm (σ := σ) (τ := τ) s (Idx.left w) = Idx.right w := rfl

@[simp] lemma SigMap.comm_apply_right
  (σ τ : Signature S) {s} (w : σ.IdxFam s) :
  comm (σ := σ) (τ := τ) s (Idx.right w) = Idx.left w := rfl

lemma var_eq {s : S} {v : ⦃s⦄.IdxFam s} : v = Idx.var := by
  cases v
  case var => rfl

end variable_maps

section var_equivs
/- This section builds a large class of SigMaps based on equivalences of Signature's.
  The goal is to develop a general mapping from any `PEquiv σ τ` to a `SigEquiv σ τ`,
  which will allow us to associate signatures of formulas and terms somewhat painlessly.

  This section is just recapitulating all of the patterns we needed to build up PEquiv.
  Maybe there is a less verbose way to do this...
-/
namespace SigMap

open Signature

/--
Associate a product from left to write
-/
def assocL (σ τ η : Signature S) : SigMap ((σ ⨯ τ) ⨯ η) (σ ⨯ (τ ⨯ η)) :=
  ⟨fun _ v =>
    match v with
    | Idx.left (Idx.left  vσ) =>
        Idx.left vσ
    | Idx.left (Idx.right vτ) =>
        Idx.right (Idx.left vτ)
    | Idx.right vη =>
        Idx.right (Idx.right vη)⟩

/--
Associate a product from right to left
-/
def assocR (σ τ η : Signature S) : SigMap (σ ⨯ (τ ⨯ η)) ((σ ⨯ τ) ⨯ η) :=
  ⟨fun _ v =>
    match v with
    | Idx.left vσ =>
        Idx.left (Idx.left vσ)
    | Idx.right (Idx.left vτ) =>
        Idx.left (Idx.right vτ)
    | Idx.right (Idx.right vη) =>
        Idx.right vη⟩

lemma assocL_assocR_left_inv (σ τ η : Signature S) :
    ∀ s (v : IdxFam ((σ ⨯ τ) ⨯ η) s),
      assocR (S := S) σ τ η s (assocL (S := S) σ τ η s v) = v :=
by
  intro s v; cases v with
  | left w =>
      cases w with
      | left vσ   => rfl
      | right vτ  => rfl
  | right w    => rfl

lemma assocL_assocR_right_inv (σ τ η : Signature S) :
    ∀ s (v : IdxFam (σ ⨯ (τ ⨯ η)) s),
      assocL (S := S) σ τ η s (assocR (S := S) σ τ η s v) = v :=
by
  intro s v; cases v with
  | left w => rfl
  | right w =>
      cases w with
      | left vτ  => rfl
      | right vη => rfl

/-
These are a very tedious set of nil-cancelling maps, needed for completeness to construct
our general map `PEquiv → SigEquiv`.

It may be potentially less messy to just in-line these proofs into the eventual defintions
of their associated SigEquivs?
-/

/-- Cancel off nil factors. -/
def nil_left {σ : Signature S} :
    SigMap (⦃⦄ ⨯ σ) σ :=
  ⟨fun _ v =>
    match v with
    | Idx.right vσ => vσ⟩

/-- `nil.Idx.right` gives a mapping to add nil factors -/
def nil_left_inv {σ : Signature S} :
    SigMap σ (⦃⦄ ⨯ σ) :=
  ⟨fun _ v => Idx.right v⟩

/-- Eliminate out of an empty signature -/
def nilElim (ξ : Signature S) : SigMap nil ξ :=
  default

lemma nil_left_left_inv {σ : Signature S} :
    ∀ s (v : IdxFam (⦃⦄ ⨯ σ) s),
      nil_left_inv (S := S) s (nil_left (S := S) s v) = v :=
by
  intro s v
  cases v with
  | right vσ => rfl
  | left vτ => cases vτ

lemma nil_left_right_inv {σ : Signature S} :
    ∀ s (v : IdxFam σ s),
      nil_left (S := S) s (nil_left_inv (S := S) s v) = v :=
by
  intro s v; rfl

def nil_right {σ : Signature S} :
    SigMap (σ ⨯ ⦃⦄) σ :=
  ⟨fun _ v =>
    match v with
    | Idx.left vσ => vσ⟩

def nil_right_inv {σ : Signature S} :
    SigMap σ (σ ⨯ ⦃⦄) :=
  ⟨fun _ v => Idx.left v⟩

lemma nil_right_left_inv {σ : Signature S} :
    ∀ s (v : IdxFam (σ ⨯ ⦃⦄) s),
      nil_right_inv (S := S) s (nil_right (S := S) s v) = v :=
by
  intro s v
  cases v with
  | left vσ => rfl
  | right vτ => cases vτ

lemma nil_right_right_inv {σ : Signature S} :
    ∀ s (v : IdxFam σ s),
      nil_right (S := S) s (nil_right_inv (S := S) s v) = v :=
by
  intro s v; rfl


end SigMap

namespace SigEquiv

variable {σ τ : Signature S}

open Signature SigMap

/-- Lifting SigMap.assocL to a SigEquiv. -/
def assocL (σ τ η : Signature S) :
    SigEquiv ((σ ⨯ τ) ⨯ η) (σ ⨯ (τ ⨯ η)) :=
{ toFun     := SigMap.assocL σ τ η
  , invFun  := SigMap.assocR σ τ η
  , left_inv'  := SigMap.assocL_assocR_left_inv  σ τ η
  , right_inv' := SigMap.assocL_assocR_right_inv σ τ η }

/-- Lifting SigMap.assocR to a SigEquiv. -/
def assocR (σ τ η : Signature S) :
    SigEquiv (σ ⨯ (τ ⨯ η)) ((σ ⨯ τ) ⨯ η) :=
{ toFun     := SigMap.assocR σ τ η
  , invFun  := SigMap.assocL σ τ η
  , left_inv'  := SigMap.assocL_assocR_right_inv σ τ η
  , right_inv' := SigMap.assocL_assocR_left_inv  σ τ η }

/-- Alias for SigEquiv.Id -/
@[simp]
abbrev refl (σ : Signature S) : SigEquiv σ σ := SigEquiv.Id

/-- Symmetry of SigEquivs -/
@[simp]
def symm (e : SigEquiv σ τ) : SigEquiv τ σ :=
  Fam.MSEquiv.symm e

/-- Rotate IdxFams of shape `τ ⨯ σ` to those of `σ ⨯ τ` -/
def comm {σ τ : Signature S} :
    SigEquiv (σ ⨯ τ) (τ ⨯ σ) :=
  { toFun     := SigMap.comm
  , invFun  := SigMap.comm
  , left_inv'  := fun _ _ => SigMap.comm_comm
  , right_inv' := fun _ _ => SigMap.comm_comm}

/-- SigEquivs are closed under composition -/
@[simp]
def trans {σ τ η : Signature S} (e₁ : SigEquiv σ τ) (e₂ : SigEquiv τ η) : SigEquiv σ η :=
  Fam.MSEquiv.trans e₁ e₂

/-- SigEquiv for `nil ⨯ σ ≃ σ`. -/
def nilLeft (σ : Signature S) :
    SigEquiv (nil ⨯ σ) σ :=
{ toFun     := nil_left
  , invFun  := nil_left_inv
  , left_inv'  := nil_left_left_inv
  , right_inv' := nil_left_right_inv  }

/-- SigEquiv for `σ ⨯ nil ≃ σ`. -/
def nilRight (σ : Signature S) :
    SigEquiv (σ ⨯ nil) σ :=
{ toFun     := nil_right
  , invFun  := nil_right_inv
  , left_inv'  := nil_right_left_inv
  , right_inv' := nil_right_right_inv }

/-- Canonical mapping from any PEquiv to a SigEquiv -/
def fromPEquiv {S : Type u} :
    {σ τ : Signature S} → PEquiv σ τ → SigEquiv σ τ
  | _, _, (@PEquiv.refl _ σ )  =>
      SigEquiv.refl (σ := σ)
  | _, _, PEquiv.symm e =>
      (SigEquiv.fromPEquiv e).symm
  | _, _, PEquiv.trans e₁ e₂ =>
      (SigEquiv.fromPEquiv e₁).trans (SigEquiv.fromPEquiv e₂)
  | _, _, PEquiv.assocL σ τ η =>
      SigEquiv.assocL σ τ η
  | _, _, PEquiv.assocR σ τ η =>
      SigEquiv.assocR σ τ η
  | _, _, PEquiv.nil_left σ =>
      SigEquiv.nilLeft σ
  | _, _, PEquiv.nil_right σ =>
      SigEquiv.nilRight σ
  | _, _, PEquiv.prod_congr_left e =>
      SigEquiv.extend_right (SigEquiv.fromPEquiv e)
  | _, _, PEquiv.prod_congr_right e =>
      SigEquiv.extend_left (SigEquiv.fromPEquiv e)

end SigEquiv
end var_equivs

open Idx

section one_sort
/-! ## OneSort Signatures

A `OneSort s σ` is a witness that the signature `σ` contains only variables of sort `s`.
This is useful for working with single-sorted fragments within a multi-sorted logic,
allowing us to treat multi-sorted signatures as if they were single-sorted when all
variables happen to share the same sort.

### Key Results
- `OneSort.getIdxFam_sort`: Any variable index in a OneSort signature has the designated sort
- `OneSort.oneSort_iff_toList`: Characterization via the flattened list of sorts
- `OneSort.SigEquivFin`: For OneSort `σ`, we have `σ.IdxFam s ≃ Fin σ.length`
- `OneSort.fibredMapEquiv`: Fibered maps `σ.IdxFam →ₛ α` are equivalent to simple maps
  `σ.IdxFam s → α s`

### Typical Use Cases
- Quantifying over a block of same-sort variables (e.g., `∀ x₁ x₂ ... xₙ`)
- Simplifying proofs when all bound variables have the same sort
- Converting between multi-sorted and single-sorted representations
-/

/-- A witness that signature `σ` contains only variables of sort `s`. -/
inductive OneSort (s : S) : Signature S → Prop
  | nil : OneSort s .nil
  | of  : OneSort s ⦃s⦄
  | prod {σ τ : Signature S} (hσ : OneSort s σ) (hτ : OneSort s τ) : OneSort s (σ ⨯ τ)

/-- A witness that signature `σ` contains only variables with sorts from A. -/
inductive fromSorts (A : Set S) : Signature S → Prop
  | nil : fromSorts A .nil
  | of {a : S} (h : a ∈ A): fromSorts A ⦃a⦄
  | prod {σ τ : Signature S} (hσ : fromSorts A σ) (hτ : fromSorts A τ) : fromSorts A (σ ⨯ τ)

lemma fromSorts.of_in {a : S} {A : Set S} (h : fromSorts A ⦃a⦄) : a ∈ A := by
  cases h; case of ha => exact ha

lemma fromSorts.prodl {σ τ : Signature S} {A : Set S} (h : fromSorts A (σ ⨯ τ)) : fromSorts A σ :=
  by cases h ; simp_all only

lemma fromSorts.prodr {σ τ : Signature S} {A : Set S} (h : fromSorts A (σ ⨯ τ)) :
  fromSorts A τ := by cases h ; simp_all only

lemma OneSort.of_in {t : S} {s : S} (h : OneSort s (.of t)) : t = s  := by
  cases h ; simp only

lemma OneSort.prodl {σ τ : Signature S} {s : S} (h : OneSort s (σ ⨯ τ)) : OneSort s σ := by
  cases h ; simp_all only

lemma OneSort.prodr {σ τ : Signature S} {s : S} (h : OneSort s (σ ⨯ τ)) : OneSort s τ := by
  cases h ; simp_all only

namespace fromSorts

variable {A : Set S}

/-- Helper: If a signature is fromSorts A, its list representation only contains elements of A. -/
lemma toList_mem {σ : Signature S} (h : fromSorts A σ) :
    ∀ x ∈ σ.toList, x ∈ A := by
  induction h with
  | nil => simp only [toList, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | @of a ha =>
    intro x t
    simp_all only [toList, List.mem_cons, List.not_mem_nil, or_false]
  | prod _ _ ihσ ihτ =>
    intro x hx
    simp only [Signature.toList, List.mem_append] at hx
    cases hx
    · apply ihσ; simp_all only
    · apply ihτ; simp_all only

/-- Any variable in a fromSorts A signature has sort in A. -/
theorem getIdxFam_sort {σ : Signature S} (h : fromSorts A σ) (i : Fin σ.length) :
    (σ.getIdxFam i).1 ∈ A := by
  rw [Signature.getIdxFam_fst]
  apply toList_mem h
  apply List.get_mem

/-- Characterization: `σ` is fromSorts A iff every sort in `toList σ` is in A. -/
lemma fromSorts_iff_toList {A : Set S} {σ : Signature S} :
  (fromSorts A σ) ↔ (∀ t ∈ σ.toList, t ∈ A) := by
  induction σ with
  | nil =>
    simp only [toList, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    exact fromSorts.nil
  | of a =>
    rw [toList]
    constructor
    · intro t s ht
      apply fromSorts.of_in
      simp_all only [List.mem_cons, List.not_mem_nil, or_false]
    · intro h
      let ha : a ∈ A := by
        apply h
        simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fromSorts.of ha
  |prod σ τ hσ hτ =>
    constructor
    case mp =>
      intro h t ht
      simp only [toList, List.mem_append] at ht
      cases ht
      case inl ht =>
        cases h
        simp_all only [true_iff]
      case inr ht =>
        cases h
        simp_all only [true_iff]
    case mpr =>
      intro h
      constructor <;>
      simp_all only [toList, List.mem_append, true_or, implies_true, iff_true, or_true]

noncomputable
def fromSorts_of_toList {A : Set S} {σ : Signature S}
  (h : ∀ t ∈ σ.toList, t ∈ A) : fromSorts A σ := fromSorts_iff_toList.mpr h

lemma toList_all_in_of_fromSorts {A : Set S} {σ : Signature S} (h : fromSorts A σ) :
  ∀ t ∈ σ.toList, t ∈ A := fromSorts_iff_toList.mp h

/-- A signature built from a list of elements in A is fromSorts A. -/
noncomputable
def fromSorts_fromList {A : Set S} (l : List S) (hl : ∀ x ∈ l, x ∈ A) :
    fromSorts A (Signature.fromList l) := by
  apply fromSorts_of_toList (A := A) (σ := Signature.fromList l)
  intro t ht
  simpa only using hl t (by simpa only [toList_fromList] using ht)

/-- In a fromSorts A signature, every variable must have sort in A. -/
lemma sort_in_A {t : S} {σ : Signature S} (h : fromSorts A σ) (v : σ.IdxFam t) : t ∈ A := by
  induction σ
  case nil => cases v
  case of s' =>
    cases h
    case of ha =>
      cases v
      simp_all only
  case prod σ τ ihσ ihτ =>
    cases h
    case prod hσ hτ =>
      cases v
      case left w =>
        exact ihσ hσ w
      case right w =>
        exact ihτ hτ w

/-- All variables in an IdxFamList of a fromSorts signature have sorts in A. -/
lemma IdxFamList_sorts_mem {σ : Signature S} (h : fromSorts A σ) :
    ∀ p ∈ σ.IdxFamList, p.1 ∈ A := by
  intro ⟨s, v⟩ _
  exact sort_in_A h v

/-- OneSort s σ implies fromSorts {s} σ -/
lemma of_oneSort {s : S} {σ : Signature S} (h : OneSort s σ) : fromSorts {s} σ := by
  induction σ with
  | nil => exact fromSorts.nil
  | of t =>
    cases h
    exact fromSorts.of (Set.mem_singleton s)
  | prod σ τ ihσ ihτ =>
    cases h with
    | prod hσ hτ => exact fromSorts.prod (ihσ hσ) (ihτ hτ)

/-- fromSorts {s} σ implies OneSort s σ -/
lemma to_oneSort {s : S} {σ : Signature S} (h : fromSorts {s} σ) : OneSort s σ := by
  have hmem := fromSorts_iff_toList.mp h
  induction σ with
  | nil => exact OneSort.nil
  | of t =>
    have : t = s := hmem t (by simp only [toList, List.mem_cons, List.not_mem_nil, or_false])
    subst this
    exact OneSort.of
  | prod σ τ ihσ ihτ =>
    cases h with
    | prod hσ hτ =>
      apply OneSort.prod
      · exact ihσ hσ (fun t ht => hmem t (by simp only [toList, List.mem_append, ht, true_or]))
      · exact ihτ hτ (fun t ht => hmem t (by simp only [toList, List.mem_append, ht, or_true]))

/-- fromSorts for singleton sets is equivalent to OneSort -/
lemma fromSorts_singleton_iff_oneSort {s : S} {σ : Signature S} :
    (fromSorts {s} σ) ↔ (OneSort s σ) := by
  constructor
  · exact to_oneSort
  · exact of_oneSort

/-- Restrict a fibered map to just the components in A. -/
def restrict {α : Fam S} {σ : Signature S} (g : σ.IdxFam →ₛ α) : (s : A) → σ.IdxFam s → α s :=
  fun s => g s

/-- Extend a map defined on A-components to a fibered map. -/
def extend {α : Fam S} {σ : Signature S} (h : fromSorts A σ) (f : (s : A) → σ.IdxFam s → α s) :
  σ.IdxFam →ₛ α :=
  ⟨fun t v =>
    by
      have ht : t ∈ A := sort_in_A h v
      exact f ⟨t, ht⟩ v⟩

lemma restrict_extend {α : Fam S} {σ : Signature S} (h : fromSorts A σ)
    (f : (s : A) → σ.IdxFam s → α s) :
    restrict (σ := σ) (α := α) (extend (σ := σ) (α := α) h f) = f := by
  rfl

lemma extend_restrict {α : Fam S} {σ : Signature S} (h : fromSorts A σ) (g : σ.IdxFam →ₛ α) :
    extend (σ := σ) (α := α) h (restrict (σ := σ) (α := α) g) = g := by
  rfl

/-- For fromSorts signatures, fibered maps are equivalent to maps defined on A-components. -/
def fibredMapEquiv {α : Fam S} {σ : Signature S} (h : fromSorts A σ) :
    (σ.IdxFam →ₛ α) ≃ ((s : A) → σ.IdxFam s → α s) :=
{ toFun := restrict (σ := σ) (α := α)
, invFun := extend (σ := σ) (α := α) h
, left_inv := extend_restrict (σ := σ) (α := α) h
, right_inv := restrict_extend (σ := σ) (α := α) h
}

end fromSorts

namespace OneSort

variable {s : S}

/-- Helper: If a signature is OneSort s, its list representation only contains s. -/
lemma toList_mem {σ : Signature S} (h : OneSort s σ) :
    ∀ x ∈ σ.toList, x = s := by
    rw[←fromSorts.fromSorts_singleton_iff_oneSort] at h
    exact fromSorts.toList_mem h

/-- Any variable in a OneSort signature has sort s. -/
theorem getIdxFam_sort {σ : Signature S} (h : OneSort s σ) (i : Fin σ.length) :
    (σ.getIdxFam i).1 = s := by
  rw[←fromSorts.fromSorts_singleton_iff_oneSort] at h
  simpa only [Set.mem_singleton_iff] using (fromSorts.getIdxFam_sort h i)

/-- Characterization: `σ` is OneSort iff every sort in `toList σ` equals `s`. -/
lemma oneSort_iff_toList {s : S} {σ : Signature S} :
  (OneSort s σ) ↔ (∀ t ∈ σ.toList, t = s) := by
  rw[←fromSorts.fromSorts_singleton_iff_oneSort]
  simp only [fromSorts.fromSorts_iff_toList, Set.mem_singleton_iff]

def oneSort_of_toList {s : S} {σ : Signature S}
  (h : ∀ t ∈ σ.toList, t = s) : OneSort s σ :=
  oneSort_iff_toList.mpr h

lemma toList_all_eq_of_oneSort {s : S} {σ : Signature S} (h : OneSort s σ) :
  ∀ t ∈ σ.toList, t = s :=
  oneSort_iff_toList.mp h

/-- A signature built from `n` copies of sort `s` is trivially OneSort. -/
noncomputable
def oneSort_fromList_replicate (s : S) (n : ℕ) :
    OneSort s (Signature.fromList (List.replicate n s)) := by
  apply oneSort_of_toList (s := s) (σ := Signature.fromList (List.replicate n s))
  intro t ht
  simpa only using (List.eq_of_mem_replicate
    (by simpa only [List.mem_replicate, ne_eq, toList_fromList] using ht))

/-- In a OneSort signature, every variable must have sort `s`. -/
lemma sort_is_s {t : S} {σ : Signature S} (h : OneSort s σ) (v : σ.IdxFam t) : t = s := by
  rw[←fromSorts.fromSorts_singleton_iff_oneSort] at h
  simpa only [Set.mem_singleton_iff] using fromSorts.sort_in_A h v

/-- All variables in an IdxFamList of a OneSort signature have sort s. -/
lemma IdxFamList_sort_eq {σ : Signature S} (h : OneSort s σ) :
    ∀ p ∈ σ.IdxFamList, p.1 = s := by
  intro ⟨t, v⟩ _
  exact sort_is_s h v

/-- Inverse of `Idx.toFin` for OneSort signatures: maps `Fin σ.length` back to `σ.IdxFam s`. -/
def toFinInv {σ : Signature S} (h : OneSort s σ) (i : Fin σ.length) : σ.IdxFam s :=
  match σ with
  | .nil => nomatch i
  | .of t =>
      have : t = s := by cases h; rfl
      this ▸ Signature.Idx.var
  | .prod σ' τ' =>
      if hi : (i : Nat) < σ'.length then
        have hσ' : OneSort s σ' := by cases h with | prod hσ _ => exact hσ
        Signature.Idx.left (toFinInv hσ' ⟨(i : Nat), hi⟩)
      else
        have hτ' : OneSort s τ' := by cases h with | prod _ hτ => exact hτ
        let hle : σ'.length ≤ (i : Nat) := Nat.le_of_not_gt hi
        let hj : (i : Nat) - σ'.length < τ'.length :=
          nat_lt_lemma (n := σ'.length) (m := (i : Nat)) (k := τ'.length) i.is_lt hle
        Signature.Idx.right (toFinInv hτ' ⟨(i : Nat) - σ'.length, hj⟩)

lemma toFin_surj {σ : Signature S} (h : OneSort s σ) :
    Function.Surjective (toFin (σ := σ) (s := s)) :=
  by
    induction h with
    | nil =>
        intro i
        cases i with
        | mk n hn =>
          cases hn
    | of =>
        intro i
        refine ⟨(Signature.Idx.var : ⦃s⦄.IdxFam s), ?_⟩
        cases i with
        | mk n hn =>
          have hn0 : n = 0 := Nat.eq_of_lt_succ_of_not_lt hn (by simp only [not_lt_zero',
            not_false_eq_true])
          ext
          simp only [toFin, hn0]
    | @prod σ τ hσ hτ ihσ ihτ =>
        intro i
        by_cases hi : (i : Nat) < σ.length
        · rcases ihσ ⟨(i : Nat), hi⟩ with ⟨vσ, hvσ⟩
          refine ⟨Signature.Idx.left vσ, ?_⟩
          calc
            Signature.Idx.toFin (σ := σ ⨯ τ) (s := s) (Signature.Idx.left vσ)
                = Signature.injLeft σ τ (Signature.Idx.toFin (σ := σ) (s := s) vσ) := by
                    rfl
            _ = Signature.injLeft σ τ ⟨(i : Nat), hi⟩ := by
                  simp only [hvσ]
            _ = i := by
                  ext
                  rfl
        · have hle : σ.length ≤ (i : Nat) := Nat.le_of_not_gt hi
          have hj : (i : Nat) - σ.length < τ.length := by
            have h' := Nat.sub_lt_sub_right (b := (σ ⨯ τ).length) hle
            simp_all only [length, not_lt, Fin.is_lt, add_tsub_cancel_left, forall_const]
          let j : Fin τ.length := ⟨(i : Nat) - σ.length, hj⟩
          rcases ihτ j with ⟨vτ, hvτ⟩
          refine ⟨Signature.Idx.right vτ, ?_⟩
          calc
            Signature.Idx.toFin (σ := σ ⨯ τ) (s := s) (Signature.Idx.right vτ)
                = Signature.injRight σ τ (Signature.Idx.toFin (σ := τ) (s := s) vτ) := by
                    rfl
            _ = Signature.injRight σ τ j := by
                  simp only [hvτ]
            _ = i := by
                  ext
                  simp only [injRight, Nat.add_sub_of_le hle, Fin.eta, j]

/-- For a OneSort signature, `σ.IdxFam s` is equivalent to `Fin σ.length`.
    This is the main structural result: all variables can be numbered 0, 1, ..., n-1. -/
noncomputable def SigEquivFin {σ : Signature S} (h : OneSort s σ) :
    σ.IdxFam s ≃ (Fin σ.length)  :=
  Equiv.ofBijective
    (fun v => (Signature.Idx.toFin (σ := σ) (s := s) v))
    ⟨Signature.Idx.toFin_inj (σ := σ) (s := s),
     toFin_surj (σ := σ) (s := s) h⟩

/-- Restrict a fibered map to just the `s`-component. -/
def restrict {α : Fam S} {σ : Signature S} (g : σ.IdxFam →ₛ α) : σ.IdxFam s → α s :=
  g s

/-- Extend a simple map `σ.IdxFam s → α s` to a fibered map `σ.IdxFam →ₛ α`. -/
def extend {α : Fam S} {σ : Signature S} (h : OneSort s σ) (f : σ.IdxFam s → α s) : σ.IdxFam →ₛ α :=
  ⟨fun t v =>
    by
      cases (OneSort.sort_is_s (s := s) (σ := σ) h (v := v)) with
      | refl => exact f v⟩

@[simp] lemma restrict_extend {α : Fam S} {σ : Signature S}
    (h : OneSort s σ) (f : σ.IdxFam s → α s) :
    restrict (σ := σ) (α := α) (extend (σ := σ) (α := α) h f) = f := by
  rfl

@[simp] lemma extend_restrict {α : Fam S} {σ : Signature S}
    (h : OneSort s σ) (g : σ.IdxFam →ₛ α) :
    extend (σ := σ) (α := α) h (restrict (σ := σ) (α := α) g) = g := by
  ext t v
  cases (OneSort.sort_is_s (s := s) (σ := σ) h (v := v)) with
  | refl => rfl

/-- For OneSort signatures, fibered maps are equivalent to simple maps.
    This simplifies working with variable assignments when all variables share a sort. -/
def fibredMapEquiv {α : Fam S} {σ : Signature S} (h : OneSort s σ) :
    (σ.IdxFam →ₛ α) ≃ (σ.IdxFam s → α s) :=
{ toFun := restrict (σ := σ) (α := α)
, invFun := extend (σ := σ) (α := α) h
, left_inv := extend_restrict (σ := σ) (α := α) h
, right_inv := restrict_extend (σ := σ) (α := α) h
}

/-- The number of `s`-variables equals the signature length (as a natural number). -/
theorem card_IdxFam_eq_length {σ : Signature S} (h : OneSort s σ) :
    Fintype.card (σ.IdxFam s) = σ.length := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (SigEquivFin h))

/-- The cardinality of `s`-variables equals the signature length (as a cardinal). -/
theorem mk_IdxFam_eq_length {σ : Signature S} (h : OneSort s σ) :
    Cardinal.mk (σ.IdxFam s) = σ.length := by
  classical
  simp only [(Cardinal.mk_congr
      ((SigEquivFin (σ := σ) (s := s) h).trans Equiv.ulift.{u, 0}.symm)),
    Cardinal.mk_fintype, Fintype.card_ulift, Fintype.card_fin]

end OneSort

end one_sort

namespace SigEquiv

variable {S : Type u}

def prod_congr {σ σ' τ τ' : Signature S} (e1 : SigEquiv σ σ') (e2 : SigEquiv τ τ') :
    SigEquiv (σ ⨯ τ) (σ'.prod τ') :=
  SigEquiv.extend_left e2 |>.trans (SigEquiv.extend_right e1)

end SigEquiv

end Signature

end MSFirstOrder
