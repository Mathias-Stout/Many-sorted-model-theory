import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic
import Lean
import ProdExpr.Fam
import Mathlib.SetTheory.Cardinal.Basic


universe u v

namespace MSFirstOrder

/--
Non-associative product expressions as recommended by Adam Topaz in Zulip chat:
-/
inductive ProdExpr (S : Type u) where
  | nil  : ProdExpr S
  | of   : S → ProdExpr S
  | prod : ProdExpr S → ProdExpr S → ProdExpr S
deriving Repr, DecidableEq

/-- Mapping suggested by Adam Topaz: -/
@[reducible]
def ProdExpr.Interpret {S : Type u} (X : S → Type v) : ProdExpr S → Type v
  | .nil       => PUnit
  | .of s      => X s
  | .prod a b  => Interpret X a × Interpret X b

namespace ProdExpr

/--
An alternative inductive version of `toFam`. The idea is to construct, for each `σ : ProdExpr S`,
and each `s : S`, a canonical type `indVar σ s` representing the collection of `s`-type variables
occuring in `σ`. While we can do this with `Fin`, this approach avoids the use of indices and
preserves the non-associative positional data of `σ`.
-/
inductive indVar {S : Type u} : ProdExpr S → S → Type u where
  | var {s : S} : indVar (.of s) s
  | left {σ τ: ProdExpr S} {s : S} (v : indVar σ s) : indVar (σ.prod τ) s
  | right {σ τ: ProdExpr S} {s : S} (v : indVar τ s) : indVar (σ.prod τ) s
deriving Repr

variable {S : Type u}

section defs

def length : ProdExpr S → ℕ
  | .nil => 0
  | .of _     => 1
  | .prod a b  => a.length + b.length

@[simp] lemma length_nil : (ProdExpr.nil : ProdExpr S).length = 0 := by simp[ProdExpr.length]
@[simp] lemma length_of (s : S) : (ProdExpr.of s).length = 1 := by simp[ProdExpr.length]
@[simp] lemma length_prod (σ τ : ProdExpr S) :
  (ProdExpr.prod σ τ).length = σ.length + τ.length := by simp[ProdExpr.length]

/-- `indVar` for a product splits as a sum of `indVar` for the factors. -/
def indVar_as_prod (σ τ : ProdExpr S) :
    (σ.prod τ).indVar ≃ₛ σ.indVar ⊕ₛ τ.indVar :=
{ toFun := fun s v =>
    match v with
    | ProdExpr.indVar.left  vσ => Sum.inl vσ
    | ProdExpr.indVar.right vτ => Sum.inr vτ
  , invFun := fun s v =>
    match v with
    | Sum.inl vσ => ProdExpr.indVar.left vσ
    | Sum.inr vτ => ProdExpr.indVar.right vτ
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

/-- Flatten a `ProdExpr` to a list of sorts. -/
def toList : ProdExpr S → List S
  | .nil       => []
  | .of s      => [s]
  | .prod a b  => a.toList ++ b.toList

/--
Given acc, and an input list L we want to insert L into acc
so that acc comes before L and the resulting item is normalized.
This is done by injesting head to tail, taking each head s and inserting
it as the left factor.
-/
def fromListAux (acc : ProdExpr S) : List S → ProdExpr S
  | []      => acc
  | s :: L  =>
      let acc' :=
        match acc with
        | .nil   => .of s --If accumulating on nil, just reaplce with (of s)
        | acc    => .prod acc (.of s) --Otherwise we make (of s) the new left product
      fromListAux acc' L

/-- Fold a list of `S` into a left-associated `ProdExpr S`. -/
def fromList (L : List S) : ProdExpr S :=
  fromListAux .nil L

abbrev fromList' {S : Type*} : (List S) → ProdExpr S
    | [] => .nil
    | [a] => .of a
    | a :: (b :: r) => .prod (.of a) (fromList' (b :: r))

lemma toList_fromListAux (acc : ProdExpr S) (l : List S) :
    (fromListAux acc l).toList = acc.toList ++ l := by
  induction l generalizing acc with
  | nil =>
      simp [fromListAux]
  | cons s l ih =>
      simp_all only [fromListAux]
      cases acc <;> simp [toList]

lemma toList_fromList (l : List S) :
    (fromList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a as ih => rw[fromList, toList_fromListAux]; rfl

lemma toList_length (a : ProdExpr S) : a.length = a.toList.length := by
  induction a with
  | of => simp only [length, toList, List.length_cons, List.length_nil, zero_add]
  | prod _ _ ih₁ ih₂ => simp only [length, ih₁, ih₂, toList, List.length_append]
  | nil => simp only [length, toList, List.length_nil]

end to_list

section maps

lemma nat_lt_lemma {n m k : ℕ} (hink : m < n + k) (hni : n ≤ m) : m - n < k := by
   have h := Nat.sub_lt_sub_right (a:= m) (c:= n) (b := n + k)
   simp_all only [add_tsub_cancel_left, forall_const]

def get : ∀ {σ : ProdExpr S}, Fin σ.length → S
  | .nil, i =>
      False.elim (Fin.elim0 i)
  | .of s, _ =>
      s
  | .prod σ τ, i =>
      if h : (i : Nat) < σ.length then
        σ.get ⟨i, h⟩
      else
        τ.get
          ⟨(i : Nat) - σ.length,
            by
              have hi : (i : Nat) < σ.length + τ.length := i.is_lt
              have hge : σ.length ≤ (i : Nat) := Nat.le_of_not_lt h
              have hi' : (↑i : Nat) < σ.length + τ.length := hi
              have hsub :
                (↑i : Nat) - σ.length < τ.length := by
                 simp_all only [not_lt, nat_lt_lemma hi']
              exact hsub
          ⟩

/--
Left index transformation to ensure the identity
  `(prod σ τ).get (injLeft σ τ j) = σ.get j`
-/
def injLeft (σ τ : ProdExpr S) (i : Fin σ.length) :
    Fin (ProdExpr.prod σ τ).length :=
  ⟨i,
    by
      -- `i < σ.length ≤ σ.length + τ.length`
      have hi : (i : Nat) < σ.length := i.is_lt
      exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)⟩

@[simp] lemma get_prod_left
    {σ τ : ProdExpr S} (i : Fin σ.length) :
    (ProdExpr.prod σ τ).get (injLeft σ τ i) = σ.get i := by
  simp [injLeft, ProdExpr.get, ProdExpr.length]

@[simp] lemma get_prod_left'
    {σ τ : ProdExpr S} (i : Fin (ProdExpr.prod σ τ).length) (hi : i < σ.length) :
    (ProdExpr.prod σ τ).get i = σ.get ⟨i, hi⟩  := by
  have heq: (ProdExpr.prod σ τ).get i = (ProdExpr.prod σ τ).get (injLeft σ τ ⟨i, hi⟩) := by
    simp[injLeft]
  simp[heq]

/--
Right index transformation to ensure the identity
  `(prod σ τ).get (injRight σ τ j) = τ.get j`
-/
def injRight (σ τ : ProdExpr S) (j : Fin τ.length) :
    Fin (ProdExpr.prod σ τ).length :=
  ⟨σ.length + j,
    by
      have hj : (j : Nat) < τ.length := j.is_lt
      have : σ.length + (j : Nat) < σ.length + τ.length :=
        Nat.add_lt_add_left hj σ.length
      simp [ProdExpr.length]⟩

@[simp] lemma get_prod_right
    {σ τ : ProdExpr S} (j : Fin τ.length) :
    (prod σ τ).get (injRight σ τ j) = τ.get j := by
  let i : Fin (ProdExpr.prod σ τ).length := injRight σ τ j
  have hi_val : (i : Nat) = σ.length + (j : Nat) := rfl
  have h_not_lt : ¬ (i : Nat) < σ.length := by
    intro h
    have : σ.length + (j : Nat) < σ.length := by
      simp_all
    exact
      (Nat.not_lt.mpr (Nat.le_add_right _ _)) this
  have hi_lt_total : (i : Nat) < σ.length + τ.length := i.is_lt
  have h_sub :
      (i : Nat) - σ.length = (j : Nat) := by
    simp [hi_val, Nat.add_comm]
  have hnot:  ¬ ↑(σ.injRight τ j) < σ.length :=
    by simp[injRight]
  simp[get, injRight]

end maps

section equivalences
/- This section defines the equivalence relation on `ProdExpr S` expressing when
`σ` and `τ` are equivalent up to associativity. It also defines a canonical normalized
representative for each class which trims out all `nil` factors from products and
associates to the right. For example,
    `prod (prod nil
                (of s)
          )
          (prod (prod (of s)
                      (of t)
                )
                (prod nil
                      (of t)
                )
          )`

    becomes

    `prod (of s)
          (prod (of s)
                (prod (of t)
                      (of t)
                )
          )`

    As of now this normalization definition kind of cheats by flattening into a list and
    then reconstructing the ProdExpr.
-/

/--
Inductive type indexing the basic generating types of product equivalences
-/
inductive PEquiv : ProdExpr S → ProdExpr S → Type u where
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

namespace PEquiv

def prod_congr {a a' b b' : ProdExpr S}
    (h₁ : PEquiv a a') (h₂ : PEquiv b b') :
    PEquiv (.prod a b) (.prod a' b') :=
  PEquiv.trans (PEquiv.prod_congr_left h₁) (PEquiv.prod_congr_right h₂)

end PEquiv

open PEquiv

/--
Constructs a PEquiv on an intermediate state of the fromList construction:
-/
def PEquiv_fromListAux (acc : ProdExpr S) (l : List S) :
  PEquiv (.prod acc (fromList l)) (fromListAux acc l) := by
  induction l generalizing acc with
  | nil =>
      rw[fromList, fromListAux, fromListAux]
      exact PEquiv.nil_right acc
  | cons s l ih =>
      cases acc with
      | nil => rw[fromList, fromListAux]; apply PEquiv.nil_left
      | of t =>
          rw[fromList, fromListAux, fromListAux]
          · apply PEquiv.trans _ (ih ((of t).prod (of s)))
            let h := PEquiv.assocR (S:= S) (of t) (of s) (nil.fromListAux l)
            apply PEquiv.trans _ h
            apply PEquiv.prod_congr_right
            apply PEquiv.trans _ (ih (of s)).symm
            exact PEquiv.refl
          · simp
      | prod a b =>
          rw [fromList, fromListAux]
          have h1 : PEquiv (.prod (.of s) (fromList l)) (fromListAux (.of s) l) :=
            ih (.of s)
          have h2 := ih (.prod (.prod a b) (.of s))
          have h1' := PEquiv.symm h1
          have h_left :
            PEquiv (.prod (.prod a b) (fromListAux (.of s) l))
                    (.prod (.prod a b) (.prod (.of s) (fromList l))) :=
            PEquiv.prod_congr_right h1'
          have h_assoc := PEquiv.assocR (.prod a b) (.of s) (fromList l)
          exact PEquiv.trans h_left (PEquiv.trans h_assoc h2)

lemma fromListAux_append (acc : ProdExpr S) (l₁ l₂ : List S) :
  fromListAux acc (l₁ ++ l₂) =
    fromListAux (fromListAux acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil =>
      simp [fromListAux]
  | cons s l ih =>
      cases acc with
      | nil =>
          simp [fromListAux, List.cons_append, ih]
      | of t =>
          simp [fromListAux, List.cons_append, ih]
      | prod a b =>
          simp [fromListAux, List.cons_append, ih]

lemma fromList_append_eq_fromListAux (l₁ l₂ : List S) :
  fromList (l₁ ++ l₂) = fromListAux (fromList l₁) l₂ := by
  unfold fromList
  simpa [fromList] using
    fromListAux_append (acc := ProdExpr.nil) (l₁ := l₁) (l₂ := l₂)

/--
Helper for showing that `σ ≃ fromList (toList σ)`
-/
def fromList_app (l₁ l₂ : List S) :
  PEquiv (.prod (fromList l₁) (fromList l₂)) (fromList (l₁ ++ l₂)) := by
  have h_eq : fromList (l₁ ++ l₂) = fromListAux (fromList l₁) l₂ :=
    fromList_append_eq_fromListAux (S := S) l₁ l₂
  have h :=
    PEquiv_fromListAux (S := S) (acc := fromList l₁) (l := l₂)
  simpa [h_eq] using h

/--
The PEquiv witnessing the equivalence between `σ` and `(fromList (toList σ))`
-/
def equivToFromList : (σ : ProdExpr S) → PEquiv σ (fromList (toList σ))
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
def leftAppend {S} : ProdExpr S → ProdExpr S → ProdExpr S
  | acc, .nil        => ProdExpr.prod acc ProdExpr.nil
  | acc, .of s       => ProdExpr.prod acc (.of s)
  | acc, .prod σ τ   =>
      let acc' := leftAppend acc σ
      leftAppend acc' τ

/-- Left-associate a `ProdExpr` without trimming `nil`s. -/
def leftAssoc : ProdExpr S → ProdExpr S
  | .nil      => .nil
  | .of s     => .of s
  | .prod σ τ => leftAppend (leftAssoc σ) τ

def trimNil : ProdExpr S → ProdExpr S
  | .nil      => .nil
  | .of s     => .of s
  | .prod σ τ =>
      match trimNil σ, trimNil τ with
      | .nil, .nil => .nil
      | .nil, τ'   => τ'
      | σ',  .nil  => σ'
      | σ',  τ'    => .prod σ' τ'

lemma toList_leftAppend (acc σ : ProdExpr S) :
  (leftAppend acc σ).toList = acc.toList ++ σ.toList := by
  induction σ generalizing acc with
  | nil =>
      simp [leftAppend, toList]
  | of s =>
      simp [leftAppend, toList]
  | prod σ τ ihσ ihτ =>
      simp [leftAppend, toList, ihσ, ihτ, List.append_assoc]

lemma toList_leftAssoc (σ : ProdExpr S) :
  (leftAssoc σ).toList = σ.toList := by
  induction σ with
  | nil =>
      simp [leftAssoc, toList]
  | of s =>
      simp [leftAssoc, toList]
  | prod σ τ ihσ ihτ =>
      simp [leftAssoc, toList, toList_leftAppend, ihσ]


def normalize (σ : ProdExpr S) : ProdExpr S := trimNil (leftAssoc σ)

/-- The normalization bundled with a proof of equivalence -/
@[simp]
def normalize_list (σ : ProdExpr S) : Σ σ' : ProdExpr S, PEquiv σ σ' :=
  ⟨fromList (toList σ), equivToFromList σ⟩

variable {S : Type u}

lemma trimNil_prod_of (acc : ProdExpr S) (s : S) :
    trimNil (.prod acc (.of s)) = match trimNil acc with
      | .nil => .of s
      | a => .prod a (.of s) := by
  simp only [trimNil, reduceCtorEq, imp_self, implies_true]
  split
  next x x_1 heq heq_1 => simp_all only [reduceCtorEq]
  next x x_1 heq x_2 => simp_all only [reduceCtorEq, implies_true]
  next x x_1 heq x_2 x_3 => simp_all only [reduceCtorEq]
  next x x_1 x_2 x_3 x_4 => simp_all only [imp_false, reduceCtorEq, implies_true]

lemma fromListAux_eq_trimNil_leftAppend (acc : ProdExpr S) (σ : ProdExpr S) :
    fromListAux (trimNil acc) (toList σ) = trimNil (leftAppend acc σ) := by
  induction σ generalizing acc with
  | nil =>
      simp [toList, fromListAux, leftAppend, trimNil]
      split <;> simp_all
  | of s =>
      simp only [toList, fromListAux, leftAppend, trimNil_prod_of]
  | prod x y ihx ihy =>
      rw [toList, leftAppend,fromListAux_append]
      simp_all only

lemma normalize_unique (σ : ProdExpr S) : normalize σ =  (fromList (toList σ))  := by
  unfold normalize
  induction σ with
  | nil =>
      rfl
  | of s =>
      rfl
  | prod x y ih_x ih_y =>
      rw [fromList, toList, fromListAux_append]
      have h_fold_x :  trimNil (leftAssoc x) = fromListAux .nil (toList x) := ih_x
      rw [←h_fold_x]
      rw [fromListAux_eq_trimNil_leftAppend (leftAssoc x) y]
      rfl

open Equiv

def interpretEquiv (X : S → Type v) :
    {σ₁ σ₂ : ProdExpr S} → PEquiv σ₁ σ₂ → Interpret X σ₁ ≃ Interpret X σ₂
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

def InterpretNormalized (X : S → Type v) (σ : ProdExpr S) : Type v :=
  Interpret X (normalize σ)

def interpretToInterpretNormalizedEquiv (X : S → Type v) (σ : ProdExpr S) :
    Interpret X σ ≃ InterpretNormalized X σ := by
    let h:= equivToFromList σ
    unfold InterpretNormalized
    rw[normalize_unique]
    exact interpretEquiv X h

end normalization

abbrev append (σ : ProdExpr S) (τ : ProdExpr S) : ProdExpr S := (σ.prod τ)

abbrev extend (σ : ProdExpr S) (s : S) : ProdExpr S :=  σ.prod (.of s)

section variable_maps
/-
This section explores a few options for defining alternatives to toFam which avoid
variable indexing by `Fin n`. indVar does this with an inductive type, and toFam2 does
it using Sigma types.
-/

/-- List out the associated variables to a given σ -/
def indVarList : (σ : ProdExpr S) -> List (Sigma σ.indVar)
  | nil => []
  | of s => [⟨s, indVar.var⟩]
  | prod σ τ => σ.indVarList.map (fun ⟨s, v⟩ => ⟨s, indVar.left v⟩) ++
                τ.indVarList.map (fun ⟨s, v⟩ => ⟨s, indVar.right v⟩)

/-- A type for dependent mappings on bound variable sets -/
abbrev VarMap (σ τ : ProdExpr S) := σ.indVar →ₛ τ.indVar

/-- Injective VarMaps -/
abbrev VarEmbed (σ τ : ProdExpr S) := Fam.MSEmbedding σ.indVar τ.indVar

/-- VarMaps which are Equivs -/
abbrev VarEquiv (σ τ : ProdExpr S) := Fam.MSEquiv σ.indVar τ.indVar

/-- VarEmbeds are determined by their toFun.
 Mysterious aesop proof maybe is telling me this is redundant? -/
@[ext]
lemma varEmbed_ext {σ τ : ProdExpr S} {h h' : VarEmbed σ τ} (heq : h.toFun = h'.toFun) :
    h = h' := by
  ext x x_1 : 3
  simp_all only

/-- VarEquivs are determined by their toFun -/
@[ext]
lemma varEquiv_ext {σ τ : ProdExpr S} {h h' : VarEquiv σ τ} (heq : h.toFun = h'.toFun) :
    h = h' := by
  ext x x_1 : 3
  simp_all only

/-- Identity variable map -/
def VarMap.Id {σ : ProdExpr S} : VarMap σ σ := Fam.id (α := σ.indVar)

/-- Identity variable embedding -/
@[simp] def VarEmbed.Id {σ : ProdExpr S} : VarEmbed σ σ :=
 {toFun := VarMap.Id ,
  inj' := by
          intro t h a₂ a
          subst a
          simp_all only [Fam.id,VarMap.Id, id_eq]
  }

/-- Identity variable equivalence -/
@[simp] def VarEquiv.Id {σ : ProdExpr S} : VarEquiv σ σ :=
 {toFun := VarMap.Id ,
  invFun := VarMap.Id,
  left_inv' := by intro s h; simp[VarMap.Id],
  right_inv' := by intro s h; simp[VarMap.Id]
  }

@[simp] lemma VarMap.Id_apply {σ : ProdExpr S} (s : S) (v : σ.indVar s) :
  (VarMap.Id s) v = v := rfl

@[simp] lemma VarEmbed.Id_apply {σ : ProdExpr S} (s : S) (v : σ.indVar s) :
  (VarEmbed.Id s) v = v := rfl

instance (σ τ : ProdExpr S) : CoeFun (VarEmbed σ τ) (fun _ => σ.indVar →ₛ τ.indVar) where
  coe := (fun h => h.toFun)

instance (σ τ : ProdExpr S) : CoeFun (VarEquiv σ τ) (fun _ => σ.indVar →ₛ τ.indVar) where
  coe := (fun h => h.toFun)

/-- If we have a varMap from `σ` to `τ`,
  it can naturally be extended to products with `η` by applying the
    identity on `η`-variables.

    It might be helpful to reformulate this stuff by just spelling out the equivalence

      `σ.indVar ⊕ₛ η.indVar ≃ₛ (σ.prod η).indVar`

    which can be used to define a more general class of variable mappings.
-/
def VarMap.extend_right {σ τ η : ProdExpr S} (h : VarMap σ τ) :
    VarMap (σ.prod η) (τ.prod η) :=
   fun s => fun v =>
      match v with
      | .left w =>
          indVar.left ((h s) w)
      | .right w =>
          indVar.right w

def VarMap.extend_left {σ τ η : ProdExpr S} (h : VarMap σ τ) :
    VarMap (η.prod σ) (η.prod τ) :=
   fun s => fun v =>
      match v with
      | .left w  =>
          indVar.left w
      | .right w =>
          indVar.right ((h s) w)

/-- Canonical Extension of VarEmbeds by adding a factor on the right.
    The mapping maps variables on the left by h and variables on the
    right embed in the same position, relative to the right factor. -/
def VarEmbed.extend_right {σ τ η : ProdExpr S} (h : VarEmbed σ τ)
  : VarEmbed (σ.prod η) (τ.prod η) :=
  { toFun := VarMap.extend_right h
  , inj' := by
      intro s x y hxy
      cases x <;> cases y <;> simp only [VarMap.extend_right, indVar.left.injEq,
        reduceCtorEq, indVar.right.injEq] at hxy
      case left =>
        apply h.inj' at hxy
        simp[hxy];
      case right => simp[hxy]
  }

/-- Canonical Extension of VarEequivs by adding a factor on the right.
    The mapping maps variables on the left by h and variables on the
    right embed in the same position, relative to the right factor. -/
def VarEquiv.extend_right {σ τ η : ProdExpr S} (h : VarEquiv σ τ)
  : VarEquiv (σ.prod η) (τ.prod η) :=
  { toFun := VarMap.extend_right h,
    invFun := fun s => fun v =>
      match v with
      |.left w => indVar.left (h.invFun s w)
      |.right w => indVar.right w,
    left_inv' := by
      intro s v
      match v with
      |.left w => simp[VarMap.extend_right]
      |.right w => rfl
    right_inv' := by
      intro s v
      match v with
      |.left w => simp[VarMap.extend_right]
      |.right w => rfl
  }

/-- Canonical Extension of VarEequivs by adding a factor on the left.
    The mapping maps variables on the right by h and variables on the
    left embed in the same position, relative to the right factor. -/
def VarEquiv.extend_left {σ τ η : ProdExpr S} (h : VarEquiv σ τ)
  : VarEquiv (η.prod σ) (η.prod τ) :=
  { toFun := VarMap.extend_left h,
    invFun := fun s => fun v =>
      match v with
      |.left w => indVar.left w
      |.right w => indVar.right (h.invFun s w),
    left_inv' := by
      intro s v
      match v with
      |.left w => rfl
      |.right w => simp[VarMap.extend_left]
    right_inv' := by
      intro s v
      match v with
      |.left w => rfl
      |.right w => simp[VarMap.extend_left]
  }

/-- The Inclusion map `σ.indVar → (σ.prod τ).indVar` -/
abbrev VarMap.incl_left {σ τ : ProdExpr S} : VarMap σ (σ.prod τ) :=
  fun _ => fun v => indVar.left v

/-- The Inclusion map `σ.indVar → (τ.prod σ).indVar` -/
abbrev VarMap.incl_right {σ τ : ProdExpr S} : VarMap σ (τ.prod σ) :=
  fun _ => fun v => indVar.right v

@[simp]
lemma VarMap.idExtend {σ : ProdExpr S} (η : ProdExpr S) :
  (Id (σ := σ)).extend_right = Id (σ := σ.prod η) := by
  ext
  simp_all only [extend_right, Id, Fam.id, id_eq];
  split
  next v vσ => simp_all only
  next v vη => simp_all only

@[simp]
lemma VarEmbed.idExtend {σ : ProdExpr S} (η : ProdExpr S) :
  (Id (σ := σ)).extend_right = Id (σ := σ.prod η)  := by
  ext
  unfold Id extend_right VarMap.extend_right
  simp only [VarMap.Id_apply]
  split
  next v vσ => simp_all only
  next v vη => simp_all only

@[simp]
lemma VarEquiv.idExtend {σ : ProdExpr S} (η : ProdExpr S) :
  (Id (σ := σ)).extend_right = Id (σ := σ.prod η) := by
  ext
  unfold Id extend_right VarMap.extend_right
  simp only [VarMap.Id_apply]
  split
  next v vσ => simp_all only
  next v vη => simp_all only

@[simp]
lemma VarMap.extend_right_comp
  {σ τ η ξ : ProdExpr S}
  (hστ : VarMap σ τ) (hτη : VarMap τ η) :
  ∀ s : S,
    VarMap.extend_right (η := ξ) hτη s ∘ (VarMap.extend_right hστ s )
      = VarMap.extend_right (hτη ∘ₛ hστ) s  := by
  intro s
  ext v
  cases v with
  | left w => simp [VarMap.extend_right]
  | right w => simp [VarMap.extend_right]

@[simp]
lemma VarMap.extend_left_comp
  {σ τ η ξ : ProdExpr S}
  (hστ : VarMap σ τ) (hτη : VarMap τ η) :
  ∀ s : S,
    VarMap.extend_left (η := ξ) hτη s ∘ (VarMap.extend_left hστ s )
      = VarMap.extend_left (hτη ∘ₛ hστ) s  := by
  intro s
  ext v
  cases v with
  | left w => simp [VarMap.extend_left]
  | right w => simp [VarMap.extend_left]

lemma var_eq {s : S} {v : (of s).indVar s} : v = indVar.var := by
  cases v
  case var => rfl

end variable_maps

section var_equivs
/-This section builds a large class of VarMaps based on equivalences of ProdExpr's.
  The goal is to develop a general mapping from any `PEquiv σ τ` to a `VarEquiv σ τ`,
  which will allow us to associate signatures of formulas and terms somewhat painlessly.

  This section is just recapitulating all of the patterns we needed to build up PEquiv.
  Maybe there is a less verbose way to do this...
-/
namespace VarMap

open ProdExpr

/--
Associate a product from left to write
-/
def assocL (σ τ η : ProdExpr S) : VarMap ((σ.prod τ).prod η) (σ.prod (τ.prod η)) :=
  fun _ v =>
    match v with
    | indVar.left (indVar.left  vσ) =>
        indVar.left vσ
    | indVar.left (indVar.right vτ) =>
        indVar.right (indVar.left vτ)
    | indVar.right vη =>
        indVar.right (indVar.right vη)

/--
Associate a product from right to left
-/
def assocR (σ τ η : ProdExpr S) : VarMap (σ.prod (τ.prod η)) ((σ.prod τ).prod η) :=
  fun _ v =>
    match v with
    | indVar.left vσ =>
        indVar.left (indVar.left vσ)
    | indVar.right (indVar.left vτ) =>
        indVar.left (indVar.right vτ)
    | indVar.right (indVar.right vη) =>
        indVar.right vη

lemma assocL_assocR_left_inv (σ τ η : ProdExpr S) :
    ∀ s (v : indVar ((σ.prod τ).prod η) s),
      assocR (S:= S) σ τ η s (assocL (S:=S) σ τ η s v) = v :=
by
  intro s v; cases v with
  | left w =>
      cases w with
      | left vσ   => rfl
      | right vτ  => rfl
  | right w    => rfl

lemma assocL_assocR_right_inv (σ τ η : ProdExpr S) :
    ∀ s (v : indVar (σ.prod (τ.prod η)) s),
      assocL (S:=S) σ τ η s (assocR (S:=S) σ τ η s v) = v :=
by
  intro s v; cases v with
  | left w => rfl
  | right w =>
      cases w with
      | left vτ  => rfl
      | right vη => rfl

/-
These are a very tedious set of nil-cancelling maps, needed for completeness to construct
our general functor `PEquiv → VarEquiv`.

It may be potentially less messy to just in-line these proofs into the eventual defintions
of their associated VarEquivs?
-/

/-- Cancel off nil factors. -/
def nil_left (σ : ProdExpr S) :
    VarMap (ProdExpr.nil.prod σ) σ :=
  fun _ v =>
    match v with
    | indVar.right vσ => vσ

/-- `nil.indVar.right` gives a mapping to add nil factors -/
def nil_left_inv (σ : ProdExpr S) :
    VarMap σ (ProdExpr.nil.prod σ) :=
  fun _ v => indVar.right v

lemma nil_left_left_inv (σ : ProdExpr S) :
    ∀ s (v : indVar (ProdExpr.nil.prod σ) s),
      nil_left_inv (S:=S) σ s (nil_left (S:=S) σ s v) = v :=
by
  intro s v
  cases v with
  | right vσ => rfl
  | left vτ => cases vτ

lemma nil_left_right_inv (σ : ProdExpr S) :
    ∀ s (v : indVar σ s),
      nil_left (S:=S) σ s (nil_left_inv (S:=S) σ s v) = v :=
by
  intro s v; rfl

def nil_right (σ : ProdExpr S) :
    VarMap (σ.prod ProdExpr.nil) σ :=
  fun _ v =>
    match v with
    | indVar.left vσ => vσ

def nil_right_inv (σ : ProdExpr S) :
    VarMap σ (σ.prod ProdExpr.nil) :=
  fun _ v => indVar.left v

lemma nil_right_left_inv (σ : ProdExpr S) :
    ∀ s (v : indVar (σ.prod ProdExpr.nil) s),
      nil_right_inv (S:=S) σ s (nil_right (S:=S) σ s v) = v :=
by
  intro s v
  cases v with
  | left vσ => rfl
  | right vτ => cases vτ

lemma nil_right_right_inv (σ : ProdExpr S) :
    ∀ s (v : indVar σ s),
      nil_right (S:=S) σ s (nil_right_inv (S:=S) σ s v) = v :=
by
  intro s v; rfl

end VarMap

namespace VarEquiv

open ProdExpr VarMap

/-- Lifting VarMap.assocL to a VarEquiv. -/
def assocL (σ τ η : ProdExpr S) :
    VarEquiv ((σ.prod τ).prod η) (σ.prod (τ.prod η)) :=
{ toFun     := VarMap.assocL σ τ η
  , invFun  := VarMap.assocR σ τ η
  , left_inv'  := VarMap.assocL_assocR_left_inv  σ τ η
  , right_inv' := VarMap.assocL_assocR_right_inv σ τ η }

/-- Lifting VarMap.assocR to a VarEquiv. -/
def assocR (σ τ η : ProdExpr S) :
    VarEquiv (σ.prod (τ.prod η)) ((σ.prod τ).prod η) :=
{ toFun     := VarMap.assocR σ τ η
  , invFun  := VarMap.assocL σ τ η
  , left_inv'  := VarMap.assocL_assocR_right_inv σ τ η
  , right_inv' := VarMap.assocL_assocR_left_inv  σ τ η }

/-- Alias for VarEquiv.Id -/
@[simp]
abbrev refl (σ : ProdExpr S) : VarEquiv σ σ := VarEquiv.Id

/-- Symmetry of VarEquivs -/
@[simp]
def symm (σ τ : ProdExpr S) (e : VarEquiv σ τ) : VarEquiv τ σ :=
  Fam.MSEquiv.symm e

/-- VarEquivs are closed under composition -/
@[simp]
def trans {σ τ η : ProdExpr S} (e₁ : VarEquiv σ τ) (e₂ : VarEquiv τ η) : VarEquiv σ η :=
  Fam.MSEquiv.trans e₁ e₂

/-- VarEquiv for `nil.prod σ ≃ σ`. -/
def nilLeft (σ : ProdExpr S) :
    VarEquiv (nil.prod σ) σ :=
{ toFun     := nil_left σ
  , invFun  := nil_left_inv σ
  , left_inv'  := nil_left_left_inv σ
  , right_inv' := nil_left_right_inv σ }

/-- VarEquiv for `σ.prod nil ≃ σ`. -/
def nilRight (σ : ProdExpr S) :
    VarEquiv (σ.prod nil) σ :=
{ toFun     := nil_right σ
  , invFun  := nil_right_inv σ
  , left_inv'  := nil_right_left_inv σ
  , right_inv' := nil_right_right_inv σ }

/-- Canonical mapping from any PEquiv to a VarEquiv -/
def fromPEquiv {S : Type u} :
    {σ τ : ProdExpr S} → PEquiv σ τ → VarEquiv σ τ
  | _, _, (@PEquiv.refl _ σ )  =>
      VarEquiv.refl (σ := σ)
  | _, _, PEquiv.symm e =>
      (VarEquiv.fromPEquiv e).symm
  | _, _, PEquiv.trans e₁ e₂ =>
      (VarEquiv.fromPEquiv e₁).trans (VarEquiv.fromPEquiv e₂)
  | _, _, PEquiv.assocL σ τ η =>
      VarEquiv.assocL σ τ η
  | _, _, PEquiv.assocR σ τ η =>
      VarEquiv.assocR σ τ η
  | _, _, PEquiv.nil_left σ =>
      VarEquiv.nilLeft σ
  | _, _, PEquiv.nil_right σ =>
      VarEquiv.nilRight σ
  | _, _, PEquiv.prod_congr_left e =>
      VarEquiv.extend_right (VarEquiv.fromPEquiv e)
  | _, _, PEquiv.prod_congr_right e =>
      VarEquiv.extend_left (VarEquiv.fromPEquiv e)


end VarEquiv
end var_equivs

--EXPERIMENTAL:

def map {S'} (σ : ProdExpr S) (φ : S → S') : ProdExpr S' :=
match σ with
| nil => nil
| of s => of (φ s)
| prod σ₁ σ₂ => prod (σ₁.map φ) (σ₂.map φ)

open indVar
/-- Transformation required for liftAt analogue to new setting.

Interested in any feedback on this idea:

    The one-sorted case was:
      -i < m' => i
      -m' <= i < n => i + n'

    basically: (v_1, ... , v_{m'-1}, v_m, ..., v_n) => (v_1, ... , v_{m'-1},
    [n' variables in between)],  v_m, ..., v_n)

    The proposed generalization is:
    -Old vars: (σ.prod τ).indVar
    -New vars: (σ.prod (σ'.prod τ)).indVar

    where:
    -`σ variables` stay at the front
    -`τ variables` move to the end
    -`σ' variables` go in between

    and we associate to the left.
-/
def liftVar
    {σ σ' τ : ProdExpr S} : VarMap (σ.prod τ) ((σ.prod σ').prod τ) :=
    fun _ v =>
    match v with
    | .left w  =>
        .left (.left w)
    | .right w =>
        .right w

/-- Map an expression along an assignment from S to other expressions.
  Essentially we are taking every leaf of the tree corresponding to σ and
  replacing it with something else. Maybe this will be useful later if we
want to represent formulas φ(x₁,..., xₙ) where each xᵢ is itself a tuple? -/
def collapse (σ : ProdExpr (ProdExpr S)) :  ProdExpr S :=
  match σ with
  | nil => nil
  | of τ => τ
  | prod τ η => prod (collapse τ) (collapse η)


end ProdExpr
end MSFirstOrder
