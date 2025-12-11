import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Embedding.Basic

/-Wrapper code for working with families of objects with type `base → Type u'
    Similar to sigma types, but the base is fixed -/

universe u v w z u' w'

namespace List
/-A trick suggested by Sky Wilshaw.
  An alternative would be to work with a variable set + assigment functions instead of sorted tuples everywhere-/
def toFam {S : Type*} (σ : List S) : S → Type := fun s => {n : Fin σ.length // σ.get n = s}

@[simp]
theorem toFam_IsEmpty {S : Type*} : ∀ (s : S), IsEmpty <| ([] : List S).toFam s :=
  fun _s =>  ⟨fun ⟨n,_⟩ ↦ Fin.elim0 n ⟩

end List

namespace MSFirstOrder

namespace Fam
variable {base : Type u} (α : base → Type v) (β : base → Type w) (γ : base → Type z)

/-- A map between two families over the same base -/
abbrev famMap (α : base → Type v) (β : base → Type w) :=
  (s : base) → (α s → β s)

/-- Notation for famMap -/
notation:25 A  " →ₛ " B  => famMap A B

/-The following is useful notation for pointwise composition of homomorphisms which are
parametrized by a Sort type. For us, morphism will be DFunLike objects which can be coerced to
maps (t : Sorts) -> M t → N t.-/
notation:80 f " ∘ₛ " g => fun t => f t ∘ g t

/--Notation for dependent disjoint union of types-/
notation:30 f " ⊕ₛ " g => fun s => (f s) ⊕ (g s)

@[simp]
protected def id : famMap α α := fun _ => id

@[simp]
theorem famId {δ : base → Type u} : Fam.id δ = (fun d => @id (δ d)) := rfl

def EmptyFam : base → Type := fun _ => Empty


def PEmptyFam : base → Type u := fun _ => PEmpty


section aux

variable {S : Type*} {α : S → Type*} {β : S → Type*} {σ : List S} {l : List (Sigma α)}

/-- Dependent analogue of Sum.Elim-/
def Sum_inl : α →ₛ α ⊕ₛ β := fun _s a => Sum.inl a

def Sum_inr : β →ₛ α ⊕ₛ β := fun _s b => Sum.inr b

def sumElim {γ : S → Type*} (f : α →ₛ γ) (g : β →ₛ γ) : (α ⊕ₛ β) →ₛ γ :=
  fun s => Sum.elim (f s) (g s)

@[simp]
theorem sumElim_inl {γ : S → Type*} (f : α →ₛ γ)  (g : β →ₛ γ) :
    (fun s => sumElim f g s ∘ Sum.inl) = f := by
  funext s x
  rfl

@[simp]
theorem sumElim_inr {γ : S → Type*} (f : α →ₛ γ)  (g : β →ₛ γ) :
    (fun s => sumElim f g s ∘ Sum.inr) = g := by
  funext s x
  rfl

@[simp]
theorem sumComp_elim {γ : S → Type*} {δ : S → Type*} (f : γ →ₛ δ) (g : α →ₛ γ) (h : β →ₛ γ) :
    (f ∘ₛ (sumElim g h)) = sumElim (f ∘ₛ g) (f ∘ₛ h) := by
  funext s x
  simp_all only [Function.comp_apply]
  cases x <;> rfl

end aux

section manySortedEmbeddings

/-
This section introduces classes for the many-sorted analogues of embeddings and equivalences.
It provides dependent versions of Mathlib.Logic.Equiv and Mathlib.Logic.Embedding to mimic the
development of the one-sorted case.
-/
variable {Sorts : Type*} (M : Sorts → Type w) (N : Sorts → Type w')

/-- A many-sorted embedding is a family of functions that are all injective. -/
--Think about whether this can wrap ergular Embedding via sigma types.
@[ext]
structure MSEmbedding (M : Sorts → Type*) (N : Sorts → Type*) where
  /- The family of underlying functions. -/
  toFun : M →ₛ N
  /- The proof that each function in the family is injective. -/
  inj' : ∀ t, Function.Injective (toFun t)

notation:25 A  " ↪ₛ " B  => MSEmbedding A B

instance : CoeFun (M ↪ₛ N) (fun _ => M →ₛ N) where
  coe := MSEmbedding.toFun

instance : DFunLike (M ↪ₛ N) Sorts (fun t => M t → N t) where
  coe := MSEmbedding.toFun
  coe_injective' :=
   by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have : f = g := by
      funext t x
      exact congrFun (congrArg (fun φ => φ t) h) x
    cases this
    have : hf = hg := Subsingleton.elim _ _
    cases this
    rfl

def MSEmbedding.comp' {A B C : Sorts → Type*} (g: MSEmbedding B C) (f : MSEmbedding A B) :
  MSEmbedding A C :=
  {toFun := g ∘ₛ f,
    inj' := by simp only [g.inj', Function.Injective.of_comp_iff, f.inj', implies_true]
  }

/-- Constructs an embedding from a family of bundled embeddings. -/
def MSEmbedding.fromEmbeddings {M : Sorts → Type w} {N : Sorts → Type w'}
    (f : ∀ t,  (M t) ↪ (N t)) : M ↪ₛ N :=
  ⟨ (fun t => (f t : M t → N t)) , (fun t => (f t).inj') ⟩

/-- A many-sorted equivalence is a family of bijections, one for each sort. -/
structure MSEquiv (M : Sorts → Type*) (N : Sorts → Type*) where
  /-- The family of forward functions. -/
  toFun : M →ₛ N
  /-- The family of inverse functions. -/
  invFun : N →ₛ M
  /-- The proof that `invFun` is a left inverse to `toFun` for each sort. -/
  left_inv' : ∀ t, Function.LeftInverse (invFun t) (toFun t)
  /-- The proof that `invFun` is a right inverse to `toFun` for each sort. -/
  right_inv' : ∀ t, Function.RightInverse (invFun t) (toFun t)

notation:25 A  " ≃ₛ " B  => MSEquiv A B

/-- Constructs an MSEquiv from a family of bundled Equivs -/
def MSEquiv.fromEquivs {M : Sorts → Type w} {N : Sorts → Type w'}
    (f : ∀ t,  (M t) ≃ (N t)) : M ≃ₛ N :=
 ⟨ (fun t => (f t : M t → N t)),
  (fun t => ((f t).symm : N t → M t)),
  (fun t => (f t).left_inv),
  (fun t => (f t).right_inv) ⟩

/-- Function coercion for MSEquiv -/
instance : CoeFun (M ≃ₛ N) (fun _ => M →ₛ N) where
  coe := MSEquiv.toFun

instance : DFunLike (M ≃ₛ N) Sorts (fun t => M t → N t) where
  coe := MSEquiv.toFun
  coe_injective' :=
   by
    rintro ⟨f, g, L, R⟩ ⟨f', g', L', R'⟩ h
    have : f = f' := by
      funext t x
      exact congrFun (congrArg (fun φ => φ t) h) x
    have : g = g' := by
      funext t y
      have hF_t : f t = f' t := congrArg (fun φ => φ t) this
      have L_t : Function.LeftInverse (g t) (f t) := L t
      have R'_t : Function.RightInverse (g' t) (f' t) := R' t
      calc
        g t y
            = g t (f' t (g' t y)) := by
                rw[<- (R'_t y).symm]
        _   = g' t y := by
                simpa [hF_t] using L_t (g' t y)
    cases this; cases this
    have : L = L' := Subsingleton.elim _ _
    have : R = R' := Subsingleton.elim _ _
    cases this; cases this
    rfl

/-- MSEquiv ext lemma only needs to check equality of toFun:
TODO: this proof can likely be improved. -/
@[ext]
theorem MSEquiv.ext {M N : Sorts → Type*}
    {e₁ e₂ : M ≃ₛ N}
    (h : ∀ t, e₁.toFun t = e₂.toFun t) : e₁ = e₂ := by
  cases e₁ with
  | mk to₁ inv₁ left₁ right₁ =>
    cases e₂ with
    | mk to₂ inv₂ left₂ right₂ =>
      -- forward maps equal (by funext₂ on h)
      have hF : to₁ = to₂ := by
        funext t; exact h t
      -- inverse maps equal (use left inverse of e₁ and right inverse of e₂)
      have hI : inv₁ = inv₂ := by
        funext t y
        have hF_t : to₁ t = to₂ t := congrArg (fun φ => φ t) hF
        have L₁ : Function.LeftInverse (inv₁ t) (to₁ t) := left₁ t
        have R₂ : Function.RightInverse (inv₂ t) (to₂ t) := right₂ t
        calc
          inv₁ t y
              = inv₁ t (to₂ t (inv₂ t y)) := by
                  rw[<- (R₂ y).symm]
          _   = inv₂ t y := by
                  simpa [hF_t] using L₁ (inv₂ t y)
      -- identify structures fieldwise; Prop fields by proof irrelevance
      cases hF; cases hI
      have : left₁ = left₂ := Subsingleton.elim _ _
      have : right₁ = right₂ := Subsingleton.elim _ _
      cases this; cases this
      rfl


variable {M N}
/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm]
protected def MSEquiv.symm  (e : M ≃ₛ N) : MSEquiv N M := ⟨e.invFun, e.toFun, e.right_inv', e.left_inv'⟩

namespace MSEquiv

def refl (M : Sorts → Type*) : MSEquiv M M where
  toFun     := fun _ => id
  invFun    := fun _ => id
  left_inv' := by intro t x; rfl
  right_inv' := by intro t x; rfl

def toEquiv (e : MSEquiv M N) (s: Sorts) : M s ≃ N s:=
  {
    toFun := e.toFun s
    invFun := e.invFun s
    left_inv := e.left_inv' s
    right_inv := e.right_inv' s
  }

/-- Composition of many-sorted equivalences. -/
def trans {K} (e₁ : MSEquiv M N) (e₂ : MSEquiv N K) : MSEquiv M K :=
  MSEquiv.fromEquivs (fun s => Equiv.trans (e₁.toEquiv s) (e₂.toEquiv s))

lemma trans_is_comp {K} (e₁ : MSEquiv M N) (e₂ : MSEquiv N K) :
  ∀ {s : Sorts}, e₁.trans e₂ s = (e₂ ∘ₛ e₁) s := by
  intro s
  simp_all only
  rfl

/-- Helper simp lemma for applying MSEquiv inverse on left-/
@[simp] lemma inv_to (e : M ≃ₛ N) (t : Sorts) (x : M t) :
    e.invFun t (e.toFun t x) = x :=
  (e.left_inv' t) x

/-- Helper simp lemma for applying MSEquiv inverse on right-/
@[simp] lemma to_inv (e : M ≃ₛ N) (t : Sorts) (y : N t) :
    e.toFun t (e.invFun t y) = y :=
  (e.right_inv' t) y

@[simp] lemma inv_comp (e : M ≃ₛ N) (t : Sorts)
    : e.invFun t ∘ e.toFun t = id := by ext x; exact e.inv_to t x

@[simp] lemma to_comp (e : M ≃ₛ N) (t : Sorts)
    : e.toFun t ∘ e.invFun t = id := by ext y; exact e.to_inv t y

end MSEquiv

end manySortedEmbeddings

/-- A class for dependent families of injective functions. -/
class InjectivePerSort
    {Sorts : Type _} {M N : Sorts → Type _} (F : Type*)
    [DFunLike F Sorts (fun t => M t → N t)] where
    (inj' : ∀ (f: F) t, Function.Injective (f t))

instance {Sorts : Type _} {M N : Sorts → Type _}: InjectivePerSort (M ↪ₛ N) where
  inj' := MSEmbedding.inj'


/-- Per-sort analogue of `EquivLike`: an element of `F` is a family of bijections,
one for each sort. -/
class PerSortEquivLike
    {Sorts : Type _} (F : Type*) (M N : Sorts → Type _)
    [DFunLike F Sorts (fun t => M t → N t)] where
  inv : F → (N →ₛ M)
  left_inv : ∀ f t, Function.LeftInverse (inv f t) (f t)
  right_inv : ∀ f t, Function.RightInverse (inv f t) (f t)

instance {Sorts : Type _} {M N : Sorts → Type _}: PerSortEquivLike (M ≃ₛ N) M N where
  inv := MSEquiv.invFun
  left_inv := MSEquiv.left_inv'
  right_inv := MSEquiv.right_inv'

/-- Turn an element of a type `F` satisfying `PerSortEquivLike F α β` into an actual
`Equiv`. This is declared as the default coercion from `F` to `α ≃ β`. -/
@[coe]
def PerSortEquivLike.toEquiv {Sorts : Type _} {F} {M N : Sorts → Type _} [DFunLike F Sorts (fun t => M t → N t)] [PerSortEquivLike F M N] (f : F) : M ≃ₛ N where
  toFun := f
  invFun := PerSortEquivLike.inv f
  left_inv' := PerSortEquivLike.left_inv f
  right_inv' := PerSortEquivLike.right_inv f

namespace PerSortEquivLike

variable {Sorts : Type*} {F : Type*} {M N : Sorts → Type*}

variable [DFunLike F Sorts (fun t => M t → N t)] [PerSortEquivLike F M N]

@[simp]
theorem apply_inv_apply (g : F) (s : Sorts) (x : N s) : g s (inv g s x) = x := right_inv _ _ _

@[simp]
theorem inv_apply_apply (g : F) (s : Sorts) (x : M s) : (inv g) s (g s x) = x := left_inv _ _ _

theorem apply_inv_apply_fun (g : F) :
    (fun s => g s ∘ (inv g s)) = fun _ => id := by
  funext
  simp only [Function.comp_apply, apply_inv_apply, id_eq]

theorem inv_apply_apply_fun (g : F) :
    (fun s => inv g s ∘ (g s)) = fun _ => id := by
  funext
  simp only [Function.comp_apply, inv_apply_apply, id_eq]

end PerSortEquivLike
end Fam
end MSFirstOrder
