import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.SetTheory.Cardinal.Basic

/- Wrapper code for working with families of objects with type `Fam base'
    Similar to sigma types, but base is fixed. -/
universe u v w z u' v' w'

namespace MSFirstOrder

section fam
variable {base : Type u}

structure Fam base where
  toFun : base → Type v

instance : FunLike (Fam base) base (Type v) where
  coe := Fam.toFun
  coe_injective :=
   by
    intro f g hfg
    have : f = g := by
      change (⟨f.toFun⟩ : Fam base) = ⟨g.toFun⟩
      simpa only [Fam.mk.injEq] using hfg
    exact this

@[ext]
theorem Fam.ext {f g : Fam base} (h : ∀ s, f s = g s) : f = g :=
  DFunLike.ext f g h

end fam

namespace Fam

section fam_map
variable {base : Type u}

/-- A type for a map between two families over the same base -/
structure FamMap (α : Fam.{v} base) (β : Fam.{w} base) where
  toFun : (s : base) → (α s → β s)

/-- A type for the Fam of pointwise maps between two Fa. -/
def MapFam (α : Fam.{v} base) (β : Fam.{w} base) : Fam base :=
  ⟨fun s => α s → β s⟩

/-- Notation for FamMap -/
notation:25 A  " →ₛ " B  => FamMap A B

instance {α : Fam.{v} base} {β : Fam.{w} base} : DFunLike (α →ₛ β) base (fun t => α t → β t) where
  coe := FamMap.toFun
  coe_injective := by
       intro f g h; cases f; cases g; simpa only [FamMap.mk.injEq] using h

@[simp] lemma FamMap.mk_apply {α : Fam.{v} base} {β : Fam.{w} base} {s : base}
    {f : (s : base) → (α s → β s)} :
  (FamMap.mk f) s = f s := rfl

lemma mk_apply {s : base} {f : base → Type*} :
  (Fam.mk f) s = f s := rfl

@[ext]
theorem FamMap.ext {α : Fam.{v} base} {β : Fam.{w} base} {f g : α →ₛ β}
    (h : ∀ s x, f s x = g s x) : f = g := by
  apply DFunLike.ext
  intro s
  funext x
  exact h s x

def FamMap.idₛ {α : Fam base} : α →ₛ α :=
  {toFun := fun _ => id}

def FamMap.comp {α : Fam.{v} base} {β : Fam.{w} base} {γ : Fam.{z} base}
  (g : β →ₛ γ) (f : α →ₛ β) : α →ₛ γ :=
  ⟨fun s => g s ∘ f s⟩

infixr:90 " ∘ₛ " => FamMap.comp

variable {α : Fam.{v} base} {β : Fam.{w} base} {γ : Fam.{z} base}

lemma FamMap.comp_apply (g : β →ₛ γ) (f : α →ₛ β) (s) :
  (g ∘ₛ f) s  = g s ∘ f s := rfl

@[simp]
lemma FamMap.comp_apply' (g : β →ₛ γ) (f : α →ₛ β) (s) (x) :
  (g ∘ₛ f) s x  = g s (f s x) := rfl

lemma FamMap.comp_assoc {δ : Fam.{u'} base}
    (h : γ →ₛ δ) (g : β →ₛ γ) (f : α →ₛ β) :
    (h ∘ₛ g) ∘ₛ f = h ∘ₛ (g ∘ₛ f) := by
  ext s x
  rfl

lemma FamMap.idₛ_apply (s) : (FamMap.idₛ (α := α)) s  = id := rfl

@[simp]
theorem FamMap.idₛ_comp {S : Type z} {α β : Fam S} (f : α →ₛ β) : idₛ ∘ₛ f = f := by
  ext
  rw [comp_apply,idₛ_apply, Function.comp_apply,]
  rfl

@[simp]
theorem FamMap.comp_idₛ {S : Type z} {α β : Fam S} (f : α →ₛ β) : f ∘ₛ idₛ = f := by
  ext
  rw [comp_apply,idₛ_apply, Function.comp_apply,]
  rfl

@[simp] lemma FamMap.idₛ_apply' (s) (x) : (FamMap.idₛ (α := α)) s x = x := rfl

end fam_map

section fam_map_class

/-- Typeclass for types that coerce to `FamMap M N`.
    Extending `DFunLike` ensures a single coercion path to functions. -/
class FamMapClass (F : Type*) {base : outParam (Type*)}
    (M : outParam (Fam base)) (N : outParam (Fam base))
    extends DFunLike F base (fun t => M t → N t)

namespace FamMapClass

variable {base : Type*} {F : Type*} {M : Fam base} {N : Fam base} [FamMapClass F M N]

/-- Coerce any `FamMapClass` element to the bundled map type. -/
def toFamMap (f : F) : M →ₛ N := ⟨fun s x => f s x⟩

/-- The bundled coercion to `FamMap` is injective. -/
theorem toFamMap_injective :
    Function.Injective (toFamMap (F := F) (M := M) (N := N)) := by
  intro f g h
  apply DFunLike.coe_injective
  funext s x
  exact congrArg (fun (m : M →ₛ N) => m s x) h

/-- High priority coercion to FamMap for better type inference with `<$>ₛ` -/
instance (priority := 1000) instCoeTC : CoeTC F (M →ₛ N) := ⟨toFamMap⟩

@[simp] lemma coe_apply (f : F) (s : base) (x : M s) :
    ((f : M →ₛ N) s x) = (FamMapClass.toFamMap f) s x := rfl

end FamMapClass

-- Base instances to reduce friction when using bundled maps.
instance {base : Type*} {M : Fam base} {N : Fam base} : FamMapClass (M →ₛ N) M N where
  coe f := f
  coe_injective := by
    intro f g h
    exact DFunLike.coe_injective h

instance {base : Type*} {M : Fam base} {N : Fam base} :
    FamMapClass ((s : base) → M s → N s) M N where
  coe f := f
  coe_injective := by
    intro f g h
    funext s x
    exact congrFun (congrFun h s) x

@[simp] lemma coeFun_apply {base : Type*} {M : Fam base} {N : Fam base}
    (f : (s : base) → M s → N s) (s : base) (x : M s) :
    ((f : M →ₛ N) s x) = f s x := rfl


end fam_map_class

section fam_ops
variable {base : Type u}
variable {α : Fam.{v} base} {β : Fam.{w} base} {γ : Fam.{z} base} {δ : Fam.{u'} base}

def subtype (p : ∀ s, α s → Prop) : Fam base :=
  ⟨fun s => { x : α s // p s x }⟩

/-- The family of subtypes cut out by a family of sets. -/
def subtypeSet (A : ∀ s, Set (α s)) : Fam base :=
  ⟨fun s => { x : α s // x ∈ A s }⟩

def sum (α : Fam.{v} base) (β : Fam.{w} base) : Fam.{max v w} base :=
  ⟨fun s =>  (α s) ⊕ (β s)⟩

notation:30 A " ⊕ₛ " B => sum A B

def inl : α →ₛ (α ⊕ₛ β) := ⟨fun _ x => Sum.inl x⟩
def inr : β →ₛ (α ⊕ₛ β) := ⟨fun _ x => Sum.inr x⟩

lemma sum_apply {s : base} : (α ⊕ₛ β) s = (α s ⊕ β s) := rfl

def sumElim (f : α →ₛ γ) (g : β →ₛ γ) : (α ⊕ₛ β) →ₛ γ :=
  ⟨fun s => Sum.elim (f s) (g s)⟩

@[simp] lemma sumElim_inl (f : α →ₛ γ) (g : β →ₛ γ) :
    (sumElim f g ∘ₛ inl) = f := by
  ext s x; rfl

@[simp] lemma sumElim_inr (f : α →ₛ γ) (g : β →ₛ γ) :
    (sumElim f g ∘ₛ inr) = g := by
  ext s x; rfl

@[simp] lemma sumElim_eval_l (f : α →ₛ γ) (g : β →ₛ γ) {s : base} {v : α s} :
    (sumElim f g) s (Sum.inl v) = f s v := rfl

@[simp] lemma sumElim_eval_r (f : α →ₛ γ) (g : β →ₛ γ) {s : base} {v : β s} :
    (sumElim f g) s (Sum.inr v) = g s v := rfl


--@[simp]
theorem sumComp_elim (f : γ →ₛ δ) (g : α →ₛ γ) (h : β →ₛ γ) :
    (f ∘ₛ (sumElim g h)) = sumElim (f ∘ₛ g) (f ∘ₛ h) := by
  ext s x
  simp only [FamMap.comp_apply]; cases x <;> rfl

def sumMap
    (f : α →ₛ γ) (g : β →ₛ δ) : (α ⊕ₛ β) →ₛ (γ ⊕ₛ δ) :=
  ⟨fun s => Sum.map (f s) (g s)⟩

@[simp] lemma sumMap_inl (f : α →ₛ γ) (g : β →ₛ δ) :
    (sumMap f g ∘ₛ inl) = inl ∘ₛ f := by
  ext s x; rfl

@[simp] lemma sumMap_id :
    sumMap (FamMap.idₛ (α := α )) (FamMap.idₛ (α := β ))= FamMap.idₛ := by
  ext s x
  cases x <;> rfl

@[simp] lemma sumMap_inr (f : α →ₛ γ) (g : β →ₛ δ) :
    (sumMap f g ∘ₛ inr) = inr ∘ₛ g := by
  ext s x; rfl

@[simp] lemma sumMap_inl_apply (f : α →ₛ γ) (g : β →ₛ δ) (s) (x) :
    sumMap f g s (Sum.inl x) = Sum.inl (f s x) := rfl

@[simp] lemma sumMap_inr_apply (f : α →ₛ γ) (g : β →ₛ δ) (s) (x) :
    sumMap f g s (Sum.inr x) = Sum.inr (g s x) := rfl

/-
/-- Distributing pointwise evaluation over `sumElim`.
    Useful in ultraproduct proofs where we evaluate at a specific index `a`. -/
@[simp]
theorem sumElim_apply {γ : Fam base} {I : Type*}
    (f : α →ₛ ⟨fun s => I → γ s⟩) (g : β →ₛ ⟨fun s => I → γ s⟩) (a : I) :
    (fun s b => sumElim f g s b a) = sumElim ⟨fun s => I → γ s⟩ ⟨fun s x => g s x a⟩ := by
  funext s x
  cases x <;> refl
-/

def EmptyFam : Fam.{0} base := ⟨fun _ => Empty⟩

def PEmptyFam : Fam base := ⟨fun _ => PEmpty⟩

instance emptyFamisEmpty : ∀ (s : base), IsEmpty (EmptyFam s) := by
  unfold EmptyFam
  intro s
  change IsEmpty Empty
  infer_instance

instance pemptyFamisEmpty : ∀ (s : base), IsEmpty (PEmptyFam s) := by
  unfold PEmptyFam
  intro s
  change IsEmpty PEmpty
  infer_instance

@[simp]
instance sumEmptyIsEmpty [∀ (s : base), IsEmpty (α s)] [∀ (s : base), IsEmpty (β s)] :
    ∀ (s : base), IsEmpty ((α ⊕ₛ β) s) := by
  intro s
  simp only [sum, mk_apply, isEmpty_sum]
  simp_all only [and_self]

instance emptyDomUniqueMap [∀ (s : base), IsEmpty (α s)] : Unique (α →ₛ β) := by
  constructor
  · intro a
    ext s v
    apply IsEmpty.elim' _ v
    · use default
    · infer_instance

instance inhabitedImageInhabitedMap [∀ (s : base), Inhabited (β s)] : Inhabited (α →ₛ β) := by
  use fun s v => default

instance UniqueImageUniqueMap [∀ (s : base), Unique (β s)] : Unique (α →ₛ β) := by
  constructor
  · intro a
    ext s v
    simp[ ←Unique.default_eq (α := β s)]
  · infer_instance

def UnitFam {base : Type u} : Fam base := ⟨fun _ => Unit⟩

def PUnitFam {base : Type u} : Fam base := ⟨fun _ => PUnit⟩

instance unitFamisUnique : ∀ (s : base), Unique (UnitFam s) := by
  unfold UnitFam
  intro s
  change Unique Unit
  infer_instance

instance punitFamisUnique : ∀ (s : base), Unique (PUnitFam s) := by
  unfold PUnitFam
  intro s
  change Unique Unit
  infer_instance

abbrev Section (M : Fam base) := UnitFam →ₛ M

def Section.eval {M : Fam base} (f : Section M) (s) : M s := f s Unit.unit

abbrev toSection {M : Fam base} (g : ∀ s, M s) : Section M := ⟨fun s _ => g s⟩

def sectionEquiv (M : Fam base) : Section M ≃ (∀ s, M s) where
  toFun f s := f s PUnit.unit
  invFun := toSection
  left_inv := by intro f; ext s x; cases x; rfl
  right_inv := by intro g; rfl

/- `FamMap α β` is a section of `MapFam α β`. -/
def FamMap.equivMapFam (α : Fam.{v} base) (β : Fam.{w} base) :
    FamMap α β ≃ Section (MapFam α β) where
  toFun f := ⟨fun s _ => f s⟩
  invFun f := ⟨fun s a => f s () a ⟩
  left_inv := by
    intro f
    cases f
    rfl
  right_inv := by
    intro f
    ext s u
    cases u
    rfl

def sigma (α : Fam.{v} base) : Type _ :=
  Sigma α

open Cardinal

def card (α : Fam.{v} base) : Cardinal := #(α.sigma)

end fam_ops


section many_sorted_setoids

/-
This section introduces dependent families of setoids and their quotients.
It mirrors the structure of standard `Quotient`, `Quotient.lift`, and `Quotient.map`
but applied sort-wise.
-/

/-- Given a family `α : ι → Fam.{v} base`  Fam's over the same base, this is the
  `Π`-Fam over this family. Essentially this commutes the quantifiers in
  `∀ (i : ι) (∀ (s : base) Type u) ≃ ∀ (s : base) (∀ (i : ι) Type u)` so we can view
  it as a Fam object. -/
def piFam {base : Type u} {ι : Type u'} (α : ι → Fam.{v} base) : Fam base :=
  ⟨fun s => ∀ i, α i s⟩

/-- Turn a family of Sections into a Section of a pi-family. -/
def Section.pi {base : Type u} {ι : Type u'} {α : ι → Fam.{v} base}
     (f : ∀ i, Section (α i)) : Section (piFam α) :=
     ⟨fun (s: base) () => fun i => f i s ()⟩

notation "Πₛ[" f "]" => Section.pi f

variable {base : Type u} {M : Fam.{v} base} {N : Fam.{w} base}

/-- A many-sorted setoid is a family of setoids, one for each sort. -/
class MSSetoid (M : Fam.{v} base) where
  /-- The family of setoid structures. -/
  toSetoid : ∀ s, Setoid (M s)

instance [S : MSSetoid M] (s : base) : Setoid (M s) := S.toSetoid s

instance : CoeFun (MSSetoid M) (fun _ => ∀ s, Setoid (M s)) where
  coe S := S.toSetoid

instance MSSetoid.piSetoid [S : MSSetoid M] : Setoid ((s : base) → M s) := inferInstance

/-- Given a dependent mapping of Fams, returns the product MSSetoid of the family. -/
instance MSSetoid.piMSSetoid {ι} {α : ι → Fam base} [∀ i, MSSetoid (α i)] :
      MSSetoid (piFam α) := ⟨fun s => (inferInstance : Setoid (∀ i, α i s))⟩

/-- We can extend an `MSSetoid M` to an `MSSetoid (MapFam α M)` via
   sortwise application of the equivalence. -/
instance MSSetoid.instMapFam [S : MSSetoid M] {α : Fam base} :
    MSSetoid (MapFam α M) :=
  MSSetoid.mk fun s : base => (inferInstance : Setoid (α s → M s))

/-- The `instMapFam` naturally induces a Setoid structure on `N →ₛ M`: -/
instance MSSetoid.famMapSetoid [S : MSSetoid M] (N : Fam base) : Setoid (N →ₛ M) :=
  Setoid.comap (fun f => f.toFun) (inferInstance)

def MSQuotient (S : MSSetoid M) : Fam base :=
  ⟨fun s => Quotient (S.toSetoid s)⟩

/-- Notation for Many-Sorted Quotient. Input `\sdiv` for the slash. -/
notation:35 M " /ₛ " S => @MSQuotient _ M S

/-- The canonical projection map from the family to its quotient. -/
def MSQuotient.mk (S : MSSetoid M) : M →ₛ (M /ₛ S) :=
  ⟨fun s => Quotient.mk (S.toSetoid s)⟩

def MSQuotient.mkSection (S : MSSetoid M) (f : M.Section) : (M /ₛ S).Section :=
    toSection (fun s => MSQuotient.mk inferInstance s (f s ()))

@[simp]
lemma MSQuotient.mkSection_apply {s} {u} {S : MSSetoid M} {f : M.Section} :
  mkSection S f s u = MSQuotient.mk inferInstance s (f s ()) := by rfl


/--
Lift a map `f : M →ₛ N` to `(M /ₛ S) →ₛ N`.
Requires proof that `f` respects the relation `S` at every sort.
-/
def MSQuotient.lift {S : MSSetoid M} (f : M →ₛ N)
    (respects : ∀ s (x y : M s), @Setoid.r _ (S.toSetoid s) x y → f s x = f s y) :
    (M /ₛ S) →ₛ N :=
  ⟨fun s => Quotient.lift (f s) (respects s)⟩

@[simp]
theorem MSQuotient.lift_comp_mk {S : MSSetoid M} (f : M →ₛ N) (h) :
    (MSQuotient.lift f h ∘ₛ MSQuotient.mk S) = f := by
  ext s x
  rfl

/--
Map between quotients: if `f : M →ₛ N` sends related elements in `S` to related elements in `R`,
it descends to a map between quotients.
-/
def MSQuotient.map {S : MSSetoid M} {R : MSSetoid N} (f : M →ₛ N)
    (h : ∀ s (x y : M s), x ≈ y → f s x ≈ f s y) :
    (M /ₛ S) →ₛ (N /ₛ R) :=
  ⟨fun s => Quotient.map (f s) (h s)⟩

@[simp]
theorem MSQuotient.map_comp_mk {S : MSSetoid M} {R : MSSetoid N} (f : M →ₛ N) (h) :
    (MSQuotient.map f h ∘ₛ MSQuotient.mk S) = (MSQuotient.mk R) ∘ₛ f := by
  ext s x
  rfl

noncomputable def MSQuotient.out {S : MSSetoid M} : (M /ₛ S) →ₛ M :=
  ⟨fun _ ↦ Quotient.out⟩

lemma MSQuotient.out_eq {S : MSSetoid M} : MSQuotient.mk S ∘ₛ MSQuotient.out (S := S) = FamMap.idₛ
:= by
  ext s x
  exact Quotient.out_eq x

/-- Given a class of functions `q : @MQuotient (∀ i, α i) _`, returns the class of `i`-th projection
`Section (MSQuotient (S i))`. -/
def MSQuotient.eval {ι : Type*} {α : ι → Fam base} {S : ∀ i, MSSetoid (α i)}
    (q : (@MSQuotient base (piFam α) (by infer_instance)).Section) (i : ι) :
    Section (MSQuotient (S i)) :=
  toSection (fun s => MSQuotient.map ⟨fun s (m : piFam α s) => m i⟩
    (fun s x y h => by
      simp_all only [FamMap.mk_apply]
      apply h
    )
    s (q s ()))

@[simp]
theorem MSQuotient.eval_mk {ι : Type*} {α : ι → Fam base}
    {S : ∀ i, MSSetoid (α i)} (f : Section (piFam α)) :
    MSQuotient.eval (S := S) (mkSection _ f) = fun i => ⟨fun s () => mk (S i) s (f s () i)⟩ :=
  rfl

/-- The kernel of a many-sorted map `f` is the family of setoids defined by `x ≈ y ↔ f x = f y`. -/
@[reducible]
def FamMap.ker (f : M →ₛ N) : MSSetoid M where
  toSetoid := fun s => Setoid.ker (f s)

noncomputable def MSQuotient.choice {ι : Type*} {α : ι → Fam base} {S : ∀ i, MSSetoid (α i)}
      (f : (i : ι) → Section (MSQuotient (S i))) :
      Section (@MSQuotient base (piFam α) (by infer_instance)) :=
      ⟨fun s () => Quotient.choice (fun i => f i s ())⟩


@[simp] theorem MSQuotient.choice_eq
        {ι : Type*} {α : ι → Fam base} {S : ∀ i, MSSetoid (α i)} {f : ∀ i, (α i).Section} :
        MSQuotient.choice (S := S)
              (fun i => toSection (fun s => MSQuotient.mk (S i) s (f i s ())))
        = MSQuotient.mkSection _ (Πₛ[f]) := by
  ext s u
  simp only [choice, FamMap.mk_apply, mkSection_apply, mk, Section.pi]
  apply Quotient.sound
  change MSSetoid.piMSSetoid s  ((fun i ↦ ((fun i ↦ ⟦(f i) s ()⟧) i).out)) (fun i ↦ (f i) s ())
  rw[MSSetoid.piMSSetoid]
  intro i
  refine Quotient.exact ?_
  simp only [Quotient.out_eq]


/-
/--
Given xs : N →ₛ (M /ₛ S), choose representatives to get N →ₛ M, but return it
modulo the induced pointwise setoid `S.instMapFam.piSetoid : Setoid (N →ₛ M)`
-/
noncomputable def MSSetoid.choice (S : MSSetoid M) (xs : N →ₛ (M /ₛ S)) :
 Quotient (α := N →ₛ M)
          --S.instMapFam is an `MSSetoid (fun s => N s → M s)`
          --S.famMapSetoid is the corresponding piSetoid `Setoid (N →ₛ M)`
          (S.famMapSetoid N) :=
  Quotient.map (FamMap.mk) (by
                              intro a b hab
                              change (MSSetoid.famMapSetoid S N).r (⟨a⟩ : N →ₛ M) (⟨b⟩: N →ₛ M)
                              simp[famMapSetoid, Setoid.comap, Function.onFun]
                              exact hab
                           )
               (Quotient.choice (fun s => Quotient.choice (xs s)))

@[simp] theorem MSSetoid.choice_eq
  {base : Type u} {M : Fam.{v} base} {N : Fam.{w} base}
  (S : Fam.MSSetoid M) (f : N →ₛ M) :
  S.choice (MSQuotient.mk S ∘ₛ f)
    = (⟦f⟧ : Quotient (S.famMapSetoid N)) := by
    unfold MSQuotient.choice

    rw[ Quotient.choice_eq]
    have h :
      (fun s =>
        Quotient.choice (MSQuotient.mk S s ∘ f s))
        =
      (fun s =>
        (⟦f s⟧ : Quotient ((S.instMapFam (α := N)).toSetoid s))) := by
      funext s

      rw[MSQuotient.mk]



      rfl
    simp_all only [Function.comp_def, instMapFam, choice, Quotient.choice_eq]
    rfl
-/

end many_sorted_setoids



section manySortedEmbeddings

/-
This section introduces classes for the many-sorted analogues of embeddings and equivalences.
It provides dependent versions of Mathlib.Logic.Equiv and Mathlib.Logic.Embedding to mimic the
development of the one-sorted case.
-/
variable {base : Type*} (M : Fam.{w} base) (N : Fam.{w'} base)

/-- A many-sorted embedding is a family of functions that are all injective. -/
--Think about whether this can wrap ergular Embedding via sigma types.
@[ext]
structure MSEmbedding (M : Fam base) (N : Fam base) where
  /-- The family of underlying functions. -/
  toFun : M →ₛ N
  /-- The proof that each function in the family is injective. -/
  inj' : ∀ t, Function.Injective (toFun t)

notation:25 A  " ↪ₛ " B  => MSEmbedding A B

instance : FamMapClass (M ↪ₛ N) M N where
  coe f := f.toFun
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have : f = g := by
      ext t x
      exact congrFun (congrArg (fun φ => φ t) h) x
    cases this
    have : hf = hg := Subsingleton.elim _ _
    cases this
    rfl

def MSEmbedding.comp' {A : Fam base} {B : Fam base} {C : Fam base}
    (g : MSEmbedding B C) (f : MSEmbedding A B) : MSEmbedding A C :=
  {toFun := g.toFun ∘ₛ f.toFun,
    inj' := by
      intro t x y h;
      simp_all only [FamMap.comp_apply']
      apply f.inj'; apply g.inj'
      exact h
  }

/-- Constructs an embedding from a family of bundled embeddings. -/
def MSEmbedding.fromEmbeddings {M : Fam.{w} base} {N : Fam.{w'} base}
    (f : ∀ t, (M t) ↪ (N t)) : M ↪ₛ N :=
  ⟨ ⟨fun t => (f t : M t → N t)⟩ , (fun t => (f t).inj') ⟩

/-- A many-sorted equivalence is a family of bijections, one for each sort. -/
structure MSEquiv (M : Fam base) (N : Fam base) where
  /-- The family of forward functions. -/
  toFun : M →ₛ N
  /-- The family of inverse functions. -/
  invFun: N →ₛ M
  /-- The proof that `invFun` is a left inverse to `toFun` for each sort. -/
  left_inv' : ∀ t, Function.LeftInverse (invFun t) (toFun t)
  /-- The proof that `invFun` is a right inverse to `toFun` for each sort. -/
  right_inv' : ∀ t, Function.RightInverse (invFun t) (toFun t)

notation:25 A  " ≃ₛ " B  => MSEquiv A B

/-- Constructs an MSEquiv from a family of Equivs -/
def MSEquiv.fromEquivs {M : Fam.{w} base} {N : Fam.{w'} base}
    (f : ∀ t, (M t) ≃ (N t)) : M ≃ₛ N :=
 ⟨ ⟨fun t => (f t : M t → N t)⟩,
  ⟨fun t => ((f t).symm : N t → M t)⟩,
  (fun t => (f t).left_inv),
  (fun t => (f t).right_inv) ⟩

/-- Function coercion for MSEquiv -/
instance : FamMapClass (M ≃ₛ N) M N where
  coe := fun f => f.toFun
  coe_injective :=
   by
    rintro ⟨f, g, L, R⟩ ⟨f', g', L', R'⟩ h
    have : f = f' := by
      ext t x
      exact congrFun (congrArg (fun φ => φ t) h) x
    have : g = g' := by
      ext t y
      have hF_t : f t = f' t := congrArg (fun φ => φ t) this
      have L_t : Function.LeftInverse (g t) (f t) := L t
      have R'_t : Function.RightInverse (g' t) (f' t) := R' t
      calc
        g t y
            = g t (f' t (g' t y)) := by
                rw [← (R'_t y).symm]
        _   = g' t y := by
                simpa only [hF_t] using L_t (g' t y)
    cases this; cases this
    have : L = L' := Subsingleton.elim _ _
    have : R = R' := Subsingleton.elim _ _
    cases this; cases this
    rfl

@[ext]
theorem MSEquiv.ext {M : Fam base} {N : Fam base}
    {e₁ e₂ : M ≃ₛ N}
    (h : ∀ t, e₁.toFun t = e₂.toFun t) : e₁ = e₂ := by
  cases e₁ with
  | mk to₁ inv₁ left₁ right₁ =>
    cases e₂ with
    | mk to₂ inv₂ left₂ right₂ =>
      have hF : to₁ = to₂ := by
        ext t; simp_all only
      have hI : inv₁ = inv₂ := by
        ext t y
        have hF_t : to₁ t = to₂ t := congrArg (fun φ => φ t) hF
        have L₁ : Function.LeftInverse (inv₁ t) (to₁ t) := left₁ t
        have R₂ : Function.RightInverse (inv₂ t) (to₂ t) := right₂ t
        calc
          inv₁ t y
              = inv₁ t (to₂ t (inv₂ t y)) := by
                  rw [← (R₂ y).symm]
          _   = inv₂ t y := by
                  simpa only [hF_t] using L₁ (inv₂ t y)
      cases hF; cases hI
      have : left₁ = left₂ := Subsingleton.elim _ _
      have : right₁ = right₂ := Subsingleton.elim _ _
      cases this; cases this
      rfl

variable {M} {N}
/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm]
protected def MSEquiv.symm (e : M ≃ₛ N) : MSEquiv N M :=
  ⟨e.invFun, e.toFun, e.right_inv', e.left_inv'⟩

namespace MSEquiv

def refl {M : Fam base} : MSEquiv M M where
  toFun     := FamMap.idₛ
  invFun    := FamMap.idₛ
  left_inv' := by intro t x; rfl
  right_inv' := by intro t x; rfl

def toEquiv (e : MSEquiv M N) (s : base) : M s ≃ N s :=
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
  ∀ {s : base}, e₁.trans e₂ s = (e₂.toFun ∘ₛ e₁.toFun) s := by
  intro s
  rfl


/-- Helper simp lemma for applying MSEquiv inverse on left -/
@[simp] lemma inv_to (e : M ≃ₛ N) (t : base) (x : M t) :
    e.invFun t (e.toFun t x) = x :=
  (e.left_inv' t) x

/-- Helper simp lemma for applying MSEquiv inverse on right -/
@[simp] lemma to_inv (e : M ≃ₛ N) (t : base) (y : N t) :
    e.toFun t (e.invFun t y) = y :=
  (e.right_inv' t) y

/-- The forward function of the inverse is the inverse function. -/
@[simp] lemma symm_toFun (e : M ≃ₛ N) : e.symm.toFun = e.invFun := rfl

/-- The inverse function of the inverse is the forward function. -/
@[simp] lemma symm_invFun (e : M ≃ₛ N) : e.symm.invFun = e.toFun := rfl

/-- Applying symm.toFun then toFun gives the identity. -/
@[simp] lemma symm_toFun_toFun (e : M ≃ₛ N) (t : base) (x : M t) :
    e.symm.toFun t (e.toFun t x) = x :=
  e.inv_to t x

/-- Applying toFun then symm.toFun gives the identity. -/
@[simp] lemma toFun_symm_toFun (e : M ≃ₛ N) (t : base) (y : N t) :
    e.toFun t (e.symm.toFun t y) = y :=
  e.to_inv t y

@[simp] lemma inv_comp (e : M ≃ₛ N) (t : base) :
    e.invFun t ∘ e.toFun t = id := by ext x; exact e.inv_to t x

@[simp] lemma to_comp (e : M ≃ₛ N) (t : base) :
    e.toFun t ∘ e.invFun t = id := by ext y; exact e.to_inv t y

@[simp] lemma inv_compₛ (e : M ≃ₛ N) :
    (e.invFun ∘ₛ e.toFun) = FamMap.idₛ (α := M) := by
  ext t x
  simp only [FamMap.comp_apply', inv_to, FamMap.idₛ_apply']

@[simp] lemma to_compₛ (e : M ≃ₛ N) :
    e.toFun ∘ₛ e.invFun = FamMap.idₛ (α := N) := by
  ext t x
  simp only [FamMap.comp_apply', to_inv, FamMap.idₛ_apply']

@[simp] lemma symm_comp_comp_symm {P : Fam base} (hmn : M ≃ₛ N) (hnp : N ≃ₛ P) :
    (hmn.symm.toFun ∘ₛ hnp.symm.toFun) ∘ₛ (hnp.toFun ∘ₛ hmn.toFun) = FamMap.idₛ (α := M) := by
  ext t x
  simp_all only [MSEquiv.symm, FamMap.comp_apply', inv_to, FamMap.idₛ_apply']

@[simp] lemma symm_comp_comp_symm' {t} {x} {P : Fam base} (hmn : M ≃ₛ N) (hnp : N ≃ₛ P) :
  hmn.symm.toFun t (hnp.symm.toFun t (hnp.toFun t (hmn.toFun t x))) = x := by
  simp_all only [MSEquiv.symm, inv_to]

def sumCongr {α₁ : Fam base} {α₂ : Fam base}
    {β₁ : Fam base} {β₂ : Fam base}
    (ea : α₁ ≃ₛ α₂) (eb : β₁ ≃ₛ β₂) : (α₁ ⊕ₛ β₁) ≃ₛ (α₂ ⊕ₛ β₂) :=
  MSEquiv.fromEquivs (fun s => (ea.toEquiv s).sumCongr (eb.toEquiv s))

end MSEquiv

end manySortedEmbeddings

/-- A class for dependent families of injective functions.
    Extends `FamMapClass` to provide a coercion to `FamMap`. -/
class InjectivePerSort
    (F : Type*) {base : outParam (Type*)}
    (M : outParam (Fam base)) (N : outParam (Fam base))
    extends FamMapClass F M N where
  inj' : ∀ (f : F) t, Function.Injective (FamMapClass.toFamMap f t)

instance {base : Type _} {M : Fam base} {N : Fam base} : InjectivePerSort (M ↪ₛ N) M N where
  toFamMapClass := inferInstance
  inj' := MSEmbedding.inj'

/-- Per-sort analogue of `EquivLike`: an element of `F` is a family of bijections,
one for each sort. Extends `FamMapClass` to provide a coercion to `FamMap`. -/
class PerSortEquivLike
    (F : Type*) {base : outParam (Type*)}
    (M : outParam (Fam base)) (N : outParam (Fam base))
    extends FamMapClass F M N where
  inv : F → (N →ₛ M)
  left_inv : ∀ f t, Function.LeftInverse (inv f t) (FamMapClass.toFamMap f t)
  right_inv : ∀ f t, Function.RightInverse (inv f t) (FamMapClass.toFamMap f t)

instance {base : Type _} {M : Fam base} {N : Fam base} : PerSortEquivLike (M ≃ₛ N) M N where
  toFamMapClass := inferInstance
  inv := MSEquiv.invFun
  left_inv := MSEquiv.left_inv'
  right_inv := MSEquiv.right_inv'

/-- A `PerSortEquivLike` is automatically `InjectivePerSort`. -/
instance (priority := 100) PerSortEquivLike.toInjectivePerSort
    {base : Type*} {F : Type*} {M : Fam base} {N : Fam base}
    [PerSortEquivLike F M N] : InjectivePerSort F M N where
  toFamMapClass := PerSortEquivLike.toFamMapClass
  inj' f t := (PerSortEquivLike.left_inv f t).injective

/-- Turn an element of a type `F` satisfying `PerSortEquivLike F M N` into an actual
`MSEquiv`. -/
@[coe]
def PerSortEquivLike.toEquiv {base : Type _} {F}
    {M : Fam base} {N : Fam base}
    [PerSortEquivLike F M N] (f : F) : M ≃ₛ N where
  toFun := FamMapClass.toFamMap f
  invFun := PerSortEquivLike.inv f
  left_inv' := PerSortEquivLike.left_inv f
  right_inv' := PerSortEquivLike.right_inv f

namespace PerSortEquivLike

variable {base : Type*} {F : Type*} {M : Fam base} {N : Fam base}
  [PerSortEquivLike F M N]

@[simp]
theorem apply_inv_apply (g : F) (s : base) (x : N s) : g s (inv g s x) = x := right_inv _ _ _

@[simp]
theorem inv_apply_apply (g : F) (s : base) (x : M s) : (inv g) s (g s x) = x := left_inv _ _ _

@[simp]
theorem inv_comp (g : F) :
    (inv g) ∘ₛ (FamMapClass.toFamMap g) = FamMap.idₛ := by
  ext s x
  exact inv_apply_apply g s x

@[simp]
theorem comp_inv (g : F) :
    (FamMapClass.toFamMap g) ∘ₛ (inv g) = FamMap.idₛ := by
  ext s x
  exact apply_inv_apply g s x

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
