import ProdExpr.SortedTuple
import Mathlib.SetTheory.Cardinal.Basic

/-
Based on the corresponding Mathlib file Mathlib\ModelTheory\Syntax.lean
which was authored by 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn,
and is released under the Apache 2.0 license.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/

universe u v u' v' w w' z z'
open Cardinal

namespace MSFirstOrder
open Signature

section LanguageDefs
@[ext]
structure MSLanguage (S : Type z) where
  Functions : Signature S → S → Type u
  Relations : Signature S → Type v

namespace MSLanguage

variable {S : Type z}
variable (L : MSLanguage.{u, v, z} S)

/-- A language is relational when it has no function symbols. -/
abbrev IsRelational : Prop := ∀ σ t, IsEmpty (L.Functions σ t)

/-- A language is algebraic when it has no relation symbols. -/
abbrev IsAlgebraic : Prop := ∀ σ, IsEmpty (L.Relations σ)

@[simp] protected def empty : MSLanguage S :=
  ⟨fun _ _ => Empty, fun _ => Empty⟩

lemma Empty_relations_imp_algebraic (L : MSLanguage S)
  (h : ∀ σ, L.Relations σ = Empty) : IsAlgebraic L :=
  fun σ => by rw [h σ]; infer_instance

lemma Empty_functions_imp_relational (L : MSLanguage S)
  (h : ∀ σ t, L.Functions σ t = Empty) : IsRelational L :=
  fun σ t => by rw [h σ t]; infer_instance

instance : @IsAlgebraic.{0,0,z} S MSLanguage.empty :=
 by
  have it: (∀ (σ : Signature S), MSLanguage.empty.Relations σ = Empty)
  := by simp only [MSLanguage.empty, implies_true]
  exact Empty_relations_imp_algebraic _ it

instance : Inhabited (MSLanguage S) :=
  ⟨MSLanguage.empty⟩

/-- The sum of two languages with equal S consists of the disjoint union of
  their symbols over their S. -/
protected def sum (L' : (MSLanguage.{u', v', z} S)) : MSLanguage S :=
  ⟨fun σ => fun t => L.Functions σ t  ⊕ L'.Functions σ t, fun σ => L.Relations σ ⊕ L'.Relations σ⟩

/-- The type of constants in a given language. -/
protected abbrev Constants t :=
  L.Functions nil t

/-- The type of symbols in a given language. -/
abbrev Symbols :=
  (Σ σ t, L.Functions σ t) ⊕ (Σ σ, L.Relations σ)

/-- The cardinality of a language is the cardinality of its type of symbols. -/
def card : Cardinal :=
   #L.Symbols

variable {L} {L' : MSLanguage.{u', v', z} S}

--New: simplified this lemma by removing helpers and making Cardinal lifts more explicit in
--by adding z (universe level of Sorts) to the lifts on the right. They are redundant but useful for
--proving.
theorem card_eq_card_functions_add_card_relations :
    L.card =
      (Cardinal.sum fun σ => Cardinal.sum fun t => Cardinal.lift.{max v z, u} #(L.Functions σ t)) +
        (Cardinal.sum fun σ'  => Cardinal.lift.{max u z, v} #(L.Relations σ')) := by
  unfold card Symbols
  repeat rw[mk_sum, mk_sigma, lift_sum]
  simp_all only [mk_sigma, lift_sum]

instance isRelational_sum [L.IsRelational] [L'.IsRelational] : IsRelational (L.sum L') :=
  fun _ _ => instIsEmptySum

instance isAlgebraic_sum [L.IsAlgebraic] [L'.IsAlgebraic] : IsAlgebraic (L.sum L') :=
  fun _ => instIsEmptySum

instance isEmpty_empty : IsEmpty (@MSLanguage.empty S).Symbols := by
  simp only [MSLanguage.Symbols, isEmpty_sum, isEmpty_sigma]
  unfold MSLanguage.empty
  constructor
  · exact fun _ => inferInstance
  · exact inferInstance

@[simp]
theorem card_empty : (@MSLanguage.empty S).card = 0 := by
  unfold card
  simp only [MSLanguage.empty, mk_sum, mk_sigma, mk_eq_zero, sum_const, lift_uzero, lift_zero,
    mul_zero, lift_id, add_zero]

instance Countable.countable_functions [h : Countable L.Symbols] :
    Countable (Σ σ t, L.Functions σ t) :=
  @Function.Injective.countable _ _ h _ Sum.inl_injective

@[simp]
theorem card_functions_sum (σ : Signature S) (t : S) :
    #((L.sum L').Functions σ t) =
    (Cardinal.lift.{u'} #(L.Functions σ t) + Cardinal.lift.{u} #(L'.Functions σ t) : Cardinal) := by
  simp only [MSLanguage.sum, mk_sum]

@[simp]
theorem card_relations_sum (σ : Signature S) :
    #((L.sum L').Relations σ) =
      Cardinal.lift.{v'} #(L.Relations σ) + Cardinal.lift.{v} #(L'.Relations σ) := by
  simp only [MSLanguage.sum, mk_sum]

theorem card_sum {L' : MSLanguage.{u', v', z} S} :
    (L.sum L').card = Cardinal.lift.{max u' v'} L.card + Cardinal.lift.{max u v} L'.card := by
  unfold MSLanguage.sum
  simp only [card, Symbols, mk_sum, mk_sigma,sum_add_distrib', lift_add, lift_sum,
    lift_lift, add_assoc,
    add_comm (Cardinal.sum fun σ => Cardinal.sum fun i => (#(L'.Functions σ i)).lift)]

/-- Passes decidableEq instance through functions, cf. 1-sorted case -/
instance instDecidableEqFunctions {S : Type z} {f : Signature S → S → Type*}
    {R : Signature S → Type*} (σ : Signature S) (t : S) [DecidableEq (f σ t)] :
    DecidableEq ((⟨f, R⟩ : MSLanguage S).Functions σ t) := inferInstance

instance instDecidableEqRelations {S : Type z} {f : Signature S → S → Type*}
     {R : Signature S → Type*} (σ : Signature S) [DecidableEq (R σ)] :
    DecidableEq ((⟨f, R⟩ : MSLanguage S).Relations σ) := inferInstance

end MSLanguage
end LanguageDefs

namespace MSLanguage

section StructureDefs


@[ext]
class MSStructure {S} (L : MSLanguage S) (M : Fam.{w} S) where
funMap : ∀ {σ t}, L.Functions σ t → M [^] σ → M t := by
    exact fun {σ} => fun {t} => isEmptyElim
RelMap : ∀ {σ}, L.Relations σ → (M [^] σ)  → Prop := by
    exact fun {σ} => isEmptyElim


end StructureDefs

open MSStructure

section MsStructureHoms

variable {S : Type*} (L : MSLanguage S) (M : Fam.{w} S)


open MSStructure

@[reducible]
def Inhabited.trivialStructure {α : Fam S} [Inhabited S] [h : ∀ t, Inhabited (α t)] :
       L.MSStructure α := ⟨fun _ => fun _ =>  default , default⟩


variable (N : Fam.{w'} S) [L.MSStructure M] [L.MSStructure N]


/-- Homomorphisms between sorted first-order L-structures.
    In general it seems necessary to make σ and t explicit
    to avoid type inference issues, since structures M may map
    distinct S to the same type. -/
@[ext]
structure Hom where
  /-- The underlying function of a homomorphism of structures -/
  toFun : M →ₛ N
  /-- The homomorphism commutes with the interpretations of the function symbols -/
  map_fun' : ∀ {σ t} (f : L.Functions σ t) (x : M [^] σ ),
    toFun t (funMap f x) = funMap f (toFun <$>ₛ x) := by
    intros; trivial
  /-- The homomorphism sends related elements to related elements -/
  map_rel' : ∀ {σ } (r : L.Relations σ) (x), RelMap r x → RelMap r (toFun <$>ₛ x ) := by
    intros; trivial

@[inherit_doc]
scoped[MSFirstOrder] notation:25 A " →[" L "] " B => MSFirstOrder.MSLanguage.Hom L A B

/-- An embedding of first-order sorted structures is a many-sorted embedding that
commutes with the interpretations of functions and relations. -/
@[ext]
structure Embedding extends Fam.MSEmbedding M N where
  map_fun' : ∀ {σ t} (f : L.Functions σ t) (x),
    toFun t (funMap f x) = funMap f (toFun <$>ₛ x) := by
      intros; trivial
  map_rel' : ∀ {σ} (r : L.Relations σ) (x),
    RelMap r (toFun <$>ₛ x) ↔ RelMap r x := by
      intros; trivial

/- An embedding of first-order sorted structures. -/
@[inherit_doc]
scoped[MSFirstOrder] notation:25 A " ↪[" L "] " B => MSFirstOrder.MSLanguage.Embedding L A B

--For example:  variable (φ : M ↪[L] N)

/-- An equivalence of first-order sorted structures is a many-sorted equivalence that
commutes with the interpretations of functions and relations. -/
structure Equiv extends Fam.MSEquiv M N where
  map_fun' : ∀ (σ t) (f : L.Functions σ t) (x),
    toFun t (funMap f x) = funMap f (toFun <$>ₛ x) := by
      intros; trivial
  map_rel' : ∀ (σ) (r : L.Relations σ) (x),
    RelMap r (toFun <$>ₛ x ) ↔ RelMap r x := by
      intros; trivial

/-- The ext theorem for Equiv only needs to check equality of toFun -/
@[ext]
theorem Equiv.ext {L : MSLanguage S}
    [L.MSStructure M] [L.MSStructure N]
    {e₁ e₂ : Equiv L M N}
    (h : ∀ t, e₁.toFun t = e₂.toFun t) : e₁ = e₂ := by
  cases e₁ with
  | mk a hf hr =>
    cases e₂ with
    | mk a' hf' hr' =>
      -- MSEquiv bases are equal by ext lemma
      have hMS : a = a' := by
        ext t x
        exact congr (h t) (rfl)
      have hF: hf = hMS ▸ hf' := by rfl
      have hR: hr = hMS ▸ hr' := by rfl
      congr

@[inherit_doc]
scoped[MSFirstOrder] notation:25 A " ≃[" L "] " B => MSFirstOrder.MSLanguage.Equiv L A B

--For example:  variable (φ : M ≃[L] N)
variable {L M N} {P : Fam S}

/-- Interpretation of a constant symbol -/
@[coe]
def constantMap {t} (c : L.Constants t) : M t := funMap c default

instance {t} : CoeTC (L.Constants t) (M t) :=
  ⟨constantMap⟩

theorem funMap_eq_coe_constants {t} {c : L.Constants t} {xs : nil.Interpret M} : funMap c xs = c :=
  congr rfl (Unique.eq_default xs)

example {α : Type} [Unique α] (x : α) : x = default := Unique.eq_default x

/-- Given a language with a nonempty type of constants, any structure will be nonempty. This cannot
  be a global instance, because `L` becomes a metavariable. -/
theorem nonempty_of_nonempty_constants {t} [h : Nonempty (L.Constants t)] : Nonempty (M t):=
  h.map (↑)

/-- `HomClass L F M N` states that `F` is a type of `L`-homomorphisms. You should extend this
  typeclass when you extend `MSFirstOrder.MSLanguage.Hom`.
  This is a modified version of the one-sorted case where the typeclass assumption
  `[FunLike F L M]` is replaced with `[FamMapClass F M N]`. This
  means that an element φ of F can be coerced to a function which maps S `t` to functions
  `M t → N t`. -/
class HomClass (L : outParam (MSLanguage S)) (F : Type*) (M : (Fam S)) (N : outParam (Fam S))
  [L.MSStructure M] [L.MSStructure N] extends Fam.FamMapClass F M N where

  map_fun : ∀ (φ : F) {σ t} (f : L.Functions σ t) (x : M [^] σ ),
               φ t (funMap f x) = funMap f (φ <$>ₛ x)

  map_rel : ∀ (φ : F) {σ} (r : L.Relations σ) (x : M [^] σ ),
              RelMap r x → RelMap r (φ <$>ₛ x : N [^] σ)

/-- `StrongHomClass L F M N` states that `F` is a type of `L`-homomorphisms which preserve
  relations in both directions. -/
class StrongHomClass (L : outParam (MSLanguage S)) (F : Type*)
    (M : outParam (Fam S)) (N : outParam (Fam S))
    [L.MSStructure M] [L.MSStructure N] extends Fam.FamMapClass F M N where

  map_fun : ∀ (φ : F) {σ t} (f : L.Functions σ t) (x : M [^] σ ),
              φ t (funMap f x) = funMap f (φ <$>ₛ x)

  map_rel : ∀ (φ : F) {σ} (r : L.Relations σ) (x : M [^] σ ),
              RelMap r (φ <$>ₛ x : N[^]σ) ↔ RelMap r x

/-- `StrongEquivHomClass L F M N` packages a strong hom class together with per-sort inverses.
The inverse data is tied to the same underlying `FamMapClass` as `StrongHomClass`,
which avoids map-coercion diamonds between separate classes. -/
class StrongEquivHomClass (L : outParam (MSLanguage S)) (F : Type*)
    (M : outParam (Fam S)) (N : outParam (Fam S))
    [L.MSStructure M] [L.MSStructure N] extends StrongHomClass L F M N where
  inv : F → (N →ₛ M)
  left_inv : ∀ f t, Function.LeftInverse (inv f t) ((toFamMapClass.toFamMap f) t)
  right_inv : ∀ f t, Function.RightInverse (inv f t) ((toFamMapClass.toFamMap f) t)

@[reducible]
def StrongEquivHomClass.toPerSortEquivLike
    {S : Type*} {L : MSLanguage S} {M N : Fam S} {F : Type*}
    [L.MSStructure M] [L.MSStructure N] [StrongEquivHomClass L F M N] :
    Fam.PerSortEquivLike F M N where
  toFamMapClass := StrongHomClass.toFamMapClass
  inv := StrongEquivHomClass.inv
  left_inv := StrongEquivHomClass.left_inv
  right_inv := StrongEquivHomClass.right_inv

namespace StrongEquivHomClass

variable {F : Type*} [StrongEquivHomClass L F M N]

@[simp]
theorem apply_inv_apply (g : F) (s : S) (x : N s) :
    g s (StrongEquivHomClass.inv g s x) = x := by
  simpa using (StrongEquivHomClass.right_inv g s x)

@[simp]
theorem inv_apply_apply (g : F) (s : S) (x : M s) :
    (StrongEquivHomClass.inv g) s (g s x) = x := by
  simpa using (StrongEquivHomClass.left_inv g s x)

@[simp]
theorem inv_comp (g : F) :
    (StrongEquivHomClass.inv g) ∘ₛ (Fam.FamMapClass.toFamMap g) = Fam.FamMap.idₛ := by
  ext s x
  exact inv_apply_apply g s x

@[simp]
theorem comp_inv (g : F) :
    (Fam.FamMapClass.toFamMap g) ∘ₛ (StrongEquivHomClass.inv g) = Fam.FamMap.idₛ := by
  ext s x
  exact apply_inv_apply g s x

theorem apply_inv_apply_fun (g : F) :
    (fun s => (Fam.FamMapClass.toFamMap g) s ∘ (StrongEquivHomClass.inv g) s) = fun _ => id := by
  funext s
  funext x
  change ((Fam.FamMapClass.toFamMap g) s) ((StrongEquivHomClass.inv g) s x) = x
  exact StrongEquivHomClass.right_inv g s x

theorem inv_apply_apply_fun (g : F) :
    (fun s => (StrongEquivHomClass.inv g) s ∘ (Fam.FamMapClass.toFamMap g) s) = fun _ => id := by
  funext s
  funext x
  change ((StrongEquivHomClass.inv g) s) ((Fam.FamMapClass.toFamMap g) s x) = x
  exact StrongEquivHomClass.left_inv g s x

end StrongEquivHomClass

instance (priority := 100) StrongHomClass.homClass {F : Type*} [L.MSStructure M]
    [L.MSStructure N] [StrongHomClass L F M N] : HomClass L F M N where
  toFamMapClass := StrongHomClass.toFamMapClass
  map_fun := StrongHomClass.map_fun
  map_rel φ _ R x := (StrongHomClass.map_rel φ R x).2

/-- Not an instance to avoid a loop. -/
@[reducible]
def HomClass.strongHomClassOfIsAlgebraic [L.IsAlgebraic] {F M N} [L.MSStructure M]
    [L.MSStructure N] [HomClass L F M N] :
    StrongHomClass L F M N where
  toFamMapClass := HomClass.toFamMapClass
  map_fun := HomClass.map_fun
  map_rel _ _ := isEmptyElim

@[simp]
theorem HomClass.map_constants {F M N t} [m : L.MSStructure M] [n : L.MSStructure N]
    [h : HomClass L F M N]
    (φ : F) (c : L.Constants t) : (φ t) c  = c  :=
    (HomClass.map_fun φ c default).trans (congr rfl rfl)

attribute [simp] HomClass.map_fun HomClass.map_rel StrongHomClass.map_fun StrongHomClass.map_rel

/-- Any element of a `HomClass` can be realized as a multisorted first_order homomorphism. -/
@[simps] def HomClass.toHom {F M N} [L.MSStructure M] [L.MSStructure N]
    [HomClass L F M N] : F → M →[L] N := fun φ =>
  ⟨φ, HomClass.map_fun φ, HomClass.map_rel φ⟩


attribute [inherit_doc MSFirstOrder.MSLanguage.Hom.map_fun']
  MSFirstOrder.MSLanguage.Embedding.map_fun' MSFirstOrder.MSLanguage.HomClass.map_fun
  MSFirstOrder.MSLanguage.StrongHomClass.map_fun MSFirstOrder.MSLanguage.Equiv.map_fun'

attribute [inherit_doc MSFirstOrder.MSLanguage.Hom.map_rel']
  MSFirstOrder.MSLanguage.Embedding.map_rel' MSFirstOrder.MSLanguage.HomClass.map_rel
  MSFirstOrder.MSLanguage.StrongHomClass.map_rel MSFirstOrder.MSLanguage.Equiv.map_rel'

namespace Hom

instance famMapClass : Fam.FamMapClass (M →[L] N) M N where
  coe φ := φ.toFun
  coe_injective' := by
    intro f g h
    ext t x
    exact congrFun (congrFun h t) x

instance homClass : HomClass L (M →[L] N) M N where
  toFamMapClass := inferInstance
  map_fun := map_fun'
  map_rel := map_rel'

instance [L.IsAlgebraic] : StrongHomClass L (M →[L] N) M N :=
  HomClass.strongHomClassOfIsAlgebraic

@[simp]
theorem toFun_eq_coe {t} {f : M →[L] N} : f.toFun t = (f t : M t → N t) :=
  rfl

theorem map_fun (φ : M →[L] N) {σ t} (f : L.Functions σ t) (x : M [^] σ ) :
    φ t (funMap f x) = funMap f (φ <$>ₛ x) :=
  HomClass.map_fun φ f x

theorem map_constants {t} (φ : M →[L] N) (c : L.Constants t) : (φ t) c = c :=
  HomClass.map_constants φ c

theorem map_rel (φ : M →[L] N) {σ} (r : L.Relations σ) (x : M [^] σ ) :
    RelMap r x → RelMap r (φ <$>ₛ x) :=
  HomClass.map_rel φ r x

end Hom

end MsStructureHoms

section IdHom

namespace Hom
open MSStructure Fam

variable {S : Type z} (L : MSLanguage S) (M : Fam.{w} S) [L.MSStructure M]

/-- The identity map from a structure to itself. -/
@[refl]
def id : M →[L] M where
  toFun := Fam.FamMap.idₛ
  map_fun' := by
    intro _ _ _ xs
    simp only [Fam.FamMap.idₛ_apply', Interpret.map_id]
  map_rel' := by
    intro  _ _ xs r
    simp_all only [Interpret.map_id]

variable {L} {M}

instance : Inhabited (M →[L] M) :=
  ⟨id L M⟩

@[simp]
theorem id_apply {t} (x : M t) : id L M t x = x :=
  rfl

end Hom

end IdHom

section CompHom

open MSStructure

namespace Hom
variable {S : Type z} {L : MSLanguage S}
          {M : Fam.{w} S} [L.MSStructure M]
          {N : Fam.{w'} S} [L.MSStructure N]
          {P : Fam S} [L.MSStructure P] {Q : Fam S} [L.MSStructure Q]

/-- Composition of first-order homomorphisms. -/
@[trans]
def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P where
  toFun := hnp.toFun ∘ₛ hmn.toFun
  map_fun' := by
    intro _ _ _ xs
    simp_all only [Fam.FamMap.comp_apply', Interpret.comp_map, toFun_eq_coe, map_fun]
    rfl
  map_rel' r xs h :=  by
    rw [Interpret.comp_map]
    exact (map_rel _ _ _ (map_rel _ _ _ h))

@[simp]
theorem comp_apply {t} (g : N →[L] P) (f : M →[L] N) (x : M t) : g.comp f t x = g t (f t x) :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_id (f : M →[L] N) : f.comp (id L M) = f :=
  rfl

@[simp]
theorem id_comp (f : M →[L] N) : (id L N).comp f = f :=
  rfl

end Hom

end CompHom

section Embeddings

variable {S : Type z} {L : MSLanguage S}
          {M : Fam.{w} S} [L.MSStructure M]
          {N : Fam.{w'} S} [L.MSStructure N]

namespace Embedding
open Fam

instance famMapClass : Fam.FamMapClass (M ↪[L] N) M N where
  coe f := f.toFun
  coe_injective' := by
    intro f g h
    ext t x
    exact congrFun (congrFun h t) x

instance : Fam.InjectivePerSort (M ↪[L] N) M N where
  toFamMapClass := inferInstance
  inj' f t := f.inj' t

/-- The pointwise (single-sorted) embedding induced by a many-sorted embedding at sort `t`. -/
def atSort (φ : M ↪[L] N) (t : S) : (M t) ↪ (N t) :=
{ toFun := φ t
  inj'  := φ.inj' t }

@[simp] lemma atSort_apply (φ : M ↪[L] N) (t : S) (x : M t) :
  φ.atSort t x = φ t x := rfl

/-- Injectivity of `φ` at a given sort. -/
@[simp] lemma injective (φ : M ↪[L] N) (t : S) :
  Function.Injective (φ t) :=
φ.inj' t

/-- Pointwise cancellation at a sort. -/
@[simp] lemma at_eq_iff (φ : M ↪[L] N) {t : S} {x y : M t} :
  φ t x = φ t y ↔ x = y :=
by
  constructor
  · intro h; exact φ.inj' t h
  · intro h; simp only [h]

instance strongHomClass : StrongHomClass L (M ↪[L] N) M N where
  toFamMapClass := inferInstance
  map_fun := map_fun'
  map_rel := map_rel'

theorem map_fun (φ : M ↪[L] N) {t : S} {σ : Signature S}
    (f : L.Functions σ t) (x : M [^] σ) :
    φ t (funMap f x) = funMap f (φ <$>ₛ x) :=
  HomClass.map_fun φ f x

theorem map_constants {t} (φ : M ↪[L] N) (c : L.Constants t) : φ t c = c :=
  HomClass.map_constants φ c

theorem map_rel (φ : M ↪[L] N) {σ : Signature S} (r : L.Relations σ) (x : M [^] σ) :
    RelMap r (φ <$>ₛ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- A first-order embedding is also a first-order homomorphism. -/
def toHom : (M ↪[L] N) → M →[L] N :=
  HomClass.toHom

@[simp]
theorem coe_toHom {t} {f : M ↪[L] N} : (f.toHom t : M t → N t) = f t :=
  rfl

theorem coe_injective : @Function.Injective (M ↪[L] N) ((t: S) -> (M t → N t)) (↑)
  | f, g, h => by
    cases f
    cases g
    congr
    ext t x
    exact congr_fun (congr_arg (fun f => f t) h) x

theorem toHom_injective : @Function.Injective (M ↪[L] N) (M →[L] N) (·.toHom) := by
  intro f f' h
  ext t x
  exact congr_fun (congr_arg (fun f => f t) h) x

@[simp]
theorem toHom_inj {f g : M ↪[L] N} : f.toHom = g.toHom ↔ f = g :=
  ⟨fun h ↦ toHom_injective h, fun h ↦ congr_arg (·.toHom) h⟩

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simp]
def ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : ∀ t,  Function.Injective (f t)) : M ↪[L] N :=
  { f with
    inj' := hf
    map_rel' := fun {_} r x => StrongHomClass.map_rel f r x }

@[simp]
theorem coeFn_ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : ∀ t,  Function.Injective (f t)):
    (ofInjective hf : (∀ t, M t → N t)) = f := by
  ext t x
  simp_all only [ofInjective]
  rfl

@[simp]
theorem ofInjective_toHom [L.IsAlgebraic] {f : M →[L] N} (hf : ∀ t,  Function.Injective (f t)) :
    (ofInjective hf).toHom = f := by
  ext
  simp_all only [ofInjective, Hom.toFun_eq_coe, coe_toHom]
  rfl

variable (L) (M)

/-- The identity embedding from a structure to itself. -/
@[refl]
def refl : M ↪[L] M where
  toFun := FamMap.idₛ
  inj' := by
    intro t x y h
    simpa only [id_eq] using h
  map_fun' := by
    intros σ t f x
    simp_all only [FamMap.idₛ_apply', Interpret.map_id]
  map_rel' := by
    intros σ r x
    simp_all only [Interpret.map_id]

variable {L} {M}

instance : Inhabited (M ↪[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (t : S) (x : M t) : refl L M t x = x :=
  rfl

variable {P : Fam S} [L.MSStructure P] {Q : Fam S} [L.MSStructure Q]

/-- Composition of first-order Embeddings. -/
@[trans]
def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where
  toFun := hnp.toFun ∘ₛ hmn.toFun
  inj' := by
    intro t
    exact (hnp.injective t).comp (hmn.injective t)
  map_fun' := by
    intros σ s f x
    simp_all only [FamMap.comp_apply', Interpret.comp_map, map_fun']
  map_rel' := by
    intros σ r x
    rw [Interpret.comp_map]
    exact Iff.trans (hnp.map_rel' r (hmn.toFun <$>ₛ x)) (hmn.map_rel' r x)

@[simp]
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) t (x : M t) : g.comp f t x = g t (f t x) :=
  rfl

/-- Composition of first-order Embeddings is associative. -/
theorem comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

theorem comp_injective (h : N ↪[L] P) :
    Function.Injective (h.comp : (M ↪[L] N) →  (M ↪[L] P)) := by
  intro f g hfg
  ext t x
  exact (h.injective t) (by
    simpa only [at_eq_iff, comp_apply] using congr_fun (congr_arg (fun φ => φ t) hfg) x)


@[simp]
theorem comp_inj (h : N ↪[L] P) (f g : M ↪[L] N) : h.comp f = h.comp g ↔ f = g :=
  ⟨fun eq ↦ h.comp_injective eq, congr_arg h.comp⟩

theorem toHom_comp_injective (h : N ↪[L] P) :
    Function.Injective (h.toHom.comp : (M →[L] N) →  (M →[L] P)) := by
  intro f g hfg
  ext t x
  apply (h.injective t)
  have hx := congr_fun (congr_arg (fun φ => φ t) hfg) x
  simpa only [Hom.toFun_eq_coe, at_eq_iff, Hom.comp_apply, coe_toHom] using hx

@[simp]
theorem toHom_comp_inj (h : N ↪[L] P) (f g : M →[L] N) : h.toHom.comp f = h.toHom.comp g ↔ f = g :=
  ⟨fun eq ↦ h.toHom_comp_injective eq, congr_arg h.toHom.comp⟩

@[simp]
theorem comp_toHom (hnp : N ↪[L] P) (hmn : M ↪[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl

@[simp]
theorem comp_refl (f : M ↪[L] N) : f.comp (refl L M) = f := DFunLike.coe_injective rfl

@[simp]
theorem refl_comp (f : M ↪[L] N) : (refl L N).comp f = f := DFunLike.coe_injective rfl

@[simp]
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

end Embedding

open Fam

/-- Any element of an injective `StrongHomClass` can be realized as a first_order embedding. -/
def StrongHomClass.toEmbedding
    {F M N}
    [L.MSStructure M] [L.MSStructure N]
    [StrongHomClass L F M N]
    (φ : F) (inj : ∀ t, Function.Injective (φ t)) : M ↪[L] N :=
  { toFun := FamMapClass.toFamMap φ
    inj' := inj
    map_fun' := fun f x => StrongHomClass.map_fun φ f x
    map_rel' := fun r x => StrongHomClass.map_rel φ r x }

@[simp] theorem StrongHomClass.toEmbedding_toFun
    {F M N}
    [L.MSStructure M] [L.MSStructure N]
    [StrongHomClass L F M N]
    (φ : F) (inj : ∀ t, Function.Injective (φ t)) :
    (StrongHomClass.toEmbedding (L := L) (M := M) (N := N) φ inj).toFun =
      FamMapClass.toFamMap φ := rfl

@[simp] theorem StrongHomClass.toEmbedding_apply
    {F M N}
    [L.MSStructure M] [L.MSStructure N]
    [StrongHomClass L F M N]
    (φ : F) (inj : ∀ t, Function.Injective (φ t)) (t) (x) :
    StrongHomClass.toEmbedding (L := L) (M := M) (N := N) φ inj t x = φ t x := rfl

end Embeddings

section Equivs
variable {S : Type z} {L : MSLanguage S}
          {M : Fam.{w} S} [L.MSStructure M]
          {N : Fam.{w'} S} [L.MSStructure N]

namespace Equiv

instance famMapClass : Fam.FamMapClass (M ≃[L] N) M N where
  coe f := f.toFun
  coe_injective' := by
    intro f g h
    apply MSLanguage.Equiv.ext
    intro t
    funext x
    exact congrFun (congrFun h t) x

/-- We can also do ext arguments at the sort level. -/
@[ext] theorem ext_sort
  {f g : M ≃[L] N} (h : ∀ t, f t = g t) : f = g :=
by
  apply ext
  intro t
  exact h t

/-- `M ≃[L] N` forms a per-sort equivalence-like structure. -/
instance : Fam.PerSortEquivLike (M ≃[L] N) M N where
  toFamMapClass := inferInstance
  inv f := f.invFun
  left_inv f t := f.left_inv' t
  right_inv f t := f.right_inv' t

instance : StrongEquivHomClass L (M ≃[L] N) M N where
  toFamMapClass := inferInstance
  map_fun := map_fun'
  map_rel := map_rel'
  inv f := f.invFun
  left_inv f t := f.left_inv' t
  right_inv f t := f.right_inv' t

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm]
def symm (φ : M ≃[L] N) : N ≃[L] M :=
  { toFun := φ.invFun
    invFun := φ.toFun
    left_inv' := φ.right_inv'
    right_inv' := φ.left_inv'
    map_fun' := by
      intro σ t f x
      -- Show the equality by applying φ.toFun t and using injectivity
      apply ((φ.left_inv' t).injective)
      -- After applying φ.toFun t to both sides we obtain two equal terms
      have h := φ.map_fun' σ t f (φ.invFun <$>ₛ x)
      -- Simplify the composed sorted tuple
      have hx : (φ.toFun <$>ₛ (φ.invFun <$>ₛ x)) = x := by
        have : (φ.toFun ∘ₛ φ.invFun) = Fam.FamMap.idₛ := by
          ext ; simp_all only [Fam.FamMap.comp_apply', Fam.MSEquiv.to_inv, Fam.FamMap.idₛ_apply']
        simp_all only [← Interpret.comp_map, Interpret.map_id]
      -- Right side (image of the target expression)
      have hRight : φ.toFun t (funMap f (φ.invFun <$>ₛ x)) = funMap f x := by
        simpa only [hx] using h
      -- Left side (image of the source expression)
      have hLeft : φ.toFun t (φ.invFun t (funMap f x)) = funMap f x := by
        simp only [Fam.MSEquiv.to_inv]
      -- Conclude by comparing the two images
      simp only [hLeft, hRight]
    map_rel' := by
      intro σ r x
      -- Start from φ.map_rel' applied to (φ.invFun <$>ₛ x)
      have h := φ.map_rel' σ r (φ.invFun <$>ₛ x)
      have hx : (φ.toFun <$>ₛ (φ.invFun <$>ₛ x)) = x := by
        rw [← Interpret.comp_map]
        simp only [Fam.MSEquiv.to_compₛ, Interpret.map_id]
      -- Rewrite to get RelMap r x ↔ RelMap r (φ.invFun <$>ₛ x)
      have h' : RelMap r x ↔ RelMap r (φ.invFun <$>ₛ x) := by
        simpa only [hx] using h
      -- Flip the equivalence for the inverse direction
      exact h'.symm }

theorem symm_bijective : Function.Bijective (symm : (M ≃[L] N) → (N ≃[L] M)) :=
by
  refine ⟨?inj, ?surj⟩
  · intro f g h
    -- h : symm f = symm g
    have h' := congrArg (symm (M:=N) (N:=M)) h
    -- simplify double symm
    have hf : symm (symm f) = f := by cases f; rfl
    have hg : symm (symm g) = g := by cases g; rfl
    simpa only [hf, hg] using h'
  · intro g
    refine ⟨symm g, ?_⟩
    have hg : symm (symm g) = g := by cases g; rfl
    simp only [symm]

@[simp]
theorem apply_symm_apply {t} (f : M ≃[L] N) (a : N t) : f t (f.symm t a) = a := by
  -- follows from the right inverse property of f
  exact f.right_inv' t a

@[simp]
theorem symm_apply_apply {t} (f : M ≃[L] N) (a : M t) : f.symm t (f t a) = a := by
  exact f.left_inv' t a

theorem map_fun {t : S} (φ : M ≃[L] N) {σ : Signature S}
    (f : L.Functions σ t) (x : M [^] σ) :
    φ t (funMap f x) = funMap f (φ <$>ₛ x) :=
  HomClass.map_fun φ f x

theorem map_constants {t : S} (φ : M ≃[L] N) (c : L.Constants t) : φ t c = c :=
  HomClass.map_constants φ c

theorem map_rel (φ : M ≃[L] N) {σ : Signature S} (r : L.Relations σ) (x : M [^] σ) :
    RelMap r (φ <$>ₛ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- A first-order equivalence is also a first-order embedding. -/
def toEmbedding : (M ≃[L] N) → M ↪[L] N :=
  fun φ => StrongHomClass.toEmbedding φ (fun t => (φ.left_inv' t).injective)

/-- A first-order equivalence is also a first-order homomorphism. -/
def toHom : (M ≃[L] N) → M →[L] N :=
  HomClass.toHom

@[simp]
theorem toEmbedding_toHom (f : M ≃[L] N) : f.toEmbedding.toHom = f.toHom :=
  by
    ext t x
    rfl

@[simp]
theorem coe_toHom {f : M ≃[L] N} :
    (f.toHom : (t: S) → (M t → N t)) = (f :(t: S) → (M t → N t)) := rfl

@[simp]
theorem coe_toEmbedding (f : M ≃[L] N) :
    (f.toEmbedding : (t: S) → (M t → N t)) = (f : (t: S) → (M t → N t)) := by
  funext t x
  rfl

theorem injective_toEmbedding : Function.Injective (toEmbedding : (M ≃[L] N) → M ↪[L] N) := by
  intro f g h
  apply ext_sort
  intro t
  funext x
  exact congrArg (fun e : M ↪[L] N => e t x) h

theorem coe_injective : @Function.Injective (M ≃[L] N) ((t: S) → (M t → N t)) (↑) :=
  DFunLike.coe_injective

theorem bijective {t} (f : M ≃[L] N) : Function.Bijective (f t) := by
  constructor
  · intro x y h
    have := congrArg (f.symm t) h
    simpa only [symm_apply_apply] using this
  · intro y
    refine ⟨f.symm t y, ?_⟩
    simp only [apply_symm_apply]

theorem injective {t} (f : M ≃[L] N) : Function.Injective (f t) :=
  (f.bijective).1

theorem surjective {t} (f : M ≃[L] N) : Function.Surjective (f t) :=
  (f.bijective).2

variable (L) (M)

/-- The identity equivalence from a structure to itself. -/
@[refl]
def refl : M ≃[L] M where
  toFun := Fam.FamMap.idₛ
  invFun := Fam.FamMap.idₛ
  left_inv' := by
    intro t x; rfl
  right_inv' := by
    intro t x; rfl
  map_fun' := by
    intros σ t f x
    rw [Interpret.map_id]
    rfl
  map_rel' := by
    intros σ r x
    rw [Interpret.map_id]


variable {L} {M}

instance : Inhabited (M ≃[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply {t} (x : M t) : refl L M t x = x := by simp only [refl]; rfl

variable {P : Fam S} [L.MSStructure P] {Q : Fam S} [L.MSStructure Q]

/-- Composition of first-order equivalences. -/
@[trans]
def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
{ toFun := hnp.toFun ∘ₛ hmn.toFun
  invFun := hmn.symm.toFun ∘ₛ hnp.symm.toFun
  left_inv' := by
    intro t x
    simp only [Fam.FamMap.comp_apply', symm, Fam.MSEquiv.inv_to]
  right_inv' := by
    intro t y
    simp only [Fam.FamMap.comp_apply', symm, Fam.MSEquiv.to_inv]
  map_fun' := by
    intro σ t f x
    calc
      hnp t (hmn t (funMap f x))
          = hnp t (funMap f (hmn <$>ₛ x)) := by simp only [map_fun]
      _   = funMap f (hnp <$>ₛ (hmn <$>ₛ x)) := by simp only [map_fun]
      _   = funMap f ((hnp ∘ₛ hmn.toFun) <$>ₛ x) := by
        rw[Interpret.comp_map]
        rfl
  map_rel' := by
    intro σ r x
    -- compose the equivalences from hnp and hmn
    have h₁ := hnp.map_rel' σ r (hmn.toFun <$>ₛ x)
    have h₂ := hmn.map_rel' σ r x
    rw[← Interpret.comp_map] at h₁
    rw[← h₂,← h₁]
    }

@[simp]
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (t) (x : M t) : g.comp f t x = g t (f t x) :=
  rfl

@[simp]
theorem comp_refl (g : M ≃[L] N) : g.comp (refl L M) = g :=
  rfl

@[simp]
theorem refl_comp (g : M ≃[L] N) : (refl L N).comp g = g :=
  rfl

@[simp]
theorem refl_toEmbedding : (refl L M).toEmbedding = Embedding.refl L M :=
  by
    ext t x
    rfl

@[simp]
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

theorem injective_comp (h : N ≃[L] P) :
    Function.Injective (h.comp : (M ≃[L] N) →  (M ≃[L] P)) := by
  intro f g hfg
  ext t x
  -- compare the images under h at sort t
  have hpoint := congrArg (fun e : M ≃[L] P => e t x) hfg
  -- use injectivity of h at sort t
  exact (h.injective ) (by simpa only [comp_apply] using hpoint
)


@[simp]
theorem comp_toHom (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl

@[simp]
theorem comp_toEmbedding (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toEmbedding = hnp.toEmbedding.comp hmn.toEmbedding :=
  by
    ext t x
    rfl

@[simp]
theorem self_comp_symm (f : M ≃[L] N) : f.comp f.symm = refl L N := by
  ext; rw [comp_apply, apply_symm_apply, refl_apply]

@[simp]
theorem symm_comp_self (f : M ≃[L] N) : f.symm.comp f = refl L M := by
  ext; rw [comp_apply, symm_apply_apply, refl_apply]

@[simp]
theorem symm_comp_self_toEmbedding (f : M ≃[L] N) :
    f.symm.toEmbedding.comp f.toEmbedding = Embedding.refl L M := by
  rw [← comp_toEmbedding, symm_comp_self, refl_toEmbedding]

@[simp]
theorem self_comp_symm_toEmbedding (f : M ≃[L] N) :
    f.toEmbedding.comp f.symm.toEmbedding = Embedding.refl L N := by
  rw [← comp_toEmbedding, self_comp_symm, refl_toEmbedding]

@[simp]
theorem symm_comp_self_toHom (f : M ≃[L] N) :
    f.symm.toHom.comp f.toHom = Hom.id L M := by
  rw [← comp_toHom, symm_comp_self, refl_toHom]

@[simp]
theorem self_comp_symm_toHom (f : M ≃[L] N) :
    f.toHom.comp f.symm.toHom = Hom.id L N := by
  rw [← comp_toHom, self_comp_symm, refl_toHom]

@[simp]
theorem comp_symm (f : M ≃[L] N) (g : N ≃[L] P) : (g.comp f).symm = f.symm.comp g.symm :=
  rfl

theorem comp_right_injective (h : M ≃[L] N) :
    Function.Injective (fun f ↦ f.comp h : (N ≃[L] P) → (M ≃[L] P)) := by
  intro f g hfg
  convert (congr_arg (fun r : (M ≃[L] P) ↦ r.comp h.symm) hfg) <;>
    rw [comp_assoc, self_comp_symm, comp_refl]

@[simp]
theorem comp_right_inj (h : M ≃[L] N) (f g : N ≃[L] P) : f.comp h = g.comp h ↔ f = g :=
  ⟨fun eq ↦ h.comp_right_injective eq, congr_arg (fun (r : N ≃[L] P) ↦ r.comp h)⟩

end Equiv

/-- Any element of a bijective `StrongHomClass`
  can be realized as a sorted first_order isomorphism. -/
def StrongHomClass.toEquiv
    {F} {M N : Fam S}
    [L.MSStructure M] [L.MSStructure N]
    [StrongHomClass L F M N]
    (φ : F)
    (inv : N →ₛ M)
    (left_inv : ∀ t, Function.LeftInverse (inv t) (φ t))
    (right_inv : ∀ t, Function.RightInverse (inv t) (φ t)) :
    M ≃[L] N :=
  { toFun := Fam.FamMapClass.toFamMap φ
    invFun := inv
    left_inv' := left_inv
    right_inv' := right_inv
    map_fun' := fun _ _ f x => StrongHomClass.map_fun φ f x
    map_rel' := fun _ r x => StrongHomClass.map_rel φ r x }

@[simp] theorem StrongHomClass.toEquiv_toFun
    {F} {M N : Fam S}
    [L.MSStructure M] [L.MSStructure N]
    [StrongHomClass L F M N]
    (φ : F) (inv : N →ₛ M)
    (left_inv : ∀ t, Function.LeftInverse (inv t) (φ t))
    (right_inv : ∀ t, Function.RightInverse (inv t) (φ t)) :
    (StrongHomClass.toEquiv (L := L) (M := M) (N := N) φ inv left_inv right_inv).toFun =
      Fam.FamMapClass.toFamMap φ := rfl

@[simp] theorem StrongHomClass.toEquiv_apply
    {F} {M N : Fam S}
    [L.MSStructure M] [L.MSStructure N]
    [StrongHomClass L F M N]
    (φ : F) (inv : N →ₛ M)
    (left_inv : ∀ t, Function.LeftInverse (inv t) (φ t))
    (right_inv : ∀ t, Function.RightInverse (inv t) (φ t))
    (t) (x) :
    StrongHomClass.toEquiv (L := L) (M := M) (N := N) φ inv left_inv right_inv t x = φ t x := rfl

end Equivs

section SumStructure

variable {S : Type z} (L₁ L₂ : MSLanguage S) (S') [L₁.MSStructure S'] [L₂.MSStructure S']

instance sumStructure : (L₁.sum L₂).MSStructure S' where
  funMap := by
    intro σ t f
    cases f with
    | inl f1 =>
        intro x
        exact funMap (L:=L₁) f1 x
    | inr f2 =>
        intro x
        exact funMap (L:=L₂) f2 x
  RelMap := by
    intro σ r
    cases r with
    | inl r1 =>
        intro x
        exact RelMap (L:=L₁) r1 x
    | inr r2 =>
        intro x
        exact RelMap (L:=L₂) r2 x

variable {L₁ L₂ : MSLanguage S} {S'} [L₁.MSStructure S'] [L₂.MSStructure S']

@[simp]
theorem funMap_sumInl {t : S} {σ : Signature S} (f : L₁.Functions σ t) :
    @funMap S (L₁.sum L₂) S' _ σ t (Sum.inl f) = funMap f :=
  rfl

@[simp]
theorem funMap_sumInr {t : S} {σ : Signature S} (f : L₂.Functions σ t) :
    @funMap S (L₁.sum L₂) S' _ σ t (Sum.inr f) = funMap f :=
  rfl

@[simp]
theorem relMap_sumInl {σ : Signature S} (R : L₁.Relations σ) :
    @RelMap S (L₁.sum L₂) S' _ σ (Sum.inl R) = RelMap R :=
  rfl

@[simp]
theorem relMap_sumInr {σ : Signature S} (R : L₂.Relations σ) :
    @RelMap S (L₁.sum L₂) S' _ σ (Sum.inr R) = RelMap R :=
  rfl

end SumStructure

section Empty

variable {S : Type z} {L : MSLanguage S} {M : Fam.{w} S} [L.MSStructure M]

/-- Any type can be made uniquely into a structure over the empty language. -/
@[reducible]
def emptyStructure : MSLanguage.empty.MSStructure M where
  funMap := by
    intro σ t f
    cases f
  RelMap := by
    intro σ r
    cases r

instance : Unique (MSLanguage.empty.MSStructure M) :=
{ default := emptyStructure
  uniq := by
    intro S
    -- two structures over the empty language are equal since their data is vacuous
    refine MSStructure.ext ?_ ?_
    · funext σ t f x; cases f
    · funext σ r x; cases r }

variable {N : Fam.{w'} S} [L.MSStructure N]
        [MSLanguage.empty.MSStructure M] [MSLanguage.empty.MSStructure N]

instance (priority := 100) strongHomClassEmpty {F} [Fam.FamMapClass F M N] :
    StrongHomClass MSLanguage.empty F M N where
  toFamMapClass := inferInstance
  map_fun := by
    intro φ σ t f x
    cases f
  map_rel := by
    intro φ σ r x
    cases r

@[simp]
theorem empty.nonempty_embedding_iff :
    Nonempty (M ↪[MSLanguage.empty] N) ↔
      ∀ t, Cardinal.lift.{w', w} #(M t) ≤ Cardinal.lift #(N t) :=
  by
  constructor
  · intro h t
    rcases h with ⟨φ⟩
    -- Injectivity at sort t
    have hInj : Function.Injective (φ t) := φ.injective t
    -- Lift the cardinal inequality
    have hNe: Nonempty (M t ↪ N t) := ⟨⟨φ t, hInj⟩⟩
    exact Cardinal.lift_mk_le'.2 hNe
  · intro h
    have hFamInj: ∀ (t: S), Nonempty (M t ↪ N t) := by
      intro t; simp only [Cardinal.lift_mk_le'.1 (h t)]
    have hMSE: Nonempty (Fam.MSEmbedding M N) := by
      apply Nonempty.map Fam.MSEmbedding.fromEmbeddings
      exact ⟨fun t => Classical.choice (hFamInj t)⟩
    exact (Nonempty.map (fun e => StrongHomClass.toEmbedding
      (L := MSLanguage.empty) (M := M) (N := N) e (fun t => e.inj' t)) hMSE)

@[simp]
theorem empty.nonempty_equiv_iff :
    Nonempty (M ≃[MSLanguage.empty] N) ↔
      ∀ t, Cardinal.lift.{w', w} #(M t) = Cardinal.lift #(N t) :=
  by
  constructor
  · intro h t
    rcases h with ⟨φ⟩
    -- Bijectivity at sort t
    have hBij : Function.Bijective (φ t) := φ.bijective
    -- Lift the cardinal equality
    have hNe: Nonempty (M t ≃ N t) :=
      ⟨⟨φ t, φ.invFun t, φ.left_inv' t, φ.right_inv' t⟩⟩
    exact Cardinal.lift_mk_eq'.2 hNe
  · intro h
    have hMSE: Nonempty (Fam.MSEquiv M N) := by
      apply Nonempty.map Fam.MSEquiv.fromEquivs
      exact ⟨fun t => Classical.choice (Cardinal.lift_mk_eq'.1 (h t))⟩
    exact (Nonempty.map (fun e => StrongHomClass.toEquiv
      (L := MSLanguage.empty) (M := M) (N := N) e e.invFun e.left_inv' e.right_inv') hMSE)

/-- Makes a `MSLanguage.empty.Hom` out of any function. -/
@[simps]
def _root_.Function.MSemptyHom (f : M →ₛ N) : M →[MSLanguage.empty] N where toFun := f
end Empty

section InducedStructure
namespace Equiv

open MSFirstOrder.MSLanguage.MSStructure

variable {S : Type z} {L : MSLanguage S} {M : Fam.{w} S} {N : Fam.{w'} S}
variable [L.MSStructure M]

@[reducible]
def inducedStructure (e : Fam.MSEquiv M N) : L.MSStructure N :=
{ funMap := fun {σ} {t} (f : L.Functions σ t) (x : σ.Interpret N ) =>
    e t (funMap f (e.symm <$>ₛ x)),
  RelMap := fun {σ} (r : L.Relations σ) (x : σ.Interpret N) =>
    RelMap r (e.symm <$>ₛ x) }

/-- A bijection as a first-order isomorphism with the induced structure on the codomain. -/
def inducedStructureEquiv (e : M ≃ₛ N) : @MSLanguage.Equiv S L M N _ (inducedStructure e) := by
  letI S : L.MSStructure N := inducedStructure e
  exact
  { e with
    map_fun' := @fun σ t f x => by
      change e.toFun t (funMap f x) = e t (funMap f (e.invFun <$>ₛ (e.toFun <$>ₛ x)))
      have h : (e.invFun <$>ₛ (e.toFun <$>ₛ x)) = x := by
        ext s a
        simp only [Interpret.get_map]
        exact e.left_inv' s (Interpret.get x s a)
      rw [h]
      rfl
    map_rel' := @fun σ  r x => by
      change RelMap r (e.invFun <$>ₛ (e.toFun <$>ₛ x)) ↔ RelMap r x
      have h : (e.invFun <$>ₛ (e.toFun <$>ₛ x)) = x := by
        ext s a
        simp only [Interpret.get_map]
        exact e.left_inv' s (Interpret.get x s a)
      rw [h] }

@[simp]
theorem toEquiv_inducedStructureEquiv (e : M ≃ₛ N) :
    @MSLanguage.Equiv.toMSEquiv S L M N _ (inducedStructure e) (inducedStructureEquiv e) = e :=
  rfl

@[simp]
theorem toFun_inducedStructureEquiv (e : M ≃ₛ N) :
    DFunLike.coe (@inducedStructureEquiv S L M N _ e) = e :=
  rfl

@[simp]
theorem toFun_inducedStructureEquiv_Symm (e : M ≃ₛ N) :
    (by
    letI : L.MSStructure N := inducedStructure e
    exact (@inducedStructureEquiv S L M N _ e).symm.toFun) = (e.symm : N →ₛ M) :=
  rfl

end Equiv

end InducedStructure

end MSLanguage

end MSFirstOrder
