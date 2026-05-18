import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Metrizable.Basic
import LeanLCAExactChallenge.ExactCategory.Basic

/-!
The category of metrizable locally compact abelian groups used by the challenge.

Objects are bundled topological additive commutative groups that are locally
compact and metrizable.  Morphisms are continuous additive homomorphisms.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/-- Bundled metrizable locally compact abelian groups. -/
structure MetrizableLCA where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [topologicalAddGroup : IsTopologicalAddGroup carrier]
  [locallyCompactSpace : LocallyCompactSpace carrier]
  [metrizableSpace : TopologicalSpace.MetrizableSpace carrier]

attribute [instance] MetrizableLCA.addCommGroup MetrizableLCA.topologicalSpace
  MetrizableLCA.topologicalAddGroup MetrizableLCA.locallyCompactSpace
  MetrizableLCA.metrizableSpace

namespace MetrizableLCA

instance : CoeSort MetrizableLCA (Type u) where
  coe X := X.carrier

/-- Bundle an already-typed metrizable locally compact abelian group. -/
abbrev of (G : Type u) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [TopologicalSpace.MetrizableSpace G] : MetrizableLCA where
  carrier := G

/-- Morphisms in `MetrizableLCA` are continuous additive homomorphisms. -/
@[ext]
structure Hom (A B : MetrizableLCA.{u}) where
  hom' : A →ₜ+ B

instance : Category MetrizableLCA.{u} where
  Hom A B := Hom A B
  id A := ⟨ContinuousAddMonoidHom.id A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory MetrizableLCA (fun A B ↦ A →ₜ+ B) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying continuous additive homomorphism of an LCA morphism. -/
abbrev Hom.hom {A B : MetrizableLCA.{u}} (f : A ⟶ B) : A →ₜ+ B :=
  ConcreteCategory.hom (C := MetrizableLCA) f

/-- Typecheck a continuous additive homomorphism as an LCA morphism. -/
abbrev ofHom {A B : Type u} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [TopologicalSpace.MetrizableSpace A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [LocallyCompactSpace B] [TopologicalSpace.MetrizableSpace B]
    (f : A →ₜ+ B) : of A ⟶ of B :=
  ConcreteCategory.ofHom (C := MetrizableLCA) f

instance {A B : MetrizableLCA.{u}} : CoeFun (A ⟶ B) (fun _ ↦ A → B) where
  coe f := f.hom

@[ext]
lemma ext {A B : MetrizableLCA.{u}} {f g : A ⟶ B} (h : ∀ x : A, f x = g x) : f = g := by
  apply Hom.ext
  ext x
  exact h x

@[simp]
lemma hom_id {A : MetrizableLCA.{u}} :
    (𝟙 A : A ⟶ A).hom = ContinuousAddMonoidHom.id A := rfl

@[simp]
lemma id_apply (A : MetrizableLCA.{u}) (a : A) : (𝟙 A : A ⟶ A) a = a := rfl

@[simp]
lemma hom_comp {A B C : MetrizableLCA.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
lemma comp_apply {A B C : MetrizableLCA.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g : A ⟶ C) a = g (f a) := rfl

instance {A B : MetrizableLCA.{u}} : Zero (A ⟶ B) where
  zero := ⟨0⟩

@[simp]
lemma zero_apply {A B : MetrizableLCA.{u}} (a : A) : (0 : A ⟶ B) a = 0 := rfl

instance {A B : MetrizableLCA.{u}} : Add (A ⟶ B) where
  add f g := ⟨f.hom + g.hom⟩

@[simp]
lemma hom_add {A B : MetrizableLCA.{u}} (f g : A ⟶ B) :
    (f + g).hom = f.hom + g.hom := rfl

instance {A B : MetrizableLCA.{u}} : SMul ℕ (A ⟶ B) where
  smul n f := ⟨n • f.hom⟩

@[simp]
lemma hom_nsmul {A B : MetrizableLCA.{u}} (n : ℕ) (f : A ⟶ B) :
    (n • f).hom = n • f.hom := rfl

instance {A B : MetrizableLCA.{u}} : Neg (A ⟶ B) where
  neg f := ⟨-f.hom⟩

@[simp]
lemma hom_neg {A B : MetrizableLCA.{u}} (f : A ⟶ B) :
    (-f).hom = -f.hom := rfl

instance {A B : MetrizableLCA.{u}} : Sub (A ⟶ B) where
  sub f g := ⟨f.hom - g.hom⟩

@[simp]
lemma hom_sub {A B : MetrizableLCA.{u}} (f g : A ⟶ B) :
    (f - g).hom = f.hom - g.hom := rfl

instance {A B : MetrizableLCA.{u}} : SMul ℤ (A ⟶ B) where
  smul n f := ⟨n • f.hom⟩

@[simp]
lemma hom_zsmul {A B : MetrizableLCA.{u}} (n : ℤ) (f : A ⟶ B) :
    (n • f).hom = n • f.hom := rfl

instance (A B : MetrizableLCA.{u}) : AddCommGroup (A ⟶ B) :=
  Function.Injective.addCommGroup (Hom.hom) (by
    intro f g h
    exact Hom.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Preadditive MetrizableLCA.{u} where

/-- A categorical isomorphism of metrizable LCA groups gives a continuous additive equivalence. -/
noncomputable def isoToContinuousAddEquiv {A B : MetrizableLCA.{u}} (e : A ≅ B) : A ≃ₜ+ B where
  toFun := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : A ⟶ A => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : B ⟶ B => f x) e.inv_hom_id
  map_add' x y := (e.hom.hom : A →+ B).map_add x y
  continuous_toFun := e.hom.hom.continuous
  continuous_invFun := e.inv.hom.continuous

/-- Forget the topology while retaining the additive group. -/
def forgetToAddCommGrpCat : MetrizableLCA.{u} ⥤ AddCommGrpCat.{u} where
  obj A := AddCommGrpCat.of A
  map f := AddCommGrpCat.ofHom f.hom.toAddMonoidHom

instance : forgetToAddCommGrpCat.PreservesZeroMorphisms where
  map_zero A B := by
    ext x
    rfl

/-- Forget the additive structure while retaining the topology. -/
def forgetToTopCat : MetrizableLCA.{u} ⥤ TopCat.{u} where
  obj A := TopCat.of A
  map f := TopCat.ofHom f.hom.toContinuousMap

end MetrizableLCA

end LeanLCAExactChallenge
