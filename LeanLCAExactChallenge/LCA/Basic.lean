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

instance : HasZeroMorphisms MetrizableLCA.{u} where
  comp_zero := by
    intro X Y f Z
    ext x
    rfl
  zero_comp := by
    intro X Y Z f
    ext x
    simp

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
