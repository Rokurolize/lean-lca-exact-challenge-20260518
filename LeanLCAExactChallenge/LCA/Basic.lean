import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
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

/-- Product object used as the binary biproduct in `MetrizableLCA`. -/
abbrev biprodObj (A B : MetrizableLCA.{u}) : MetrizableLCA.{u} :=
  MetrizableLCA.of (A × B)

/-- First projection from the binary biproduct object. -/
def biprodFst (A B : MetrizableLCA.{u}) : biprodObj A B ⟶ A where
  hom' :=
    { toFun := Prod.fst
      map_zero' := rfl
      map_add' := by
        intro x y
        rfl
      continuous_toFun := continuous_fst }

/-- Second projection from the binary biproduct object. -/
def biprodSnd (A B : MetrizableLCA.{u}) : biprodObj A B ⟶ B where
  hom' :=
    { toFun := Prod.snd
      map_zero' := rfl
      map_add' := by
        intro x y
        rfl
      continuous_toFun := continuous_snd }

/-- First inclusion into the binary biproduct object. -/
def biprodInl (A B : MetrizableLCA.{u}) : A ⟶ biprodObj A B where
  hom' :=
    { toFun := fun a => (a, 0)
      map_zero' := rfl
      map_add' := by
        intro x y
        ext <;> simp
      continuous_toFun := continuous_id.prodMk continuous_const }

/-- Second inclusion into the binary biproduct object. -/
def biprodInr (A B : MetrizableLCA.{u}) : B ⟶ biprodObj A B where
  hom' :=
    { toFun := fun b => (0, b)
      map_zero' := rfl
      map_add' := by
        intro x y
        ext <;> simp
      continuous_toFun := continuous_const.prodMk continuous_id }

@[simp]
lemma biprodFst_apply (A B : MetrizableLCA.{u}) (x : A × B) :
    biprodFst A B x = x.1 := rfl

@[simp]
lemma biprodSnd_apply (A B : MetrizableLCA.{u}) (x : A × B) :
    biprodSnd A B x = x.2 := rfl

@[simp]
lemma biprodInl_apply (A B : MetrizableLCA.{u}) (a : A) :
    biprodInl A B a = (a, 0) := rfl

@[simp]
lemma biprodInr_apply (A B : MetrizableLCA.{u}) (b : B) :
    biprodInr A B b = (0, b) := rfl

/-- Map into the product side of the binary biproduct. -/
def biprodLift {T A B : MetrizableLCA.{u}} (f : T ⟶ A) (g : T ⟶ B) :
    T ⟶ biprodObj A B where
  hom' :=
    { toFun := fun t => (f t, g t)
      map_zero' := by simp
      map_add' := by
        intro x y
        ext <;> simp [map_add]
      continuous_toFun := f.hom.continuous.prodMk g.hom.continuous }

/-- Map out of the coproduct side of the binary biproduct. -/
def biprodDesc {A B T : MetrizableLCA.{u}} (f : A ⟶ T) (g : B ⟶ T) :
    biprodObj A B ⟶ T where
  hom' :=
    { toFun := fun p => f p.1 + g p.2
      map_zero' := by simp
      map_add' := by
        intro x y
        simp [map_add, add_assoc, add_left_comm, add_comm]
      continuous_toFun := (f.hom.continuous.comp continuous_fst).add
        (g.hom.continuous.comp continuous_snd) }

/-- Coordinatewise map between binary biproduct objects. -/
def biprodMap {A B A' B' : MetrizableLCA.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    biprodObj A B ⟶ biprodObj A' B' where
  hom' :=
    { toFun := fun p => (f p.1, g p.2)
      map_zero' := by simp
      map_add' := by
        intro x y
        ext <;> simp [map_add]
      continuous_toFun :=
        (f.hom.continuous.comp continuous_fst).prodMk
          (g.hom.continuous.comp continuous_snd) }

@[simp]
lemma biprodMap_apply {A B A' B' : MetrizableLCA.{u}} (f : A ⟶ A') (g : B ⟶ B')
    (p : A × B) : biprodMap f g p = (f p.1, g p.2) := rfl

@[simp]
lemma biprodLift_fst {T A B : MetrizableLCA.{u}} (f : T ⟶ A) (g : T ⟶ B) :
    biprodLift f g ≫ biprodFst A B = f := by
  ext t
  rfl

@[simp]
lemma biprodLift_snd {T A B : MetrizableLCA.{u}} (f : T ⟶ A) (g : T ⟶ B) :
    biprodLift f g ≫ biprodSnd A B = g := by
  ext t
  rfl

@[simp]
lemma biprodInl_desc {A B T : MetrizableLCA.{u}} (f : A ⟶ T) (g : B ⟶ T) :
    biprodInl A B ≫ biprodDesc f g = f := by
  ext a
  change f a + g 0 = f a
  simp

@[simp]
lemma biprodInr_desc {A B T : MetrizableLCA.{u}} (f : A ⟶ T) (g : B ⟶ T) :
    biprodInr A B ≫ biprodDesc f g = g := by
  ext b
  change f 0 + g b = g b
  simp

@[simp]
lemma biprodInl_fst (A B : MetrizableLCA.{u}) :
    biprodInl A B ≫ biprodFst A B = 𝟙 A := by
  ext a
  rfl

@[simp]
lemma biprodInl_snd (A B : MetrizableLCA.{u}) :
    biprodInl A B ≫ biprodSnd A B = 0 := by
  ext a
  rfl

@[simp]
lemma biprodInr_fst (A B : MetrizableLCA.{u}) :
    biprodInr A B ≫ biprodFst A B = 0 := by
  ext b
  rfl

@[simp]
lemma biprodInr_snd (A B : MetrizableLCA.{u}) :
    biprodInr A B ≫ biprodSnd A B = 𝟙 B := by
  ext b
  rfl

lemma biprodLift_unique {T A B : MetrizableLCA.{u}} (f : T ⟶ A) (g : T ⟶ B)
    (m : T ⟶ biprodObj A B) (hfst : m ≫ biprodFst A B = f)
    (hsnd : m ≫ biprodSnd A B = g) : m = biprodLift f g := by
  ext t
  · exact congrArg (fun h : T ⟶ A => h t) hfst
  · exact congrArg (fun h : T ⟶ B => h t) hsnd

lemma biprodDesc_unique {A B T : MetrizableLCA.{u}} (f : A ⟶ T) (g : B ⟶ T)
    (m : biprodObj A B ⟶ T) (hfst : biprodInl A B ≫ m = f)
    (hsnd : biprodInr A B ≫ m = g) : m = biprodDesc f g := by
  ext p
  have hp : p = (p.1, 0) + (0, p.2) := by ext <;> simp
  calc
    m p = m ((p.1, 0) + (0, p.2)) := congrArg (fun q => m q) hp
    _ = m (p.1, 0) + m (0, p.2) := map_add m.hom (p.1, 0) (0, p.2)
    _ = f p.1 + g p.2 := by
      have hf := congrArg (fun h : A ⟶ T => h p.1) hfst
      have hg := congrArg (fun h : B ⟶ T => h p.2) hsnd
      simpa using congrArg₂ (fun x y => x + y) hf hg
    _ = biprodDesc f g p := rfl

/-- Explicit binary biproduct data for metrizable locally compact abelian groups. -/
def binaryBiproductData (A B : MetrizableLCA.{u}) :
    BinaryBiproductData A B where
  bicone :=
    { pt := biprodObj A B
      fst := biprodFst A B
      snd := biprodSnd A B
      inl := biprodInl A B
      inr := biprodInr A B }
  isBilimit :=
    { isLimit := BinaryFan.IsLimit.mk _
        (fun f g => biprodLift f g)
        (fun f g => biprodLift_fst f g)
        (fun f g => biprodLift_snd f g)
        (fun f g m hfst hsnd => biprodLift_unique f g m hfst hsnd)
      isColimit := BinaryCofan.IsColimit.mk _
        (fun f g => biprodDesc f g)
        (fun f g => biprodInl_desc f g)
        (fun f g => biprodInr_desc f g)
        (fun f g m hfst hsnd => biprodDesc_unique f g m hfst hsnd) }

instance : HasBinaryBiproducts MetrizableLCA.{u} where
  has_binary_biproduct A B := HasBinaryBiproduct.mk (binaryBiproductData A B)

/-- The explicit product model is canonically isomorphic to mathlib's chosen binary biproduct. -/
noncomputable def biprodObjIsoBiprod (A B : MetrizableLCA.{u}) :
    biprodObj A B ≅ A ⊞ B :=
  biprod.uniqueUpToIso A B (binaryBiproductData A B).isBilimit

@[simp]
lemma biprodObjIsoBiprod_hom_fst (A B : MetrizableLCA.{u}) :
    (biprodObjIsoBiprod A B).hom ≫ biprod.fst = biprodFst A B := by
  simp [biprodObjIsoBiprod, binaryBiproductData]

@[simp]
lemma biprodObjIsoBiprod_hom_snd (A B : MetrizableLCA.{u}) :
    (biprodObjIsoBiprod A B).hom ≫ biprod.snd = biprodSnd A B := by
  simp [biprodObjIsoBiprod, binaryBiproductData]

@[simp]
lemma biprodObjIsoBiprod_inv_fst (A B : MetrizableLCA.{u}) :
    (biprodObjIsoBiprod A B).inv ≫ biprodFst A B = biprod.fst := by
  apply biprod.hom_ext'
  · simp [biprodObjIsoBiprod, binaryBiproductData]
  · simp [biprodObjIsoBiprod, binaryBiproductData]

@[simp]
lemma biprodObjIsoBiprod_inv_snd (A B : MetrizableLCA.{u}) :
    (biprodObjIsoBiprod A B).inv ≫ biprodSnd A B = biprod.snd := by
  apply biprod.hom_ext'
  · simp [biprodObjIsoBiprod, binaryBiproductData]
  · simp [biprodObjIsoBiprod, binaryBiproductData]

/-- Diagonal map into the chosen binary biproduct. -/
noncomputable abbrev biprodDiag (A : MetrizableLCA.{u}) : A ⟶ A ⊞ A :=
  biprod.lift (𝟙 A) (𝟙 A)

/-- Codiagonal map out of the chosen binary biproduct. -/
noncomputable abbrev biprodCodiag (A : MetrizableLCA.{u}) : A ⊞ A ⟶ A :=
  biprod.desc (𝟙 A) (𝟙 A)

@[simp]
lemma biprodDiag_fst (A : MetrizableLCA.{u}) :
    biprodDiag A ≫ biprod.fst = 𝟙 A := by
  simp [biprodDiag]

@[simp]
lemma biprodDiag_snd (A : MetrizableLCA.{u}) :
    biprodDiag A ≫ biprod.snd = 𝟙 A := by
  simp [biprodDiag]

@[simp]
lemma biprodCodiag_inl (A : MetrizableLCA.{u}) :
    biprod.inl ≫ biprodCodiag A = 𝟙 A := by
  simp [biprodCodiag]

@[simp]
lemma biprodCodiag_inr (A : MetrizableLCA.{u}) :
    biprod.inr ≫ biprodCodiag A = 𝟙 A := by
  simp [biprodCodiag]

/-- A categorical isomorphism of metrizable LCA groups gives a continuous additive equivalence. -/
noncomputable def isoToContinuousAddEquiv {A B : MetrizableLCA.{u}} (e : A ≅ B) : A ≃ₜ+ B where
  toFun := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : A ⟶ A => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : B ⟶ B => f x) e.inv_hom_id
  map_add' x y := (e.hom.hom : A →+ B).map_add x y
  continuous_toFun := e.hom.hom.continuous
  continuous_invFun := e.inv.hom.continuous

/-- A bijective open morphism of metrizable LCA groups is a continuous additive equivalence. -/
noncomputable def continuousAddEquivOfBijectiveOpenMap {A B : MetrizableLCA.{u}} (f : A ⟶ B)
    (hbij : Function.Bijective (f : A → B)) (hopen : IsOpenMap (f : A → B)) : A ≃ₜ+ B := by
  let e : A ≃ B := Equiv.ofBijective (f : A → B) hbij
  let hhomeo : A ≃ₜ B := e.toHomeomorphOfContinuousOpen f.hom.continuous hopen
  refine
    { toFun := hhomeo
      invFun := hhomeo.symm
      left_inv := hhomeo.left_inv
      right_inv := hhomeo.right_inv
      map_add' := ?_
      continuous_toFun := hhomeo.continuous_toFun
      continuous_invFun := hhomeo.continuous_invFun }
  intro x y
  exact (f.hom : A →+ B).map_add x y

/-- A bijective open morphism of metrizable LCA groups is a categorical isomorphism. -/
noncomputable def isoOfBijectiveOpenMap {A B : MetrizableLCA.{u}} (f : A ⟶ B)
    (hbij : Function.Bijective (f : A → B)) (hopen : IsOpenMap (f : A → B)) : A ≅ B := by
  let e := continuousAddEquivOfBijectiveOpenMap f hbij hopen
  refine
    { hom := f
      inv := ⟨{
        toFun := e.symm
        map_zero' := e.symm.map_zero
        map_add' := e.symm.map_add
        continuous_toFun := e.symm.continuous }
      ⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext x
    exact e.symm_apply_apply x
  · ext y
    exact e.apply_symm_apply y

theorem isIso_of_bijective_openMap {A B : MetrizableLCA.{u}} (f : A ⟶ B)
    (hbij : Function.Bijective (f : A → B)) (hopen : IsOpenMap (f : A → B)) : IsIso f :=
  (isoOfBijectiveOpenMap f hbij hopen).isIso_hom

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
