import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension
import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# Mapping out of inner anodyne extensions

This file isolates the cartesian pushout-product input needed to show that precomposition
along an inner anodyne extension has the right lifting property against every monomorphism.
The remaining combinatorial hypothesis says that the pushout-product of an inner horn
inclusion with an arbitrary monomorphism is inner anodyne.

It also proves that any simplicial map with the right lifting property against every
monomorphism has a strict section and a fiberwise contraction parametrized by the
free-living equivalence. The resulting edge in the self-internal-hom is an equivalence.

For maps between quasicategories, the equivalence edge in the self-internal-hom determines
an invertible `2`-cell in mathlib's strict bicategory of quasicategories. Together with the
strict section, this upgrades the deformation retraction to an adjoint equivalence.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty
open Opposite
open Simplicial

/-- Maps into a quasicategory extend across every inner anodyne map. -/
lemma exists_extension_of_innerAnodyne
    {A B Q : SSet.{u}} {i : A ⟶ B} [SSet.Quasicategory Q]
    (hi : SSet.innerAnodyneExtensions i) (f : A ⟶ Q) :
    ∃ g : B ⟶ Q, i ≫ g = f := by
  let t : IsTerminal (⊤_ SSet.{u}) := Limits.terminalIsTerminal
  let sq : CommSq f i (t.from Q) (t.from B) := ⟨t.hom_ext _ _⟩
  have hlift : HasLiftingProperty i (t.from Q) :=
    hi _ (SSet.Quasicategory.from_innerFibrations Q t)
  letI : HasLiftingProperty i (t.from Q) := hlift
  exact ⟨sq.lift, sq.fac_left⟩

/-- The cartesian pushout-product closure needed for mapping-object invariance. -/
def InnerAnodyneCartesianPushoutProduct : Prop :=
  ∀ ⦃A B K L : SSet.{u}⦄ (i : A ⟶ B) (j : K ⟶ L),
    SSet.innerAnodyneExtensions i → Mono j →
      SSet.innerAnodyneExtensions (Arrow.mk i □ Arrow.mk j).hom

/-- The generating pushout-product statement that remains combinatorial. -/
def InnerHornMonoPushoutProductIsInnerAnodyne : Prop :=
  ∀ {n : ℕ} {k : Fin (n + 1)}, 0 < k → k < Fin.last n →
    ∀ ⦃K L : SSet.{u}⦄ (j : K ⟶ L), Mono j →
      SSet.innerAnodyneExtensions (Arrow.mk Λ[n, k].ι □ Arrow.mk j).hom

/-- The arbitrary-mono hypothesis supplies the initial-map case used for functor objects. -/
lemma innerHornPushoutProduct_of_innerHornMono
    (hgen : InnerHornMonoPushoutProductIsInnerAnodyne.{u}) :
    InnerHornPushoutProductIsInnerAnodyne.{u} := by
  intro n k h0 hn K
  exact hgen h0 hn (initial.to K) inferInstance

/-- The generating inner-horn case implies full cartesian pushout-product closure. -/
lemma innerAnodyneCartesianPushoutProduct_of_innerHornMono
    (hgen : InnerHornMonoPushoutProductIsInnerAnodyne.{u}) :
    InnerAnodyneCartesianPushoutProduct.{u} := by
  intro A B K L i j hi hj X Y p hp
  rw [Arrow.PushoutProduct.hasLiftingProperty_mk_iff']
  apply hi
  intro U V h hh
  obtain ⟨k, h0, hn⟩ := hh
  rw [← Arrow.PushoutProduct.hasLiftingProperty_mk_iff']
  exact hgen h0 hn j hj _ hp

/-- Reduce one exponential lifting problem to the corresponding pushout-product. -/
lemma hasLiftingProperty_pre_of_innerAnodyne_pushoutProduct
    {A B K L Q : SSet.{u}} {i : A ⟶ B} {j : K ⟶ L}
    [SSet.Quasicategory Q]
    (hbox : SSet.innerAnodyneExtensions (Arrow.mk i □ Arrow.mk j).hom) :
    HasLiftingProperty j ((MonoidalClosed.pre i).app Q) := by
  rw [← Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff
    (Limits.terminalIsTerminal : IsTerminal (⊤_ SSet.{u}))]
  exact hbox _
    (SSet.Quasicategory.from_innerFibrations Q Limits.terminalIsTerminal)

/-- Under cartesian pushout-product closure, precomposition has the RLP against every mono. -/
lemma pre_mem_monomorphisms_rlp
    {A B Q : SSet.{u}} {i : A ⟶ B} [SSet.Quasicategory Q]
    (hcart : InnerAnodyneCartesianPushoutProduct.{u})
    (hi : SSet.innerAnodyneExtensions i) :
    (monomorphisms SSet.{u}).rlp ((MonoidalClosed.pre i).app Q) := by
  intro K L j hj
  exact hasLiftingProperty_pre_of_innerAnodyne_pushoutProduct
    (hcart i j hi ((monomorphisms.iff j).1 hj))

/-- The generating inner-horn case makes precomposition mono-injective. -/
lemma pre_mem_monomorphisms_rlp_of_innerHornMono
    {A B Q : SSet.{u}} {i : A ⟶ B} [SSet.Quasicategory Q]
    (hgen : InnerHornMonoPushoutProductIsInnerAnodyne.{u})
    (hi : SSet.innerAnodyneExtensions i) :
    (monomorphisms SSet.{u}).rlp ((MonoidalClosed.pre i).app Q) :=
  pre_mem_monomorphisms_rlp
    (innerAnodyneCartesianPushoutProduct_of_innerHornMono hgen) hi

/-- Boundary pushout-product closure suffices for the generating boundary RLP. -/
lemma pre_mem_boundary_rlp
    {A B Q : SSet.{u}} {i : A ⟶ B} [SSet.Quasicategory Q]
    (hbox : ∀ n : ℕ,
      SSet.innerAnodyneExtensions
        (Arrow.mk i □ Arrow.mk (SSet.boundary.{u} n).ι).hom) :
    SSet.modelCategoryQuillen.I.rlp ((MonoidalClosed.pre i).app Q) := by
  intro K L j hj
  obtain ⟨n⟩ := hj
  exact hasLiftingProperty_pre_of_innerAnodyne_pushoutProduct (hbox n)

/-- The two objects of the discrete endpoint subcategory of the free-living equivalence. -/
inductive EquivalenceEndpoint : Type u where
  | zero
  | one

/-- The discrete category on the two endpoints, with small hom types. -/
instance equivalenceEndpointCategory : Category.{0} EquivalenceEndpoint.{u} where
  Hom X Y := PLift (X = Y)
  id X := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩
  id_comp f := by rcases f with ⟨rfl⟩; rfl
  comp_id f := by rcases f with ⟨rfl⟩; rfl
  assoc f g h := by rcases f with ⟨rfl⟩; rcases g with ⟨rfl⟩; rfl

/-- Every endpoint hom type is a subsingleton. -/
instance equivalenceEndpointHom_subsingleton
    (X Y : EquivalenceEndpoint.{u}) : Subsingleton (X ⟶ Y) where
  allEq f g := by
    rcases f with ⟨f⟩
    rcases g with ⟨g⟩
    congr

/-- The nerve of the discrete endpoint category. -/
abbrev EquivalenceEndpoints : SSet.{u} :=
  CategoryTheory.nerve EquivalenceEndpoint.{u}

/-- Include the discrete endpoint category into the free-living equivalence. -/
def equivalenceEndpointsFunctor :
    EquivalenceEndpoint.{u} ⥤ EquivalenceInterval.{u} where
  obj
    | .zero => equivalenceIntervalZero
    | .one => equivalenceIntervalOne
  map {X Y} f := by
    rcases f with ⟨rfl⟩
    exact PUnit.unit
  map_id X := rfl
  map_comp f g := rfl

/-- The endpoint inclusion is injective on objects. -/
lemma equivalenceEndpointsFunctor_obj_injective :
    Function.Injective equivalenceEndpointsFunctor.obj := by
  intro X Y h
  cases X <;> cases Y <;> simp_all [equivalenceEndpointsFunctor,
    equivalenceIntervalZero, equivalenceIntervalOne]

/-- Include the endpoint nerve into the nerve of the free-living equivalence. -/
def equivalenceEndpointsInclusion :
    EquivalenceEndpoints.{u} ⟶ CategoryTheory.nerve EquivalenceInterval.{u} :=
  CategoryTheory.nerveMap equivalenceEndpointsFunctor

/-- The endpoint-nerve inclusion is a monomorphism. -/
instance equivalenceEndpointsInclusion_mono :
    Mono equivalenceEndpointsInclusion.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  intro x y hxy
  refine ComposableArrows.ext (F := x) (G := y) ?_ ?_
  · intro i
    have h := congrArg (fun z ↦ z.obj i) hxy
    exact equivalenceEndpointsFunctor_obj_injective h
  · intro i hi
    apply Subsingleton.elim

/-- Read the common endpoint label of a simplex in the discrete endpoint nerve. -/
def equivalenceEndpointLabel {U : SimplexCategoryᵒᵖ}
    (z : EquivalenceEndpoints.{u}.obj U) : EquivalenceEndpoint.{u} :=
  z.obj 0

/-- Simplicial operators preserve the endpoint label. -/
lemma equivalenceEndpointLabel_map {U V : SimplexCategoryᵒᵖ}
    (f : U ⟶ V) (z : EquivalenceEndpoints.{u}.obj U) :
    equivalenceEndpointLabel (EquivalenceEndpoints.{u}.map f z) =
      equivalenceEndpointLabel z := by
  change z.obj (f.unop.toOrderHom 0) = z.obj 0
  exact (z.map (homOfLE zero_le)).down.symm

/-- Descend two maps along the two endpoint components. -/
def endpointDesc {X Y : SSet.{u}} (f₀ f₁ : X ⟶ Y) :
    X ⊗ EquivalenceEndpoints.{u} ⟶ Y where
  app U := ↾fun z ↦ match equivalenceEndpointLabel z.2 with
    | .zero => f₀.app U z.1
    | .one => f₁.app U z.1
  naturality U V α := by
    ext z
    rcases z with ⟨x, d⟩
    dsimp
    change (match equivalenceEndpointLabel (EquivalenceEndpoints.{u}.map α d) with
      | .zero => f₀.app V (X.map α x)
      | .one => f₁.app V (X.map α x)) =
        Y.map α (match equivalenceEndpointLabel d with
          | .zero => f₀.app U x
          | .one => f₁.app U x)
    rw [equivalenceEndpointLabel_map]
    cases h : equivalenceEndpointLabel d
    · change f₀.app V (X.map α x) = Y.map α (f₀.app U x)
      exact NatTrans.naturality_apply f₀ α x
    · change f₁.app V (X.map α x) = Y.map α (f₁.app U x)
      exact NatTrans.naturality_apply f₁ α x

/-- Product with a simplicial set preserves the endpoint inclusion's monomorphism. -/
instance endpointWhiskerLeft_mono (X : SSet.{u}) :
    Mono (X ◁ equivalenceEndpointsInclusion.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  rintro ⟨x, d₁⟩ ⟨y, d₂⟩ h
  change (x, equivalenceEndpointsInclusion.app U d₁) =
    (y, equivalenceEndpointsInclusion.app U d₂) at h
  apply Prod.ext
  · exact congrArg
      (fun z : X.obj U × (CategoryTheory.nerve EquivalenceInterval.{u}).obj U ↦ z.1) h
  · have hd := congrArg
      (fun z : X.obj U × (CategoryTheory.nerve EquivalenceInterval.{u}).obj U ↦ z.2) h
    exact (mono_iff_injective _).1 inferInstance hd

/-- The endpoint map commutes with a retraction over its target. -/
lemma endpointDesc_comp
    {X Y : SSet.{u}} (p : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) :
    endpointDesc (𝟙 X) (p ≫ s) ≫ p =
      (X ◁ equivalenceEndpointsInclusion.{u}) ≫
        CartesianMonoidalCategory.fst X _ ≫ p := by
  ext U z
  rcases z with ⟨x, d⟩
  dsimp [endpointDesc]
  cases h : equivalenceEndpointLabel d
  · rfl
  · change ((p ≫ s) ≫ p).app U x = p.app U x
    rw [Category.assoc, hs, Category.comp_id]

/-- A map with the RLP against every monomorphism has a chosen strict section. -/
noncomputable def sectionOfMonoRLP {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) : Y ⟶ X := by
  have hlp : HasLiftingProperty (initial.to Y) p :=
    hp _ (monomorphisms.infer_property _)
  letI : HasLiftingProperty (initial.to Y) p := hlp
  let sq : CommSq (initial.to X) (initial.to Y) p (𝟙 Y) :=
    ⟨initial.hom_ext _ _⟩
  exact sq.lift

/-- The chosen section is a strict right inverse. -/
lemma sectionOfMonoRLP_comp {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    sectionOfMonoRLP p hp ≫ p = 𝟙 Y := by
  let hlp : HasLiftingProperty (initial.to Y) p :=
    hp _ (monomorphisms.infer_property _)
  letI : HasLiftingProperty (initial.to Y) p := hlp
  let sq : CommSq (initial.to X) (initial.to Y) p (𝟙 Y) :=
    ⟨initial.hom_ext _ _⟩
  exact sq.fac_right

/-- A fiberwise contraction parametrized by the free-living equivalence. -/
noncomputable def contractionOfMonoRLP {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    X ⊗ CategoryTheory.nerve EquivalenceInterval.{u} ⟶ X := by
  let s := sectionOfMonoRLP p hp
  have hs : s ≫ p = 𝟙 Y := sectionOfMonoRLP_comp p hp
  let i := X ◁ equivalenceEndpointsInclusion.{u}
  let q := CartesianMonoidalCategory.fst X
    (CategoryTheory.nerve EquivalenceInterval.{u}) ≫ p
  let sq : CommSq (endpointDesc (𝟙 X) (p ≫ s)) i p q :=
    ⟨endpointDesc_comp p s hs⟩
  have hlp : HasLiftingProperty i p :=
    hp _ (monomorphisms.infer_property _)
  letI : HasLiftingProperty i p := hlp
  exact sq.lift

/-- The contraction restricts to the identity and the section-retraction composite. -/
lemma endpointsInclusion_comp_contractionOfMonoRLP
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    (X ◁ equivalenceEndpointsInclusion.{u}) ≫ contractionOfMonoRLP p hp =
      endpointDesc (𝟙 X) (p ≫ sectionOfMonoRLP p hp) := by
  let s := sectionOfMonoRLP p hp
  have hs : s ≫ p = 𝟙 Y := sectionOfMonoRLP_comp p hp
  let i := X ◁ equivalenceEndpointsInclusion.{u}
  let q := CartesianMonoidalCategory.fst X
    (CategoryTheory.nerve EquivalenceInterval.{u}) ≫ p
  let sq : CommSq (endpointDesc (𝟙 X) (p ≫ s)) i p q :=
    ⟨endpointDesc_comp p s hs⟩
  have hlp : HasLiftingProperty i p :=
    hp _ (monomorphisms.infer_property _)
  letI : HasLiftingProperty i p := hlp
  exact sq.fac_left

/-- The contraction stays in the fibers of the map with the mono right lifting property. -/
lemma contractionOfMonoRLP_comp
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    contractionOfMonoRLP p hp ≫ p =
      CartesianMonoidalCategory.fst X
          (CategoryTheory.nerve EquivalenceInterval.{u}) ≫ p := by
  let s := sectionOfMonoRLP p hp
  have hs : s ≫ p = 𝟙 Y := sectionOfMonoRLP_comp p hp
  let i := X ◁ equivalenceEndpointsInclusion.{u}
  let q := CartesianMonoidalCategory.fst X
    (CategoryTheory.nerve EquivalenceInterval.{u}) ≫ p
  let sq : CommSq (endpointDesc (𝟙 X) (p ≫ s)) i p q :=
    ⟨endpointDesc_comp p s hs⟩
  have hlp : HasLiftingProperty i p :=
    hp _ (monomorphisms.infer_property _)
  letI : HasLiftingProperty i p := hlp
  exact sq.fac_right

/--
Chosen strong deformation-retraction data carried by a simplicial map with the right
lifting property against every monomorphism. The homotopy is parametrized by the
free-living equivalence, fixes the map to the target, and runs from the identity to the
section-retraction composite.
-/
structure MonoRLPStrongDeformationRetraction
    {X Y : SSet.{u}} (p : X ⟶ Y) where
  retraction : Y ⟶ X
  retraction_comp : retraction ≫ p = 𝟙 Y
  contraction : X ⊗ CategoryTheory.nerve EquivalenceInterval.{u} ⟶ X
  contraction_comp : contraction ≫ p =
    CartesianMonoidalCategory.fst X
        (CategoryTheory.nerve EquivalenceInterval.{u}) ≫ p
  endpoints :
    (X ◁ equivalenceEndpointsInclusion.{u}) ≫ contraction =
      endpointDesc (𝟙 X) (p ≫ retraction)

/-- Package the canonical section and contraction produced by the mono right lifting property. -/
noncomputable def monoRLPStrongDeformationRetraction
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    MonoRLPStrongDeformationRetraction p where
  retraction := sectionOfMonoRLP p hp
  retraction_comp := sectionOfMonoRLP_comp p hp
  contraction := contractionOfMonoRLP p hp
  contraction_comp := contractionOfMonoRLP_comp p hp
  endpoints := endpointsInclusion_comp_contractionOfMonoRLP p hp

/-- The contraction carries the forward free equivalence to an internal-hom edge. -/
noncomputable def contractionEquivalenceEdge {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    SSet.Edge
      ((MonoidalClosed.curry (contractionOfMonoRLP p hp)).app (op ⦋0⦌)
        (CategoryTheory.nerveEquiv.symm equivalenceIntervalZero))
      ((MonoidalClosed.curry (contractionOfMonoRLP p hp)).app (op ⦋0⦌)
        (CategoryTheory.nerveEquiv.symm equivalenceIntervalOne)) :=
  (CategoryTheory.nerve.edgeMk equivalenceIntervalForward).map
    (MonoidalClosed.curry (contractionOfMonoRLP p hp))

/-- The contraction edge is an equivalence edge in the self-internal-hom. -/
theorem contractionEquivalenceEdge_isEquivalence
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    EdgeIsEquivalence (contractionEquivalenceEdge p hp) :=
  (edgeIsEquivalence_nerve_of_isIso equivalenceIntervalForward).map _

/-- Naturality of the inverse vertex-to-unit-map equivalence. -/
lemma unitHomEquiv_symm_natural {A B : SSet.{u}}
    (F : A ⟶ B) (a : A _⦋0⦌) :
    (SSet.unitHomEquiv B).symm (F.app _ a) =
      (SSet.unitHomEquiv A).symm a ≫ F := by
  ext U x
  obtain ⟨⟩ := x
  dsimp [SSet.unitHomEquiv]
  rw [← NatTrans.naturality_apply]

/-- The zero endpoint of the contraction represents the identity map. -/
lemma contractionVertexZero_map
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    internalHomVertexMap X X
      ((MonoidalClosed.curry (contractionOfMonoRLP p hp)).app (op ⦋0⦌)
        (CategoryTheory.nerveEquiv.symm equivalenceIntervalZero)) = 𝟙 X := by
  rw [internalHomVertexMap, unitHomEquiv_symm_natural]
  simp only [MonoidalClosed.uncurry', MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  let d₀ : EquivalenceEndpoints.{u} _⦋0⦌ :=
    CategoryTheory.nerveEquiv.symm EquivalenceEndpoint.zero
  have hpoint :
      (SSet.unitHomEquiv (CategoryTheory.nerve EquivalenceInterval.{u})).symm
          (CategoryTheory.nerveEquiv.symm equivalenceIntervalZero) =
        (SSet.unitHomEquiv EquivalenceEndpoints.{u}).symm d₀ ≫
          equivalenceEndpointsInclusion.{u} := by
    rw [← unitHomEquiv_symm_natural equivalenceEndpointsInclusion.{u} d₀]
    rfl
  rw [hpoint, whiskerLeft_comp_assoc,
    endpointsInclusion_comp_contractionOfMonoRLP]
  ext U x
  rfl

/-- The one endpoint of the contraction represents the section-retraction composite. -/
lemma contractionVertexOne_map
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    internalHomVertexMap X X
      ((MonoidalClosed.curry (contractionOfMonoRLP p hp)).app (op ⦋0⦌)
        (CategoryTheory.nerveEquiv.symm equivalenceIntervalOne)) =
      p ≫ sectionOfMonoRLP p hp := by
  rw [internalHomVertexMap, unitHomEquiv_symm_natural]
  simp only [MonoidalClosed.uncurry', MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  let d₁ : EquivalenceEndpoints.{u} _⦋0⦌ :=
    CategoryTheory.nerveEquiv.symm EquivalenceEndpoint.one
  have hpoint :
      (SSet.unitHomEquiv (CategoryTheory.nerve EquivalenceInterval.{u})).symm
          (CategoryTheory.nerveEquiv.symm equivalenceIntervalOne) =
        (SSet.unitHomEquiv EquivalenceEndpoints.{u}).symm d₁ ≫
          equivalenceEndpointsInclusion.{u} := by
    rw [← unitHomEquiv_symm_natural equivalenceEndpointsInclusion.{u} d₁]
    rfl
  rw [hpoint, whiskerLeft_comp_assoc,
    endpointsInclusion_comp_contractionOfMonoRLP]
  ext U x
  rfl

/-- Exact identification of the zero endpoint as the vertex of the identity map. -/
lemma contractionVertexZero
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    (MonoidalClosed.curry (contractionOfMonoRLP p hp)).app (op ⦋0⦌)
        (CategoryTheory.nerveEquiv.symm equivalenceIntervalZero) =
      SSet.unitHomEquiv ((ihom X).obj X) (MonoidalClosed.curry' (𝟙 X)) := by
  apply (SSet.unitHomEquiv ((ihom X).obj X)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply MonoidalClosed.uncurry'_injective
  rw [MonoidalClosed.uncurry'_curry']
  exact contractionVertexZero_map p hp

/-- Exact identification of the one endpoint as the section-retraction vertex. -/
lemma contractionVertexOne
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    (MonoidalClosed.curry (contractionOfMonoRLP p hp)).app (op ⦋0⦌)
        (CategoryTheory.nerveEquiv.symm equivalenceIntervalOne) =
      SSet.unitHomEquiv ((ihom X).obj X)
        (MonoidalClosed.curry' (p ≫ sectionOfMonoRLP p hp)) := by
  apply (SSet.unitHomEquiv ((ihom X).obj X)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply MonoidalClosed.uncurry'_injective
  rw [MonoidalClosed.uncurry'_curry']
  exact contractionVertexOne_map p hp

/-- The contraction edge with endpoints expressed as actual maps in the internal hom. -/
noncomputable def monoRLPUnitEdge {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    SSet.Edge
      (SSet.unitHomEquiv ((ihom X).obj X) (MonoidalClosed.curry' (𝟙 X)))
      (SSet.unitHomEquiv ((ihom X).obj X)
        (MonoidalClosed.curry' (p ≫ sectionOfMonoRLP p hp))) :=
  SSet.Edge.castEndpoints (contractionVertexZero p hp).symm
    (contractionVertexOne p hp).symm (contractionEquivalenceEdge p hp)

/-- The unit edge extracted from the mono right lifting property is an equivalence edge. -/
lemma monoRLPUnitEdge_isEquivalence {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    EdgeIsEquivalence (monoRLPUnitEdge p hp) :=
  (contractionEquivalenceEdge_isEquivalence p hp).castEndpoints
    (contractionVertexZero p hp).symm (contractionVertexOne p hp).symm

/-- An equivalence edge in a mapping simplicial set gives an invertible QCat `2`-cell. -/
noncomputable def twoIsoOfInternalHomEquivalenceEdge
    {X Y : SSet.QCat.{u}} {f g : X ⟶ Y}
    (e : SSet.Edge
      (SSet.unitHomEquiv ((ihom X.obj).obj Y.obj) (MonoidalClosed.curry' f.hom))
      (SSet.unitHomEquiv ((ihom X.obj).obj Y.obj) (MonoidalClosed.curry' g.hom)))
    (he : EdgeIsEquivalence e) :
    @Iso (X ⟶ Y) (SSet.QCat.bicategory.homCategory X Y) f g := by
  letI : Category (X ⟶ Y) := SSet.QCat.bicategory.homCategory X Y
  have hi : IsIso (edgeHomotopyClass e) := he
  letI : IsIso (edgeHomotopyClass e) := hi
  let m := edgeHomotopyClass e
  have hm : IsIso m := inferInstance
  letI : IsIso m := hm
  let mi := inv m
  exact
    { hom := CatEnrichedOrdinary.Hom.mk m
      inv := CatEnrichedOrdinary.Hom.mk mi
      hom_inv_id := by
        apply CatEnrichedOrdinary.Hom.ext
        exact IsIso.hom_inv_id m
      inv_hom_id := by
        apply CatEnrichedOrdinary.Hom.ext
        exact IsIso.inv_hom_id m }

/-- A QCat map with the right lifting property against every monomorphism is an adjoint
equivalence. -/
noncomputable def bicategoricalEquivalenceOfMonoRLP
    {X Y : SSet.QCat.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p.hom) :
    Bicategory.Equivalence X Y := by
  let s : Y ⟶ X := ObjectProperty.homMk (sectionOfMonoRLP p.hom hp)
  have hs : s ≫ p = 𝟙 Y := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    exact sectionOfMonoRLP_comp p.hom hp
  letI : Category (X ⟶ X) := SSet.QCat.bicategory.homCategory X X
  letI : Category (Y ⟶ Y) := SSet.QCat.bicategory.homCategory Y Y
  let unit : (𝟙 X) ≅ p ≫ s :=
    twoIsoOfInternalHomEquivalenceEdge
      (monoRLPUnitEdge p.hom hp) (monoRLPUnitEdge_isEquivalence p.hom hp)
  let counit : s ≫ p ≅ 𝟙 Y := eqToIso hs
  exact Bicategory.Equivalence.mkOfAdjointifyCounit unit counit

/-- A QCat map with the mono right lifting property is a bicategorical equivalence. -/
theorem monoRLP_isBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p.hom) :
    IsBicategoricalEquivalence p := by
  exact ⟨bicategoricalEquivalenceOfMonoRLP p hp, rfl⟩

end Infinity
end LeanLCAExactChallenge
