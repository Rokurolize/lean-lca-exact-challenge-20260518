import LeanLCAExactChallenge.Derived.Bounded

/-!
Semantic stable input adapter audit for the `Dbounded` route.

This non-product file replaces the earlier marker-like four-projection surface with a
more concrete ordinary-category input shape: finite limits, finite colimits, a zero object,
an additive suspension candidate, and ordinary triangulated structure on `Dbounded C`.
It still does not prove product success. The adapter records the next implementation target:
construct those semantic ordinary-category fields for the strict `Dbounded` localization and
then justify that they are sufficient for the intended stable infinity-category claim.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace DboundedSemanticStableInputAdapter

/-- The ordinary `Dbounded` infinity-category context currently supplied by the project. -/
structure OrdinaryDboundedInfinityContext
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  quasicategory : SSet.Quasicategory (Dbounded.infinityNerve C)
  homotopyCategoryIso : SSet.hoFunctor.obj (Dbounded.infinityNerve C) ≅ Cat.of (Dbounded C)

/-- Assemble the current ordinary context from `Derived.Bounded`. -/
noncomputable def currentOrdinaryDboundedInfinityContext
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    OrdinaryDboundedInfinityContext C where
  quasicategory := Dbounded.infinityNerve_quasicategory (C := C)
  homotopyCategoryIso := Dbounded.homotopyCategoryIso (C := C)

/--
Concrete ordinary-category semantics that would be needed before a stable `Dbounded`
claim can be reviewed.

These fields are intentionally ordinary category/typeclass fields, not an abstract
`stableCertificate : Type` marker. They are still conditional input for this audit and are
not supplied by the current project for `Dbounded MetrizableLCA`.
-/
structure DboundedOrdinaryStableSemanticInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  preadditive : Preadditive (Dbounded C)
  finiteLimits : HasFiniteLimits (Dbounded C)
  finiteColimits : HasFiniteColimits (Dbounded C)
  zeroObject : HasZeroObject (Dbounded C)
  shiftAdditiveAll :
    letI : Preadditive (Dbounded C) := preadditive
    ∀ n : ℤ, (shiftFunctor (Dbounded C) n).Additive
  suspensionAdditive :
    letI : Preadditive (Dbounded C) := preadditive
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded C) n).Additive := shiftAdditiveAll
    (shiftFunctor (Dbounded C) (1 : ℤ)).Additive
  pretriangulated :
    letI : Preadditive (Dbounded C) := preadditive
    letI : HasZeroObject (Dbounded C) := zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded C) n).Additive := shiftAdditiveAll
    Pretriangulated (Dbounded C)
  triangulated :
    letI : Preadditive (Dbounded C) := preadditive
    letI : HasZeroObject (Dbounded C) := zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded C) n).Additive := shiftAdditiveAll
    letI : Pretriangulated (Dbounded C) := pretriangulated
    IsTriangulated (Dbounded C)

/-- Semantic certificate specialized to `Dbounded.infinityCategory C`. -/
structure DboundedSemanticStableCertificate
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (u + 1) (v + 1)) where
  semanticInput : Type (max u v)
  input : semanticInput
  finiteLimits : semanticInput → Prop
  finiteColimits : semanticInput → Prop
  suspensionLoopEquivalence : semanticInput → Prop
  pushoutPullbackCompatibility : semanticInput → Prop
  finiteLimits_ready : finiteLimits input
  finiteColimits_ready : finiteColimits input
  suspensionLoopEquivalence_ready : suspensionLoopEquivalence input
  pushoutPullbackCompatibility_ready : pushoutPullbackCompatibility input

/-- Semantic suspension-loop readiness extracted from an ordinary input record. -/
def semanticSuspensionLoopReady
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (data : DboundedOrdinaryStableSemanticInput C) : Prop :=
  letI : Preadditive (Dbounded C) := data.preadditive
  letI : ∀ n : ℤ, (shiftFunctor (Dbounded C) n).Additive := data.shiftAdditiveAll
  Nonempty (HasZeroObject (Dbounded C)) ∧
    Nonempty ((shiftFunctor (Dbounded C) (1 : ℤ)).Additive)

/-- Semantic pushout-pullback readiness represented by ordinary triangulated structure. -/
def semanticPushoutPullbackReady
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (data : DboundedOrdinaryStableSemanticInput C) : Prop :=
  letI : Preadditive (Dbounded C) := data.preadditive
  letI : HasZeroObject (Dbounded C) := data.zeroObject
  letI : ∀ n : ℤ, (shiftFunctor (Dbounded C) n).Additive := data.shiftAdditiveAll
  letI : Pretriangulated (Dbounded C) := data.pretriangulated
  Nonempty (IsTriangulated (Dbounded C))

/--
Adapter from concrete ordinary semantic fields to the single-certificate four-projection
shape. This is conditional: it consumes the missing semantic input instead of constructing it.
-/
def semanticStableCertificateOfOrdinaryInput
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (input : DboundedOrdinaryStableSemanticInput C) :
    DboundedSemanticStableCertificate C where
  semanticInput := DboundedOrdinaryStableSemanticInput C
  input := input
  finiteLimits := fun _data => Nonempty (HasFiniteLimits (Dbounded C))
  finiteColimits := fun _data => Nonempty (HasFiniteColimits (Dbounded C))
  suspensionLoopEquivalence := semanticSuspensionLoopReady
  pushoutPullbackCompatibility := semanticPushoutPullbackReady
  finiteLimits_ready := ⟨input.finiteLimits⟩
  finiteColimits_ready := ⟨input.finiteColimits⟩
  suspensionLoopEquivalence_ready := ⟨⟨input.zeroObject⟩, ⟨input.suspensionAdditive⟩⟩
  pushoutPullbackCompatibility_ready := ⟨input.triangulated⟩

/-- Readiness predicate for the semantic certificate. -/
def DboundedSemanticStableCertificate.ready
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedSemanticStableCertificate C) : Prop :=
  cert.finiteLimits cert.input ∧
    cert.finiteColimits cert.input ∧
    cert.suspensionLoopEquivalence cert.input ∧
    cert.pushoutPullbackCompatibility cert.input

/-- The ordinary semantic input adapter produces a ready semantic certificate. -/
theorem semanticStableCertificateOfOrdinaryInput_ready
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (input : DboundedOrdinaryStableSemanticInput C) :
    (semanticStableCertificateOfOrdinaryInput input).ready := by
  exact ⟨⟨input.finiteLimits⟩, ⟨input.finiteColimits⟩,
    ⟨⟨input.zeroObject⟩, ⟨input.suspensionAdditive⟩⟩, ⟨input.triangulated⟩⟩

/-- The exact conditional theorem shape still missing for the strict `Dbounded` route. -/
abbrev OrdinaryContextToSemanticStableInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) :=
  OrdinaryDboundedInfinityContext C → DboundedOrdinaryStableSemanticInput C

/-- The semantic fields that still need real construction for `Dbounded C`. -/
def missingSemanticFieldNames : List String :=
  ["HasFiniteLimits (Dbounded C)", "HasFiniteColimits (Dbounded C)",
    "HasZeroObject (Dbounded C)", "forall n, (shiftFunctor (Dbounded C) n).Additive",
    "(shiftFunctor (Dbounded C) 1).Additive", "Pretriangulated (Dbounded C)",
    "IsTriangulated (Dbounded C)"]

/-- The semantic adapter has seven concrete ordinary-category input fields. -/
theorem missingSemanticFieldNames_count :
    missingSemanticFieldNames.length = 7 := rfl

/-- Current ordinary context alone does not supply the semantic input record. -/
structure CurrentSemanticRouteState
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) where
  ordinaryContext : OrdinaryDboundedInfinityContext C
  semanticInput : Option (DboundedOrdinaryStableSemanticInput C)
  missingConstructor : String

/-- Reproducible current route state: ordinary context present, semantic input absent. -/
noncomputable def currentSemanticRouteState
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    CurrentSemanticRouteState C where
  ordinaryContext := currentOrdinaryDboundedInfinityContext C
  semanticInput := none
  missingConstructor := "OrdinaryContextToSemanticStableInput"

/-- This audit does not find a current semantic stable input constructor. -/
theorem currentSemanticRouteState_semanticInput_not_supplied
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    (currentSemanticRouteState C).semanticInput = none := rfl

section Checks

#check OrdinaryDboundedInfinityContext
#check currentOrdinaryDboundedInfinityContext
#check DboundedOrdinaryStableSemanticInput
#check DboundedSemanticStableCertificate
#check semanticSuspensionLoopReady
#check semanticPushoutPullbackReady
#check semanticStableCertificateOfOrdinaryInput
#check DboundedSemanticStableCertificate.ready
#check semanticStableCertificateOfOrdinaryInput_ready
#check OrdinaryContextToSemanticStableInput
#check missingSemanticFieldNames
#check missingSemanticFieldNames_count
#check CurrentSemanticRouteState
#check currentSemanticRouteState
#check currentSemanticRouteState_semanticInput_not_supplied
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions
#check Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
#check (currentOrdinaryDboundedInfinityContext (C := MetrizableLCA))
#check (currentSemanticRouteState (C := MetrizableLCA))

end Checks

end DboundedSemanticStableInputAdapter

end LeanLCAExactChallenge
