import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
/-- The extra cochain-level boundedness data a triangle strictification theorem must return
to discharge the bounded route.

The existing endpoint hypotheses say only that `T.obj₁` and `T.obj₃` are bounded after
passing to the homotopy category. For `boundedHomotopyObjectTrianglehIso13Realization`, the
chosen strict mapping-cone representative itself must have a bounded source and bounded
mapping cone. This payload records the missing bridge: strict bounded representatives
`Ksrc` and `Kcone`, plus cochain-level isomorphisms from them to the selected source `K`
and selected `CochainComplex.mappingCone f`. -/
abbrev boundedTrianglehIso13CochainDataStrictification
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
    boundedHomotopyObject C T.obj₁ →
    boundedHomotopyObject C T.obj₃ →
    ∃ (Ksrc Kcone K L : CochainComplex C ℤ) (f : K ⟶ L)
      (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
      (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃)
      (_eK : Ksrc ≅ K) (_eCone : Kcone ≅ CochainComplex.mappingCone f),
        (CochainComplex.mappingCone.triangleh f).mor₃ ≫
            (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map e₁.hom =
          e₃.hom ≫ T.mor₃ ∧
        boundedCochainComplex C Ksrc ∧
        boundedCochainComplex C Kcone

omit [QuillenExactCategory C] in
/-- Cochain-level boundedness transport from a strengthened strictification payload is
enough to supply the bounded strict-realization input already used by `Bounded.lean`. -/
theorem boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data_strictification
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13CochainDataStrictification C) :
    boundedHomotopyObjectTrianglehIso13Realization C := by
  intro T hT h₁ h₃
  rcases strictify hT h₁ h₃ with
    ⟨Ksrc, Kcone, K, L, f, e₁, e₃, eK, eCone, comm, hKsrc, hKcone⟩
  exact ⟨K, L, f, e₁, e₃, comm,
    (boundedCochainComplex C).prop_of_iso eK hKsrc,
    (boundedCochainComplex C).prop_of_iso eCone hKcone⟩

/-- The exact-acyclic and bounded routes need different strictification outputs.

The exact route asks for `exactAcyclic C L` for the selected middle strict complex. The
bounded route asks instead for cochain-level transport of strict boundedness to the selected
source and selected mapping cone. Providing both inputs gives the two `Closed₂` classes
consumed by the ordinary bounded homotopy Verdier scaffolding. -/
theorem exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_exact_realization_and_cochain_data
    [HasZeroObject C] [HasBinaryBiproducts C]
    (exactRealize : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C)
    (boundedStrictify : boundedTrianglehIso13CochainDataStrictification C) :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ ∧
      (boundedHomotopyObject C).IsTriangulatedClosed₂ :=
  exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_triangleh_iso13_realizations
    C exactRealize
    (boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data_strictification
      C boundedStrictify)

omit [QuillenExactCategory C] in
/-- A weaker endpoint-representability payload that is not enough for the current bounded
route.

This records the obstruction isolated by the selected-cochain strictification probes:
bounded strict representatives merely isomorphic in the homotopy category do not let us
transport `boundedCochainComplex C` to the selected source `K` or to the selected
`CochainComplex.mappingCone f`. The route above deliberately asks for strict
cochain-complex isomorphisms instead. -/
abbrev homotopyEndpointPayloadWithoutSelectedCochainIso
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
    boundedHomotopyObject C T.obj₁ →
    boundedHomotopyObject C T.obj₃ →
    ∃ (Ksrc Kcone K L : CochainComplex C ℤ) (f : K ⟶ L)
      (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
      (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃),
        (CochainComplex.mappingCone.triangleh f).mor₃ ≫
            (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map e₁.hom =
          e₃.hom ≫ T.mor₃ ∧
        boundedCochainComplex C Ksrc ∧
        boundedCochainComplex C Kcone ∧
        Nonempty ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Ksrc ≅
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ∧
        Nonempty ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Kcone ≅
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone f))

#check boundedTrianglehIso13CochainDataStrictification
#check boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data_strictification
#check exactAcyclicHomotopyIsoClosureTrianglehIso13Realization
#check exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_exact_realization_and_cochain_data
#check homotopyEndpointPayloadWithoutSelectedCochainIso

end LeanLCAExactChallenge
