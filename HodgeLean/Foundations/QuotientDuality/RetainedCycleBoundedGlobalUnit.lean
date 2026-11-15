import HodgeLean.Foundations.QuotientDuality.RetainedCycleSoftDerivedSections
import HodgeLean.Foundations.QuotientDuality.RetainedCycleTruncatedSubdivisionStage
import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedChainSheaf
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionTruncationSoftness

/-! # Detection by the original bounded global section unit -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

local instance boundedGlobalSheafDerived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) := HasDerivedCategory.standard _
local instance boundedGlobalGroupDerived : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- In the untouched truncation window, the actual global derived unit is injective on homology.
Source: subdivisionTruncatedSheafComplex_isSoft; retained_global_truncated_subdivision_quasiIsoAt.
-/
theorem retained_bounded_global_unit_injective
    (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (N : ℕ) (o : LocalRationalOrientation X (N+1))
    (i : ℤ) (hi : -((N+1 : ℕ) : ℤ)+1 < i) :
    Function.Injective ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat i).map
      ((subdivisionGlobalSectionsFunctor X).rightDerivedFunctorPlusUnit.app
        (properCycle_bounded_chain_sheaf X (N+1)))).hom := by
  let K := properCycle_bounded_chain_sheaf X (N+1)
  let L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat X) :=
    ⟨subdivisionTruncatedSheafComplex X (N+1), ⟨-((N+1 : ℕ) : ℤ), by
      dsimp [subdivisionTruncatedSheafComplex]; infer_instance⟩⟩
  let f : K ⟶ L := ObjectProperty.homMk
    (CochainComplex.truncGEMap (subdivisionSheafCochainStage X 0) (-((N+1 : ℕ) : ℤ)))
  letI := retained_soft_global_sections_unit_isIso X L
    (subdivisionTruncatedSheafComplex_isSoft X t N o)
  haveI : QuasiIsoAt ((subdivisionGlobalSectionsFunctor X).mapCochainComplexPlus.map f).hom i :=
    retained_global_truncated_subdivision_quasiIsoAt X _ i hi
  exact retained_derived_sections_unit_injective_of_comparison
    (subdivisionGlobalSectionsFunctor X) K L f i

end HodgeLean.Foundations.QuotientDuality
