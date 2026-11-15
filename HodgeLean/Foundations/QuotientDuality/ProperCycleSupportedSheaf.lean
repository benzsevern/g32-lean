import HodgeLean.Foundations.QuotientDuality.ProperCycleTopology
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedInjectiveModel

/-! # Supported singular and constant-sheaf cohomology on singular ambient spaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular TopologicalSpace HomologicalComplex
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual supported constant-sheaf presheaf agrees with relative singular cohomology.
Source: Bredon, Sheaf Theory, second edition, III.1; the contractible open basis and
flasque singular-cochain resolution, with the canonical constant augmentation.
HC no distance; AV milestone no distance. -/
def properCycle_supported_cohomology_presheaf_iso
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (S : Closeds (a3b4_an X.hom)) (n : ℕ) :
    TopCat.Sheaf.supportHOnOpenPresheaf
        (Z := S) ((TopCat.Sheaf.constantFunctor (a3b4_an X.hom)).obj
          (AddCommGrpCat.of ℚ)) n ≅
      supportRelativeCohomologyPresheaf (a3b4_an X.hom) S n := by
  let Y := a3b4_an X.hom
  letI : T2Space Y := HodgeLean.Foundations.Analytic.f4_t2Space X
  letI : ∀ V : Opens Y, ParacompactSpace V := properCycle_open_paracompact X
  let K := rationalSingularCochainComplex Y
  let a : (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat Y) 0).obj
      (TopCat.Sheaf.const Y (AddCommGrpCat.of ℚ)) ⟶ K :=
    (constantFieldSheafComplexIntIsoSingle ℚ (Over.mk X.hom)).inv ≫
      HomologicalComplex.extendMap (constantsToSingularCochainSheafComplex ℚ Y)
        ComplexShape.embeddingUpNat
  letI hconst : QuasiIso (constantsToSingularCochainSheafComplex ℚ Y) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ
      (properCycle_contractible_open_basis X)
  letI ha : QuasiIso a := by
    dsimp only [a]
    letI : QuasiIso ((constantFieldSheafComplexIntIsoSingle ℚ (Over.mk X.hom)).inv) :=
      quasiIso_of_isIso _
    letI : QuasiIso (HomologicalComplex.extendMap
        (constantsToSingularCochainSheafComplex ℚ Y) ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr hconst
    exact quasiIso_comp _ _
  letI hmono : Mono a := by
    dsimp only [a]
    exact @mono_comp _ _ _ _ _ _ inferInstance _
      (constantsToSingularCochainComplexInt_mono ℚ Y)
  exact (TopCat.Sheaf.supportHOnOpenPresheafIsoOfFlasque Y S
    ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℚ)) K a
    (fun j => rationalSingularCochainComplex_isFlasque Y j) n) ≪≫
    supportedSingularCohomologyPresheafIsoRelative Y S S.isClosed n

end HodgeLean.Foundations.QuotientDuality
