import HodgeLean.Foundations.RationalHomologyManifold.GlobalSubdivisionComplexComparison
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionLimitHomology

/-! Canonical comparison from the original supported global chains to the subdivision sheaf model.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual stage-zero supported global chain comparison with the subdivision-limit sheaf.
Source: Bredon, Sheaf Theory, second edition, VI.12; the canonical supported-chain comparison.
HC no distance; AV milestone no distance.
-/
def supportedStageZeroGlobalComparison (X : TopCat.{0}) :
    (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainPresheafComplex ℚ X) ⟶
    (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (subdivisionLimitSheafComplex X)) :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (colimit.ι (presheafSubdivisionDiagram X) 0) ≫
      subdivisionGlobalSheafificationMap X

#print axioms supportedStageZeroGlobalComparison
/-- The actual stage-zero global supported-chain comparison is a quasi-isomorphism on compact Hausdorff spaces.
Source: Bredon, Sheaf Theory, second edition, VI.12; the global subdivision comparison.
HC no distance; AV milestone no distance.
-/
theorem supportedStageZeroGlobalComparison_quasiIso (X : TopCat.{0})
    [CompactSpace X] [T2Space X] : QuasiIso (supportedStageZeroGlobalComparison X) := by
  let E := (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)
  letI := subdivisionPresheafStage_zero_quasiIso X
  letI := subdivisionGlobalSheafificationMap_isIso X
  change QuasiIso (((E.mapHomologicalComplex (ComplexShape.down ℕ)).map
    (colimit.ι (presheafSubdivisionDiagram X) 0)) ≫ subdivisionGlobalSheafificationMap X)
  infer_instance

#print axioms supportedStageZeroGlobalComparison_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
