import HodgeLean.Foundations.QuotientDuality.RetainedCycleGlobalSubdivisionStage
import HodgeLean.Foundations.QuotientDuality.RetainedCycleTruncationWindow

/-! # Actual truncated global subdivision in the middle-degree window -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual truncated subdivision map preserves global homology in every untouched window. -/
lemma retained_global_truncated_subdivision_quasiIsoAt
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] (b i : ℤ) (hi : b+1 < i) :
    QuasiIsoAt (((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.truncGEMap (subdivisionSheafCochainStage X 0) b)) i := by
  let F := subdivisionGlobalSectionsFunctor X
  let G := F.mapHomologicalComplex (.up ℤ)
  let K := singularChainSheafCochainComplex ℚ X
  let L := subdivisionLimitSheafCochainComplex X
  let φ := subdivisionSheafCochainStage X 0
  let a := G.map (K.πTruncGE b)
  let z := G.map (L.πTruncGE b)
  let c := G.map φ
  let d := G.map (CochainComplex.truncGEMap φ b)
  letI : QuasiIsoAt a i := retained_functor_truncation_quasiIsoAt F K b i hi
  letI : QuasiIsoAt z i := retained_functor_truncation_quasiIsoAt F L b i hi
  letI : QuasiIso c := retained_global_subdivision_cochain_stage_quasiIso X
  have h := congrArg (fun f => G.map f) (CochainComplex.πTruncGE_naturality φ b)
  simp only [Functor.map_comp] at h
  change a ≫ d = c ≫ z at h
  haveI : QuasiIsoAt (a ≫ d) i := by rw [h]; infer_instance
  exact quasiIsoAt_of_comp_left a d i

end HodgeLean.Foundations.QuotientDuality
