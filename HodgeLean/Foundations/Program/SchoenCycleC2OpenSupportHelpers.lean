import HodgeLean.Foundations.Program.SchoenCycleC2OpenComponentHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2EmbeddingExcisionHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Component support pulls back to the support of its factor through an open immersion. -/
theorem s2e_componentCycle_support_open_preimage
    {Q V W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (j : Q ⟶ V) (i : V ⟶ W)
    [IsClosedImmersion j.left] [IsOpenImmersion i.left]
    [IsClosedImmersion (j ≫ i).left] :
    a3b4_cycleSupport V.hom (s2e_componentCycle j ℚ) =
      Point.map i ⁻¹' a3b4_cycleSupport W.hom (s2e_componentCycle (j ≫ i) ℚ) := by
  rw [s2e_componentCycle_analytic_support, s2e_componentCycle_analytic_support]
  ext x
  change x.underlying ∈ Set.range j.left ↔
    (Point.map i x).underlying ∈ Set.range (j ≫ i).left
  rw [Point.underlying_map]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, congrArg i.left hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, i.left.isOpenEmbedding.injective hq⟩

end HodgeLean.Foundations.Program
