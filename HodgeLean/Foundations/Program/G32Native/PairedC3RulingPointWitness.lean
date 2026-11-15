import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedUnionGeometry
import HodgeLean.Foundations.Program.SchoenTowerFibreTopology
import HodgeLean.Foundations.Program.G32Native.PairedC3AffinePointTransport

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The diagonal chart value is a closed point on a smooth projective curve. -/
theorem paired_ruling_point_witness
    {P V : Over (Spec ↧ℂ)} (i : P ⟶ V) (M : V.left.IdealSheafData)
    (g : residualComponent (V := V) M ⟶ projectiveLine)
    (hsm : Smooth g.left)
    (sq : IsPullback (residualIntersection i M).hom
      (residualIntersectionSecond i M).left (projectiveLineChart 1 (1 : ℂ)).left g.left) :
    ∃ (C : Over (Spec ↧ℂ)) (_ : SmoothOfRelativeDimension 1 C.hom)
      (c₀ : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) (_ : IsClosedImmersion c₀.left)
      (g' : residualComponent (V := V) M ⟶ C),
      Smooth g'.left ∧ IsPullback (residualIntersection i M).hom
        (residualIntersectionSecond i M).left c₀.left g'.left := by
  let raw := projectiveLineChart 1 (1 : ℂ)
  obtain ⟨c₀, hc₀⟩ := paired_affine_self_point_transport projectiveLine raw
  refine ⟨projectiveLine, s0_complex_projective_relative_dimension 1,
    c₀, s2v_point_closedImmersion projectiveLine c₀, g, hsm, ?_⟩
  simpa only [hc₀] using sq

#print axioms paired_ruling_point_witness
end HodgeLean.Foundations.Program.G32Native
