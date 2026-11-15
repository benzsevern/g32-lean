import HodgeLean.Foundations.Program.SchoenTransferJ12SumReflectionMixedData
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveGeometricRetractionData
import HodgeLean.Foundations.Program.SchoenTransferJ12PointTopCoordinate

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Positive-dimensional abelian targets reflect actual curve-power cycles through their generating sums.
Source: the actual Abel adjoint data and the geometric mixed product retraction. -/
theorem s4_selected_sum_reflection_positive_dimension
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (ha : 1 ≤ TopologicalSpace.dim A.left) (hdim : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ A) (hf : Function.Injective (homPullback f 1)) (k : ℕ)
    [IsIntegral (g3_power Y (2 * k)).left] [Smooth (g3_power Y (2 * k)).hom]
    [IsProjective (g3_power Y (2 * k)).hom]
    (x : HQ A (2 * k))
    (hx : homPullback (s4_sum f (2 * k)) (2 * k) x ∈ cfd_cycleSpan (g3_power Y (2 * k)) k) :
    x ∈ cfd_cycleSpan A k := by
  letI := connectedSpace_complexPoint Y
  let eY : ComplexPoint Y := Classical.choice inferInstance
  obtain ⟨_, IY, _⟩ := s4_selected_point_top_coordinate Y 1 hdim eY
  have hpower : TopologicalSpace.dim (g3_power Y (2 * k)).left = 2 * k := by
    letI : SmoothOfRelativeDimension 1 Y.hom := by
      have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
      rwa [hdim] at h
    letI : SmoothOfRelativeDimension (2 * k) (g3_power Y (2 * k)).hom := by
      simpa using spec_g3_smoothOfRelativeDimension_power Y 1 (2 * k)
    exact SmoothOfRelativeDimension.dim_eq (f := (g3_power Y (2 * k)).hom) (2 * k)
  letI := connectedSpace_complexPoint (g3_power Y (2 * k))
  let eT : ComplexPoint (g3_power Y (2 * k)) := Classical.choice inferInstance
  obtain ⟨_, IT, _⟩ := s4_selected_point_top_coordinate (g3_power Y (2 * k)) (2 * k) hpower eT
  obtain ⟨pol, hpol, g, c, hc, hact⟩ :=
    s4_selected_curve_geometric_retraction_data A Y hdim f hf IY
  have hact' : (s4_selected_corr_action A Y 1 IY 1 1 1 (by omega)
      (s4_selected_curve_mixed_divisor A Y g pol)).comp (homPullback f 1) =
        (c : ℚ) • LinearMap.id := by
    ext v
    exact hact v
  exact s4_selected_sum_reflection_from_mixed_data A Y ha hdim f g k IY IT pol hpol
    (c : ℚ) (Nat.cast_ne_zero.mpr hc.ne') hact' x hx

#print axioms s4_selected_sum_reflection_positive_dimension
end HodgeLean.Foundations.Program
