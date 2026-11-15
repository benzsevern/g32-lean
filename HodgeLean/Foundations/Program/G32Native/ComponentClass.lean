import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2PowerDimensionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ProjectiveCoheightHelpers
import HodgeLean.Adapters.NormalConeB4aClassExistsPure

/-! # Local frames and the normalized class of a projective component -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native

/-- A projective component in a smooth finite curve-power quotient has the
expected conormal rank and a normalized supported class. -/
theorem component_frames_and_class
    (Y Q W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom]
    [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    [IsIntegral W.left] [Smooth W.hom] [IsProjective W.hom]
    (hdimY : dim Y.left = 1) (N k : ℕ) (hN : N = 2 * k)
    (q : g3_power Y N ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] :
    (∀ x : Q.left, ∃ U : Q.left.Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict (s2c_conormal ι.left) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))) ∧
    ∃ c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k,
      a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c := by
  have hQ := s2e_projective_model_dimension Q k eQ
  have hW : dim W.left = k + k := by
    rw [s2e_finite_curve_power_target_dimension Y W hdimY N q hqsurj, hN, two_mul]
  letI : SmoothOfRelativeDimension k Q.hom := by
    rw [← hQ]
    infer_instance
  letI : SmoothOfRelativeDimension (k + k) W.hom := by
    rw [← hW]
    infer_instance
  refine ⟨s2e_smooth_closedImmersion_conormal_frames Q W k k ι, ?_⟩
  apply a3b4a_cycleClass_exists_of_codimension
  intro x hx
  rw [s2e_componentCycle_support] at hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact (s2e_immersion_generic_coheight_of_dimensions ι k k hQ hW).ge

#print axioms component_frames_and_class
end HodgeLean.Foundations.Program.G32Native
