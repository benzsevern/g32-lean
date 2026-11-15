import HodgeLean.Foundations.Program.G32Native.CanonicalNormalCoordinates
import HodgeLean.Foundations.Program.SchoenCycleC2EtaleConormalFramesHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2PowerDimensionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ProjectiveCoheightHelpers

/-! # Conormal frames in the zero-pair alternative

The etale premise is U01. The conclusion is exactly U05; no change of
component, quotient map or projective identification is made.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained component has the native local conormal frames once U01 is supplied. -/
theorem g32n_canonical_conormal_frames
    (Z B₀ W₀ Q : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom]
    [IsIntegral Q.left] [Smooth Q.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (h k : ℕ) (hselected : h + 1 = 2 * k)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (β₀ : W₀ ⟶ B₀) (het : Etale β₀.left)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (ι : Q ⟶ W₀) [IsClosedImmersion ι.left] :
    ∀ x : Q.left, ∃ U : Q.left.Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict (s2c_conormal ι.left) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) := by
  letI := het
  letI : SmoothOfRelativeDimension k Q.hom := by
    rw [← s2e_projective_model_dimension Q k eQ]
    infer_instance
  have hB : TopologicalSpace.dim B₀.left = k + k := by
    rw [s2e_finite_curve_power_target_dimension Z B₀ hdimZ (h + 1) γ hγsurj,
      hselected, two_mul]
  letI : SmoothOfRelativeDimension (k + k) B₀.hom := by
    rw [← hB]
    infer_instance
  exact s2e_etale_neighbourhood_conormal_frames Q W₀ B₀ k k ι β₀ ⊤
    (fun _ _ => trivial) inferInstance

#print axioms g32n_canonical_conormal_frames
end HodgeLean.Foundations.Program
