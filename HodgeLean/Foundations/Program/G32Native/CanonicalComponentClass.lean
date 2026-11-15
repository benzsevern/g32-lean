import HodgeLean.Foundations.Program.G32Native.CanonicalConormalFrames
import HodgeLean.Foundations.Program.SchoenCycleC2DimensionHelpers
import HodgeLean.Adapters.NormalConeB4aClassExistsPure

/-! # A normalized class of the retained zero-pair component -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- U01 and the retained dimensions give a normalized class of the specified component. -/
theorem g32n_canonical_component_class
    (Z B₀ W₀ Q : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom]
    [IsIntegral W₀.left] [IsProjective W₀.hom] [IsIntegral Q.left] [Smooth Q.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (h k : ℕ) (hselected : h + 1 = 2 * k)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (β₀ : W₀ ⟶ B₀) (het : Etale β₀.left)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (ι : Q ⟶ W₀) [IsClosedImmersion ι.left] :
    ∃ c, a3b4_IsCycleClass W₀.hom (s2e_componentCycle ι ℚ) k c := by
  letI := het
  have hB : TopologicalSpace.dim B₀.left = k + k := by
    rw [s2e_finite_curve_power_target_dimension Z B₀ hdimZ (h + 1) γ hγsurj,
      hselected, two_mul]
  letI : SmoothOfRelativeDimension (k + k) B₀.hom := by
    rw [← hB]
    infer_instance
  letI : Smooth W₀.hom := by
    rw [← Over.w β₀]
    infer_instance
  letI : SmoothOfRelativeDimension (k + k) W₀.hom := by
    rw [← Over.w β₀]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 (k + k) β₀.left B₀.hom
  have hW : TopologicalSpace.dim W₀.left = k + k :=
    SmoothOfRelativeDimension.dim_eq W₀.hom (k + k)
  have hcod := s2e_immersion_generic_coheight_of_dimensions ι k k
    (s2e_projective_model_dimension Q k eQ) hW
  apply a3b4a_cycleClass_exists_of_codimension W₀.hom (s2e_componentCycle ι ℚ) k
  intro x hx
  rw [s2e_componentCycle_support] at hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact hcod.ge

#print axioms g32n_canonical_component_class
end HodgeLean.Foundations.Program
