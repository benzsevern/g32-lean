import HodgeLean.Foundations.Program.SchoenCycleC1DominantGenericFieldMap
import HodgeLean.Foundations.Program.SchoenCycleC1PowerProjectionSurjective

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual curve-power coordinate projections construct injective
rational pullbacks retaining every coordinate stalk map at every tuple. -/
theorem s2e_c1_power_generic_field_maps
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (N : ℕ) :
    ∃ φ : Fin N → (Y.left.functionField →+* (g3_power Y N).left.functionField),
      ∀ i, Function.Injective (φ i) ∧
        ∀ (p : (g3_power Y N).left) (r : Y.left.presheaf.stalk ((g3_proj Y N i).left p)),
          φ i (algebraMap (Y.left.presheaf.stalk ((g3_proj Y N i).left p)) Y.left.functionField r) =
            algebraMap ((g3_power Y N).left.presheaf.stalk p) (g3_power Y N).left.functionField
              (((g3_proj Y N i).left.stalkMap p).hom r) := by
  have h (i : Fin N) := by
    letI := s2e_c1_power_projection_surjective Y N i
    exact s2e_c1_dominant_generic_field_map (g3_proj Y N i).left
  choose φ hi hs using h
  exact ⟨φ, fun i => ⟨hi i, hs i⟩⟩

end HodgeLean.Foundations.Program
