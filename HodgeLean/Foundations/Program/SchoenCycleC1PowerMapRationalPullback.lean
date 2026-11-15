import HodgeLean.Foundations.Program.SchoenCycleC1DominantGenericFieldMap
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric
import HodgeLean.Foundations.Program.SchoenPowerComplexPoints

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual surjective curve projection constructs a rational pullback
on its power map retaining every original local stalk square. -/
theorem s2e_c1_power_map_rational_pullback
    (Y Z : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (p : Y ⟶ Z) (hp : Function.Surjective (Point.map p)) (N : ℕ) :
    ∃ ρ : (g3_power Z N).left.functionField →+* (g3_power Y N).left.functionField,
      Function.Injective ρ ∧
      ∀ x (r : (g3_power Z N).left.presheaf.stalk ((s2_powerMap p N).left x)),
        ρ (algebraMap ((g3_power Z N).left.presheaf.stalk ((s2_powerMap p N).left x))
          (g3_power Z N).left.functionField r) =
          algebraMap ((g3_power Y N).left.presheaf.stalk x) (g3_power Y N).left.functionField
            (((s2_powerMap p N).left.stalkMap x).hom r) := by
  letI : IsProper ((s2_powerMap p N).left ≫ (g3_power Z N).hom) := by
    rw [Over.w]
    infer_instance
  letI : IsProper (s2_powerMap p N).left :=
    IsProper.of_comp _ (g3_power Z N).hom
  letI : Surjective (s2_powerMap p N).left :=
    s2e_step1_surjective_of_complexPoint_surjective (g3_power Y N) (g3_power Z N)
      (s2_powerMap p N) (s2_powerMap_point_surjective p hp N)
  exact s2e_c1_dominant_generic_field_map (s2_powerMap p N).left

end HodgeLean.Foundations.Program
