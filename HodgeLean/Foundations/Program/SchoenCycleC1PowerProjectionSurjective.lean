import HodgeLean.Foundations.Program.SchoenCycleGeometryChecks

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Each actual curve-power projection is surjective on all scheme points,
using the original product diagonal as its section. -/
theorem s2e_c1_power_projection_surjective
    (Y : Over (Spec ↧ℂ)) (N : ℕ) (i : Fin N) : Surjective (g3_proj Y N i).left := by
  have hdiag : s2_lift N (fun _ => 𝟙 Y) ≫ g3_proj Y N i = 𝟙 Y :=
    s2_check_lift_proj N (fun _ => 𝟙 Y) i
  constructor
  intro y
  refine ⟨(s2_lift N (fun _ => 𝟙 Y)).left y, ?_⟩
  exact congrArg (fun f : Y ⟶ Y => f.left y) hdiag

end HodgeLean.Foundations.Program
