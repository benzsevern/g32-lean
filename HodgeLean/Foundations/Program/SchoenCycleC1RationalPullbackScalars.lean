import HodgeLean.Foundations.Program.SchoenCycleStalkScalars

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A rational embedding retaining the actual local stalk squares preserves
all structural complex constants. -/
theorem s2e_c1_rational_pullback_complex_scalars
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (φ : Y.left.functionField →+* X.left.functionField)
    (hφ : ∀ (p : X.left) (r : Y.left.presheaf.stalk (f.left p)),
      φ (algebraMap (Y.left.presheaf.stalk (f.left p)) Y.left.functionField r) =
        algebraMap (X.left.presheaf.stalk p) X.left.functionField ((f.left.stalkMap p).hom r))
    (c : ℂ) :
    φ (HodgeLean.Foundations.Curves.stalkC (genericPoint Y.left) c) =
      HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) c := by
  letI := HodgeLean.Foundations.Curves.functionFieldAlgebra X
  letI := HodgeLean.Foundations.Curves.functionFieldAlgebra Y
  change φ (algebraMap ℂ Y.left.functionField c) = algebraMap ℂ X.left.functionField c
  rw [← HodgeLean.Foundations.Curves.algebraMap_stalkC (f.left (genericPoint X.left)) c,
    hφ, s2e_stalkMap_complex_scalars,
    HodgeLean.Foundations.Curves.algebraMap_stalkC]

end HodgeLean.Foundations.Program
