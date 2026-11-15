import HodgeLean.Foundations.Program.CompensationAssemblyCrossComparison

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_double_pullback_singular (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (n : ℕ) (z : Cohomology ℚ (TopCat.of (ComplexPoint A)) n) :
    cohomologyMap ℚ n
      (TopCat.ofHom (Point.continuousMap ((𝟙 A : A ⟶ A) ^ (2 : ℤ)))) z =
      (2 : ℚ) ^ n • z := by
  obtain ⟨a, rfl⟩ := (cupComparison A n).surjective z
  have h : homPullback ((𝟙 A : A ⟶ A) ^ (2 : ℤ)) n a = (2 : ℚ) ^ n • a := by
    rw [spec_homPullback_zpow_degree, spec_homPullback_id, LinearMap.smul_apply,
      LinearMap.id_apply, Int.cast_ofNat]
  have he := congrArg (cupComparison A n) h
  simpa only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, map_smul] using he

end HodgeLean.Foundations.Program
