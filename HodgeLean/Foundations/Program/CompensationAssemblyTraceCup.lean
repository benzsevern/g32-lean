import HodgeLean.Foundations.Program.CompensationAssemblyCircleTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_circleTrace_pullback (X : TopCat.{0}) (n : ℕ)
    (a : Cohomology ℚ X (n + 1)) :
    cq_circleTrace X n
      (cohomologyMap ℚ (n + 1) (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) = 0 := by
  have he : prodCircleCohomologyEquiv X n (a, 0) =
      cohomologyMap ℚ (n + 1) (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a := by
    rw [prodCircleCohomologyEquiv_apply, map_zero, map_zero, LinearMap.zero_apply,
      add_zero]
  change ((prodCircleCohomologyEquiv X n).symm
    (cohomologyMap ℚ (n + 1) (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)).2 = 0
  rw [← he, LinearEquiv.symm_apply_apply]

theorem cq_circleTrace_cup_circleClass (X : TopCat.{0}) (n : ℕ)
    (b : Cohomology ℚ X n) :
    cq_circleTrace X n
      (cup (TopCat.of (X × UnitAddCircle)) rfl
        (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) b)
        (cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) circleClass)) = b := by
  have he : prodCircleCohomologyEquiv X n (0, b) =
      cup (TopCat.of (X × UnitAddCircle)) rfl
        (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) b)
        (cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) circleClass) := by
    rw [prodCircleCohomologyEquiv_apply, map_zero, zero_add]
  change ((prodCircleCohomologyEquiv X n).symm _).2 = b
  rw [← he, LinearEquiv.symm_apply_apply]

end HodgeLean.Foundations.Program
