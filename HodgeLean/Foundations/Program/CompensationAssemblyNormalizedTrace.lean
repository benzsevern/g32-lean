import HodgeLean.Foundations.Program.CompensationAssemblyFibreModule

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

def cq_normalizedFibreTrace (X Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ) :
    Cohomology ℚ (TopCat.of (X × Y)) (n + k) →ₗ[ℚ] Cohomology ℚ X n :=
  (cq_fibreIntegral Y k e (I.symm 1))⁻¹ • cq_fibreTrace X Y k n e

theorem cq_normalizedFibreTrace_cross (X Y : TopCat.{0}) (k i : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ)
    (a : Cohomology ℚ X i) (b : Cohomology ℚ Y (0 + k)) :
    cq_normalizedFibreTrace X Y k (i + 0) e I
      (cup (TopCat.of (X × Y)) (Nat.add_assoc i 0 k).symm
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)
        (cohomologyMap ℚ (0 + k) (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) b)) =
      I b • a := by
  rw [cq_normalizedFibreTrace, LinearMap.smul_apply, cq_fibreTrace_cross,
    cq_fibreIntegral_eq_scalar Y k e I b, smul_smul, mul_left_comm,
    inv_mul_cancel₀ (cq_fibreIntegral_unit_ne_zero Y k e I), mul_one]

theorem cq_normalizedFibreTrace_naturality {U X : TopCat.{0}} (f : U ⟶ X)
    (Y : TopCat.{0}) (k n : ℕ) (e : Y ≃ₜ UnitAddTorus (Fin k))
    (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ)
    (c : Cohomology ℚ (TopCat.of (X × Y)) (n + k)) :
    cq_normalizedFibreTrace U Y k n e I
      (cohomologyMap ℚ (n + k) (cq_fibreProductMap f Y) c) =
      cohomologyMap ℚ n f (cq_normalizedFibreTrace X Y k n e I c) := by
  simp only [cq_normalizedFibreTrace, LinearMap.smul_apply, map_smul]
  rw [cq_fibreTrace_naturality]

end HodgeLean.Foundations.Program
