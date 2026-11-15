import HodgeLean.Foundations.Program.CompensationAssemblyPrismTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

def cq_relativeCircleTrace (P : TopPair.{0}) (n : ℕ) :
    RelativeCohomology ℚ (cq_pairCircle P) (n + 1) →ₗ[ℚ] RelativeCohomology ℚ P n :=
  (cq_circlePrismFactor n)⁻¹ • cq_pairCircleCohomologyPrism P n

set_option backward.isDefEq.respectTransparency false in
theorem cq_relativeCircleTrace_absolute (P : TopPair.{0}) (n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairCircle P) (n + 1)) :
    relativeCohomologyToAbsolute ℚ P n (cq_relativeCircleTrace P n a) =
      cq_circleTrace P.fst n
        (relativeCohomologyToAbsolute ℚ (cq_pairCircle P) (n + 1) a) := by
  change relativeCohomologyToAbsolute ℚ P n
    ((cq_circlePrismFactor n)⁻¹ • cq_pairCircleCohomologyPrism P n a) = _
  rw [map_smul, ← cq_circleCohomologyPrism_relative,
    cq_circlePrism_eq_factor_trace, smul_smul,
    inv_mul_cancel₀ (cq_circlePrismFactor_ne_zero n), one_smul]

theorem cq_relativeCircleTrace_naturality {P Q : TopPair.{0}} (a : P ⟶ Q)
    (n : ℕ) (c : RelativeCohomology ℚ (cq_pairCircle Q) (n + 1)) :
    cq_relativeCircleTrace P n (relativeCohomologyMap ℚ (n + 1) (cq_pairCircleMap a) c) =
      relativeCohomologyMap ℚ n a (cq_relativeCircleTrace Q n c) := by
  change (cq_circlePrismFactor n)⁻¹ • cq_pairCircleCohomologyPrism P n
    (relativeCohomologyMap ℚ (n + 1) (cq_pairCircleMap a) c) =
      relativeCohomologyMap ℚ n a
        ((cq_circlePrismFactor n)⁻¹ • cq_pairCircleCohomologyPrism Q n c)
  rw [cq_pairCircleCohomologyPrism_naturality, map_smul]

end HodgeLean.Foundations.Program
