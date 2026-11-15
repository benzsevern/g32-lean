import HodgeLean.Foundations.Program.CompensationAssemblyRelativeNaturality

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

def cq_relativeCircleSweep (P : TopPair.{0}) (n : ℕ) :
    RelativeHomology ℚ P n →ₗ[ℚ] RelativeHomology ℚ (cq_pairCircle P) (n + 1) :=
  (cq_circlePrismFactor n)⁻¹ • (cq_pairCircleHomologyPrism P n).hom

theorem cq_relativeCircleTrace_pairing (P : TopPair.{0}) (n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairCircle P) (n + 1)) (z : RelativeHomology ℚ P n) :
    relativeCohomologyEquivDualHomology ℚ P n (cq_relativeCircleTrace P n a) z =
      relativeCohomologyEquivDualHomology ℚ (cq_pairCircle P) (n + 1) a
        (cq_relativeCircleSweep P n z) := by
  change relativeCohomologyEquivDualHomology ℚ P n
    ((cq_circlePrismFactor n)⁻¹ • cq_pairCircleCohomologyPrism P n a) z = _
  rw [map_smul, LinearMap.smul_apply, cq_pairCircleCohomologyPrism_pairing]
  change _ = relativeCohomologyEquivDualHomology ℚ (cq_pairCircle P) (n + 1) a
    ((cq_circlePrismFactor n)⁻¹ • cq_pairCircleHomologyPrism P n z)
  rw [map_smul]

def cq_relativeTorusSweep (P : TopPair.{0}) : (k n : ℕ) →
    RelativeHomology ℚ P n →ₗ[ℚ] RelativeHomology ℚ (cq_pairCircleTower P k) (n + k)
  | 0, _ => LinearMap.id
  | k + 1, n => cq_relativeCircleSweep (cq_pairCircleTower P k) (n + k) ∘ₗ
      cq_relativeTorusSweep P k n

theorem cq_relativeTorusTrace_pairing (P : TopPair.{0}) (k n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairCircleTower P k) (n + k))
    (z : RelativeHomology ℚ P n) :
    relativeCohomologyEquivDualHomology ℚ P n (cq_relativeTorusTrace P k n a) z =
      relativeCohomologyEquivDualHomology ℚ (cq_pairCircleTower P k) (n + k) a
        (cq_relativeTorusSweep P k n z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change relativeCohomologyEquivDualHomology ℚ P n
        (cq_relativeTorusTrace P k n
          (cq_relativeCircleTrace (cq_pairCircleTower P k) (n + k) a)) z = _
      exact (ih _).trans (cq_relativeCircleTrace_pairing
        (cq_pairCircleTower P k) (n + k) a (cq_relativeTorusSweep P k n z))

def cq_relativeProductTorusSweep (P : TopPair.{0}) (k n : ℕ) :
    RelativeHomology ℚ P n →ₗ[ℚ]
      RelativeHomology ℚ (cq_pairProduct P (TopCat.of (UnitAddTorus (Fin k)))) (n + k) :=
  (relativeHomologyMap ℚ (n + k) (cq_pairTorusTowerHomeomorph P k)) ∘ₗ
    cq_relativeTorusSweep P k n

theorem cq_relativeProductTorusTrace_pairing (P : TopPair.{0}) (k n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairProduct P (TopCat.of (UnitAddTorus (Fin k)))) (n + k))
    (z : RelativeHomology ℚ P n) :
    relativeCohomologyEquivDualHomology ℚ P n (cq_relativeProductTorusTrace P k n a) z =
      relativeCohomologyEquivDualHomology ℚ _ (n + k) a
        (cq_relativeProductTorusSweep P k n z) := by
  change relativeCohomologyEquivDualHomology ℚ P n
    (cq_relativeTorusTrace P k n
      (relativeCohomologyMap ℚ (n + k) (cq_pairTorusTowerHomeomorph P k) a)) z = _
  rw [cq_relativeTorusTrace_pairing,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  rfl

def cq_relativeFibreSweep (P : TopPair.{0}) (Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) :
    RelativeHomology ℚ P n →ₗ[ℚ] RelativeHomology ℚ (cq_pairProduct P Y) (n + k) :=
  (relativeHomologyMap ℚ (n + k) (cq_pairFibreTorusMap P Y k e)) ∘ₗ
    cq_relativeProductTorusSweep P k n

theorem cq_relativeFibreTrace_pairing (P : TopPair.{0}) (Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k))
    (a : RelativeCohomology ℚ (cq_pairProduct P Y) (n + k)) (z : RelativeHomology ℚ P n) :
    relativeCohomologyEquivDualHomology ℚ P n (cq_relativeFibreTrace P Y k n e a) z =
      relativeCohomologyEquivDualHomology ℚ (cq_pairProduct P Y) (n + k) a
        (cq_relativeFibreSweep P Y k n e z) := by
  change relativeCohomologyEquivDualHomology ℚ P n
    (cq_relativeProductTorusTrace P k n
      (relativeCohomologyMap ℚ (n + k) (cq_pairFibreTorusMap P Y k e) a)) z = _
  rw [cq_relativeProductTorusTrace_pairing,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  rfl

def cq_relativeNormalizedFibreSweep (P : TopPair.{0}) (Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ) :
    RelativeHomology ℚ P n →ₗ[ℚ] RelativeHomology ℚ (cq_pairProduct P Y) (n + k) :=
  (cq_fibreIntegral Y k e (I.symm 1))⁻¹ • cq_relativeFibreSweep P Y k n e

theorem cq_relativeNormalizedFibreTrace_pairing (P : TopPair.{0}) (Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ)
    (a : RelativeCohomology ℚ (cq_pairProduct P Y) (n + k)) (z : RelativeHomology ℚ P n) :
    relativeCohomologyEquivDualHomology ℚ P n
        (cq_relativeNormalizedFibreTrace P Y k n e I a) z =
      relativeCohomologyEquivDualHomology ℚ (cq_pairProduct P Y) (n + k) a
        (cq_relativeNormalizedFibreSweep P Y k n e I z) := by
  change relativeCohomologyEquivDualHomology ℚ P n
    ((cq_fibreIntegral Y k e (I.symm 1))⁻¹ • cq_relativeFibreTrace P Y k n e a) z = _
  rw [map_smul, LinearMap.smul_apply, cq_relativeFibreTrace_pairing]
  change _ = relativeCohomologyEquivDualHomology ℚ (cq_pairProduct P Y) (n + k) a
    ((cq_fibreIntegral Y k e (I.symm 1))⁻¹ • cq_relativeFibreSweep P Y k n e z)
  rw [map_smul]

end HodgeLean.Foundations.Program
