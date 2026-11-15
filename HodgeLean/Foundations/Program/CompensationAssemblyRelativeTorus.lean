import HodgeLean.Foundations.Program.CompensationAssemblyRelativeTrace
import HodgeLean.Foundations.Program.CompensationAssemblyTorusTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem cq_circleTowerMap_isEmbedding {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : Topology.IsEmbedding f) (k : ℕ) : Topology.IsEmbedding (cq_circleTowerMap f k) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact ih.prodMap Topology.IsEmbedding.id

def cq_pairCircleTower (P : TopPair.{0}) (k : ℕ) : TopPair.{0} :=
  TopPair.of (cq_circleTowerMap P.map k)
    (cq_circleTowerMap_isEmbedding P.map P.isEmbedding_map k)

def cq_relativeTorusTrace (P : TopPair.{0}) : (k n : ℕ) →
    RelativeCohomology ℚ (cq_pairCircleTower P k) (n + k) →ₗ[ℚ] RelativeCohomology ℚ P n
  | 0, _ => LinearMap.id
  | k + 1, n => cq_relativeTorusTrace P k n ∘ₗ
      cq_relativeCircleTrace (cq_pairCircleTower P k) (n + k)

set_option backward.isDefEq.respectTransparency false in
theorem cq_relativeTorusTrace_absolute (P : TopPair.{0}) (k n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairCircleTower P k) (n + k)) :
    relativeCohomologyToAbsolute ℚ P n (cq_relativeTorusTrace P k n a) =
      cq_torusTrace P.fst k n
        (relativeCohomologyToAbsolute ℚ (cq_pairCircleTower P k) (n + k) a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change relativeCohomologyToAbsolute ℚ P n
        (cq_relativeTorusTrace P k n
          (cq_relativeCircleTrace (cq_pairCircleTower P k) (n + k) a)) = _
      rw [ih, cq_relativeCircleTrace_absolute]
      rfl

def cq_pairCircleTowerMap {P Q : TopPair.{0}} (a : P ⟶ Q) :
    (k : ℕ) → cq_pairCircleTower P k ⟶ cq_pairCircleTower Q k
  | 0 => a
  | k + 1 => cq_pairCircleMap (cq_pairCircleTowerMap a k)

theorem cq_relativeTorusTrace_naturality {P Q : TopPair.{0}} (a : P ⟶ Q) (k n : ℕ)
    (c : RelativeCohomology ℚ (cq_pairCircleTower Q k) (n + k)) :
    cq_relativeTorusTrace P k n
        (relativeCohomologyMap ℚ (n + k) (cq_pairCircleTowerMap a k) c) =
      relativeCohomologyMap ℚ n a (cq_relativeTorusTrace Q k n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact (congrArg (cq_relativeTorusTrace P k n)
        (cq_relativeCircleTrace_naturality (cq_pairCircleTowerMap a k) (n + k) c)).trans (ih _)

end HodgeLean.Foundations.Program
