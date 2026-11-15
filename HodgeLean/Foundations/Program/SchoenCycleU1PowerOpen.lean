import HodgeLean.Foundations.Program.SchoenCycleStep1

/-! # Actual coordinate opens in a curve power -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The open where every factor of the retained curve power lies in a specified curve open.
Source: Hartshorne, Algebraic Geometry, II.3, products and inverse-image opens. -/
def s2e_u1_powerOpen (Z : Over (Spec ↧ℂ)) (N : ℕ) (U : Z.left.Opens) :
    (g3_power Z N).left.Opens := ⨅ i : Fin N, (g3_proj Z N i).left ⁻¹ᵁ U

/-- Coordinate opens impose the specified condition on every actual scheme point,
without discarding repeated coordinates.
Source: Hartshorne, Algebraic Geometry, II.3, products and inverse-image opens. -/
theorem s2e_u1_mem_powerOpen (Z : Over (Spec ↧ℂ)) (N : ℕ) (U : Z.left.Opens)
    (x : (g3_power Z N).left) :
    x ∈ s2e_u1_powerOpen Z N U ↔ ∀ i, (g3_proj Z N i).left x ∈ U := by
  change x ∈ (((⨅ i : Fin N, (g3_proj Z N i).left ⁻¹ᵁ U) :
    (g3_power Z N).left.Opens) : Set (g3_power Z N).left) ↔ _
  rw [Opens.coe_iInf]
  simp only [Set.mem_iInter]
  rfl

/-- Permuting the factors preserves the open where all coordinates lie in the same curve open.
Source: Hartshorne, Algebraic Geometry, II.3, products. -/
theorem s2e_u1_powerOpen_permute (Z : Over (Spec ↧ℂ)) (N : ℕ) (U : Z.left.Opens)
    (σ : Equiv.Perm (Fin N)) :
    s2e_u1_powerOpen Z N U ≤ (s2_permute Z N σ).left ⁻¹ᵁ s2e_u1_powerOpen Z N U := by
  intro x hx
  apply (s2e_u1_mem_powerOpen Z N U _).mpr
  intro i
  have he : (s2_permute Z N σ ≫ g3_proj Z N i).left =
      (g3_proj Z N (σ.symm i)).left := by
    congr 1
    simp only [s2_permute, s2_check_lift_proj]
  change ((s2_permute Z N σ ≫ g3_proj Z N i).left) x ∈ U
  rw [he]
  exact (s2e_u1_mem_powerOpen Z N U x).mp hx _

end HodgeLean.Foundations.Program
