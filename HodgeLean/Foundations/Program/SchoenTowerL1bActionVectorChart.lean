import HodgeLean.Foundations.Program.SchoenTowerL1bActionCenteredConjugacy
import HodgeLean.Foundations.Program.SchoenTowerL1bActionScalarClass

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Scalar form of a one-coordinate vector chart. -/
def s2v_l1b_action_vectorChart_scalar {M : Type} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ)) : OpenPartialHomeomorph M ℂ :=
  e.trans b6m_surfaceCoordinateEquiv.symm.toHomeomorph.toOpenPartialHomeomorph

/-- The centered scalar chart has exactly the translated vector target. -/
theorem s2v_l1b_action_vectorChart_centered_target
    {M : Type} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ)) (x : M) :
    (s2v_l1b_action_centerChart (s2v_l1b_action_vectorChart_scalar e) x).target =
      {z : ℂ | b6m_surfaceCoordinateEquiv z + e x ∈ e.target} := by
  ext z
  change (z ∈ Set.univ ∩ (fun z : ℂ => z + b6m_surfaceCoordinateEquiv.symm (e x)) ⁻¹'
    (Set.univ ∩ (fun w : ℂ => b6m_surfaceCoordinateEquiv w) ⁻¹' e.target)) ↔ _
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage, Set.mem_setOf_eq]
  rw [map_add, b6m_surfaceCoordinateEquiv.apply_symm_apply]

/-- Inverting the centered scalar chart is translation in vector
coordinates followed by the actual inverse chart. -/
theorem s2v_l1b_action_vectorChart_centered_inverse
    {M : Type} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ)) (x : M) (z : ℂ) :
    (s2v_l1b_action_centerChart (s2v_l1b_action_vectorChart_scalar e) x).symm z =
      e.symm (b6m_surfaceCoordinateEquiv z + e x) := by
  change e.symm (b6m_surfaceCoordinateEquiv
    (z + b6m_surfaceCoordinateEquiv.symm (e x))) = _
  rw [map_add, b6m_surfaceCoordinateEquiv.apply_symm_apply]

end HodgeLean.Foundations.Program
