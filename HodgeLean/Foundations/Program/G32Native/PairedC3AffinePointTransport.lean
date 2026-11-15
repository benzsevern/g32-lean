import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineChart

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A point over the scalar self-map has the same underlying map over the identity. -/
theorem paired_affine_self_point_transport (C : Over (Spec ↧ℂ))
    (raw : Over.mk (ComplexPoint.affineSpecStructureMap ℂ) ⟶ C) :
    ∃ c₀ : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C, c₀.left = raw.left := by
  have hid : ComplexPoint.affineSpecStructureMap ℂ = 𝟙 (Spec ↧ℂ) := by
    change Spec.map (𝟙 (CommRingCat.of ℂ)) = 𝟙 _
    rw [Spec.map_id]
  exact ⟨Over.homMk raw.left ((Over.w raw).trans hid), rfl⟩

#print axioms paired_affine_self_point_transport
end HodgeLean.Foundations.Program.G32Native
