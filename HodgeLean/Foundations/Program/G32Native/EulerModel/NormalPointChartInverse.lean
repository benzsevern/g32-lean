import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalComponentHolomorphicChart

/-! # Actual inverse formulas for the specified component point chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Every specified normal parameter lies in the actual component point-chart source. -/
theorem normalComponentPointChart_param_mem
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (z : Fin k → ℂ) :
    normalComponentHomeomorph k eQ (normalProjectiveChart k z) ∈
      (normalComponentPointChart k eQ).source := by
  rw [normalComponentPointChart_source]
  change Point.map eQ.hom
    (normalComponentHomeomorph k eQ (normalProjectiveChart k z)) ∈
      (normalSchemePointChart k).source
  have he : Point.map eQ.hom
      (normalComponentHomeomorph k eQ (normalProjectiveChart k z)) =
        normalSchemeAffineParam k z := by
    exact (Point.isoMapHomeomorph eQ.symm).symm_apply_apply _
  rw [he, normalSchemePointChart_source, normalSchemeAffineChart_source]
  exact ⟨z, rfl⟩

#print axioms normalComponentPointChart_param_mem
/-- The actual component point chart reconstructs every source point from its ordered normal coordinates. -/
theorem normalComponentPointChart_reconstruct
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (q : ComplexPoint Q) (hq : q ∈ (normalComponentPointChart k eQ).source) :
    normalComponentHomeomorph k eQ
      (normalProjectiveChart k ((normalComponentPointChart k eQ q).2)) = q := by
  apply (normalComponentPointChart k eQ).injOn
    (normalComponentPointChart_param_mem k eQ _) hq
  rw [normalComponentPointChart_param]
  exact Prod.ext (Subsingleton.elim _ _) rfl

#print axioms normalComponentPointChart_reconstruct
end HodgeLean.Foundations.Program.G32Native.EulerModel
