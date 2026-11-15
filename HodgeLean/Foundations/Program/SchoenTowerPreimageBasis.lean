import HodgeLean.Foundations.Program.SchoenTowerFinitePointFibres
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2v_preimage_contractible_basis {W B E : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (x : ComplexPoint (s2b_preimage β j))
    (U : TopologicalSpace.Opens (ComplexPoint (s2b_preimage β j))) (hx : x ∈ U) :
    ∃ V : TopologicalSpace.Opens (ComplexPoint (s2b_preimage β j)),
      x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  letI := s2v_preimage_projection_finite β j
  letI : LocallyOfFiniteType (s2b_preimage β j).hom := by
    rw [← (s2b_toExceptional β j).w]
    infer_instance
  exact HodgeLean.Foundations.ComplexTopology.finiteType_basis
    (s2b_preimage β j) x U hx

end HodgeLean.Foundations.Program
