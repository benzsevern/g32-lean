import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

noncomputable section
set_option maxHeartbeats 400000
open Set Topology
namespace HodgeLean.Foundations.Program

attribute [local instance] specializationOrder in
/-- A nontrivial sober irreducible space has a strict specialization chain.
Source: the generic point of an irreducible sober space. -/
theorem s0_irreducible_krull_dimension_lower
    (X : Type*) [TopologicalSpace X] [T0Space X] [QuasiSober X]
    [IrreducibleSpace X] [Nontrivial X] : 1 ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_krullDim, Order.one_le_krullDim_iff]
  obtain ⟨x, hx⟩ := exists_ne (genericPoint X)
  exact ⟨x, genericPoint X, lt_of_le_of_ne (genericPoint_specializes x) hx⟩

#print axioms s0_irreducible_krull_dimension_lower
end HodgeLean.Foundations.Program
