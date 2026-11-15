import HodgeLean.Foundations.Program.SchoenSelectedGeometryComplexFibers

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Set Topology
namespace HodgeLean.Foundations.Program

attribute [local instance] specializationOrder in
/-- A locally quasi-finite morphism cannot increase the dimension of its source.
Source: specialization chains map strictly because fibres are discrete. -/
theorem s0_quasiFinite_krull_dimension_le {X Y : Scheme.{0}}
    (f : X ⟶ Y) [LocallyQuasiFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_krullDim, topologicalKrullDim_eq_krullDim]
  apply Order.krullDim_le_of_strictMono f
  intro x y hxy
  have hs : y ⤳ x := hxy.le
  refine lt_of_le_of_ne (hs.map f.continuous) ?_
  intro he
  letI : DiscreteTopology (f ⁻¹' {f x}) := isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton (f x))
  have hsub : (⟨y, he.symm⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ :=
    (subtype_specializes_iff _ _).mpr hs
  exact hxy.ne (congrArg Subtype.val hsub.eq).symm

#print axioms s0_quasiFinite_krull_dimension_le
end HodgeLean.Foundations.Program
