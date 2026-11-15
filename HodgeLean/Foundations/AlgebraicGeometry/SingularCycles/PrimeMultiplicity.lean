import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Support

/-! # Local multiplicity of a coefficient-one prime

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters TopologicalSpace
namespace AlgebraicGeometry.SingularCycles

/-- The local multiplicity test of a coefficient-one prime has value one.
Source: Fulton, Intersection Theory, second edition, §1.5; a3b4_multiplicity. -/
theorem prime_cycle_multiplicity_one (Z : Over (Spec ↧ℂ)) [QuasiCompact Z.hom]
    (x : Z.left) (z : ComplexPoint Z) :
    a3b4_multiplicity Z.hom (Function.locallyFinsuppWithin.single x (1 : ℚ)) z = 1 := by
  haveI := a3b4_compactSpace Z.hom
  have hs : (Function.locallyFinsuppWithin.single x (1 : ℚ) : AlgebraicCycle Z.left ℚ).support =
      {x} := by
    ext y
    simp [Function.locallyFinsuppWithin.support, Function.support,
      Function.locallyFinsuppWithin.single_apply]
  have hfin : (a3b2_support_finite
      (Function.locallyFinsuppWithin.single x (1 : ℚ) : AlgebraicCycle Z.left ℚ)).toFinset =
      {x} := by
    ext y
    simp [hs]
  unfold a3b4_multiplicity
  rw [hfin]
  simp only [Finset.sum_singleton, Function.locallyFinsuppWithin.single_apply, ite_true]
  rw [if_pos]
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, ?_⟩
  rw [prime_cycle_analytic_support]
  exact Set.inter_subset_right

end AlgebraicGeometry.SingularCycles
