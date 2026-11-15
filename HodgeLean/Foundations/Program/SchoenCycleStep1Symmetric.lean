import HodgeLean.Foundations.Program.SchoenCycleStep1PointEvaluation
import HodgeLean.Foundations.GeometricIntegralityC

/-! # Scheme surjectivity and the retained permutation action -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A closed image containing every complex point contains every scheme point. -/
theorem s2e_step1_surjective_of_complexPoint_surjective
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [UniversallyClosed f.left]
    (hsurj : Function.Surjective (Point.map f)) : Surjective f.left := by
  letI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hc : closedPoints Y.left ⊆ Set.range f.left := by
    intro y hy
    let yp : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy) (by simp)
    have hyp : yp.underlying = y := pointOfClosedPoint_apply Y.hom y hy _
    obtain ⟨xp, hxp⟩ := hsurj yp
    refine ⟨xp.underlying, ?_⟩
    have he := congrArg Point.underlying hxp
    rw [Point.underlying_map] at he
    exact he.trans hyp
  have ht : Set.univ ⊆ Set.range f.left := by
    rw [← closure_closedPoints (X := Y.left)]
    exact closure_minimal hc f.left.isClosedMap.isClosed_range
  exact ⟨fun y => ht trivial⟩

/-- The identity permutation induces the identity on the retained scheme power. -/
theorem s2e_step1_permute_one (Z : Over (Spec ↧ℂ)) (N : ℕ) :
    s2_permute Z N 1 = 𝟙 (g3_power Z N) := by
  apply s2e_power_hom_ext
  intro i
  simp only [s2_permute, s2_check_lift_proj, Category.id_comp]
  rfl

/-- The retained coordinate maps satisfy the permutation action multiplication law. -/
theorem s2e_step1_permute_mul (Z : Over (Spec ↧ℂ)) (N : ℕ)
    (u v : Equiv.Perm (Fin N)) :
    s2_permute Z N (u * v) = s2_permute Z N v ≫ s2_permute Z N u := by
  apply s2e_power_hom_ext
  intro i
  simp only [Category.assoc, s2_permute, s2_check_lift_proj]
  rfl

end HodgeLean.Foundations.Program
