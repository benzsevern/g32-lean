import HodgeLean.Foundations.Program.SchoenCycleClassDefs
import HodgeLean.Foundations.Program.SchoenCycleStageDefs
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.ClosedImmersion

/-! The literal support and coefficient of a native point cycle. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters Classical
namespace HodgeLean.Foundations.Program.G32Native

/-- The scheme-image point cycle is the coefficient-one cycle at its underlying point. -/
theorem point_cycle_single (X : Over (Spec ↧ℂ)) (x : ComplexPoint X) :
    s2e_componentCycle x ℚ = Function.locallyFinsuppWithin.single x.underlying 1 := by
  unfold s2e_componentCycle Point.underlying
  congr 1
  exact congrArg x.left (show (_ : PrimeSpectrum ℂ) = _ from Subsingleton.elim _ _)

/-- The analytic support of the native point cycle is the same singleton. -/
theorem point_cycle_support (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (x : ComplexPoint X) :
    a3b4_cycleSupport X.hom (s2e_componentCycle x ℚ) = {x} := by
  classical
  have hc : IsClosed ({x.underlying} : Set X.left) :=
    ((pointEquivClosedPoint X.hom) ⟨x.left, by simp⟩).2
  have hs : (s2e_componentCycle x ℚ).support = {x.underlying} := by
    ext ξ
    change (s2e_componentCycle x ℚ) ξ ≠ 0 ↔ ξ = x.underlying
    rw [point_cycle_single]
    simp only [Function.locallyFinsuppWithin.single_apply]
    split_ifs with h <;> simp_all only [ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]
  ext y
  change y.underlying ∈ ⋃ ξ ∈ (s2e_componentCycle x ℚ).support, closure {ξ} ↔ y = x
  rw [hs]
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_eq_left, exists_prop]
  simp only [hc.closure_eq, Set.mem_singleton_iff]
  haveI : LocallyOfFiniteType (Over.mk X.hom).hom := ‹LocallyOfFiniteType X.hom›
  exact ⟨fun h => underlying_injective_of_locallyOfFiniteType h, congrArg Point.underlying⟩

/-- The local multiplicity of the native point cycle is exactly one. -/
theorem point_cycle_multiplicity (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : ComplexPoint X) :
    a3b4_multiplicity X.hom (s2e_componentCycle x ℚ) x = 1 := by
  classical
  have hs : x.underlying ∈ (s2e_componentCycle x ℚ).support := by
    change (s2e_componentCycle x ℚ) x.underlying ≠ 0
    rw [point_cycle_single]
    simp only [Function.locallyFinsuppWithin.single_apply, ite_true, one_ne_zero, ne_eq, not_false_eq_true]
  have hother : ∀ ξ ∈ (s2e_componentCycle x ℚ).support, ξ ≠ x.underlying →
      x.underlying ∉ closure ({ξ} : Set X.left) := by
    intro ξ hξ hne
    change (s2e_componentCycle x ℚ) ξ ≠ 0 at hξ
    rw [point_cycle_single, Function.locallyFinsuppWithin.single_apply, if_neg hne] at hξ
    exact (hξ rfl).elim
  rw [a3b4a_classMultiplicity_eq_component X.hom _ x.underlying hs x
    (subset_closure (Set.mem_singleton _)) hother, point_cycle_single]
  simp

#print axioms point_cycle_single
#print axioms point_cycle_support
#print axioms point_cycle_multiplicity
end HodgeLean.Foundations.Program.G32Native
