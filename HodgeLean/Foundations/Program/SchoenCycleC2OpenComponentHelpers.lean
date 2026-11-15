import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
import Mathlib.AlgebraicGeometry.Morphisms.Separated

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A component lying in a scheme open factors through it as an immersion,
and its prime-cycle coheight is preserved. -/
theorem s2e_componentCycle_factor_open
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U) (k : ℕ)
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k) :
    ∃ j : Q ⟶ ComplexPoint.openScheme W U,
      j ≫ ComplexPoint.openInclusion W U = ι ∧ IsClosedImmersion j.left ∧
      ∀ x ∈ (s2e_componentCycle j ℚ).support, Order.coheight x = k := by
  have hRange : Set.range ι.left ⊆ Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  let j := IsOpenImmersion.lift U.ι ι.left hRange
  have hj : j ≫ U.ι = ι.left := IsOpenImmersion.lift_fac _ _ _
  have hjbase : j ≫ (ComplexPoint.openScheme W U).hom = Q.hom := by
    change j ≫ U.ι ≫ W.hom = Q.hom
    rw [← Category.assoc, hj, Over.w ι]
  let jOver : Q ⟶ ComplexPoint.openScheme W U := Over.homMk j hjbase
  haveI : IsClosedImmersion (j ≫ U.ι) := by rw [hj]; infer_instance
  haveI : IsClosedImmersion j := IsClosedImmersion.of_comp j U.ι
  refine ⟨jOver, ?_, inferInstanceAs (IsClosedImmersion j), ?_⟩
  · apply Over.OverMorphism.ext
    exact hj
  · intro x hx
    rw [s2e_componentCycle_support] at hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    have hc := hcodim (ι.left (genericPoint Q.left)) (by
      rw [s2e_componentCycle_support]
      exact Set.mem_singleton _)
    have hpoint : U.ι (j (genericPoint Q.left)) = ι.left (genericPoint Q.left) :=
      congrArg (fun f : Q.left ⟶ W.left => f (genericPoint Q.left)) hj
    rw [← hpoint, coheight_eq_of_isOpenImmersion] at hc
    exact hc

end HodgeLean.Foundations.Program
