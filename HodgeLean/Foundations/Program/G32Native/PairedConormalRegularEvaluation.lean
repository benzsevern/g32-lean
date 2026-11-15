import HodgeLean.Foundations.BundleThom.LocalSectionSpecializationHelpers
/-! # Actual regular evaluation through the supplied point's section map -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Evaluation on a containing open is exactly the supplied actual complex point's section map. -/
theorem conormal_regular_evaluation_eq_appLE {Q : Over (Spec ↧ℂ)}
    (U : Q.left.Opens) (r : Γ(Q.left, U)) (x : ComplexPoint Q)
    (h : (⊤ : (Spec ↧ℂ).Opens) ≤ x.left ⁻¹ᵁ U) :
    Point.evaluate U r x = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (x.left.appLE U ⊤ h r) := by
  have hx : x.underlying ∈ U := h trivial
  rw [Point.evaluate, dite_eq_left hx]
  have hh := ConcreteCategory.congr_hom (Scheme.germ_stalkClosedPointTo x.left U hx) r
  convert! hh using 1

/-- The specified open lift evaluates the same original section with the actual top-open comparison. -/
theorem conormal_open_lift_section_map {Q : Over (Spec ↧ℂ)}
    (U : Q.left.Opens) (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U)
    (h : (⊤ : (Spec ↧ℂ).Opens) ≤ x.left ⁻¹ᵁ U) :
    U.topIso.inv ≫ (ComplexPoint.liftToOpen Q U x hx).appTop = x.left.appLE U ⊤ h := by
  let a := ComplexPoint.liftToOpen Q U x hx
  have hc := Scheme.Hom.appLE_comp_appLE a U.ι U ⊤ ⊤ (by simp) (by simp)
  convert hc using 1
  · have ht : a.appLE ⊤ ⊤ (by simp) = a.appTop := by simp [Scheme.Hom.appLE]
    rw [ht]
    congr 1
    all_goals simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    all_goals rfl
  · congr 1
    all_goals exact (ComplexPoint.liftToOpen_fac Q U x hx).symm

end HodgeLean.Foundations.Program.G32Native
