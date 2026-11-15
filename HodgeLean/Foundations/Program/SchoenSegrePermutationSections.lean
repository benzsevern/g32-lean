import HodgeLean.Foundations.Program.SchoenSegrePowerPermutations
import HodgeLean.Foundations.Program.SchoenSegreCoordinateRenames

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual tuple-chart pullback of Segre evaluations agrees with the corresponding graded coordinate rename. -/
theorem s2_segrePowerChartPerm_sections (d n : ℕ) (a : Fin n → Fin (d + 1))
    (σ : Equiv.Perm (Fin n)) :
    (s2_segrePowerChartPerm d n a σ).appTop.hom.comp
        (s2_segrePowerSections d n (fun i => a (σ.symm i))) =
      (s2_segrePowerSections d n a).comp
        (s2_segreCoordinateRename (ULift.{0} ℤ) d n σ).toRingHom := by
  let F := (s2_segrePowerChartPerm d n a σ).appTop.hom.comp
    (s2_segrePowerSections d n (fun i => a (σ.symm i)))
  let G := (s2_segrePowerSections d n a).comp
    (s2_segreCoordinateRename (ULift.{0} ℤ) d n σ).toRingHom
  change F = G
  apply MvPolynomial.ringHom_ext
  · intro c
    have H : (F.comp C).comp (ULift.ringEquiv.symm : ℤ ≃+* ULift.{0} ℤ).toRingHom =
        (G.comp C).comp (ULift.ringEquiv.symm : ℤ ≃+* ULift.{0} ℤ).toRingHom :=
      Subsingleton.elim _ _
    exact RingHom.congr_fun H c.down
  · intro b
    change (s2_segrePowerChartPerm d n a σ).appTop.hom
        (s2_segrePowerSections d n (fun i => a (σ.symm i)) (X b)) =
      s2_segrePowerSections d n a (s2_segreCoordinateRename (ULift.{0} ℤ) d n σ (X b))
    simp only [s2_segreCoordinateRename_X, s2_segrePowerSections_X, map_prod,
      s2_segrePowerChartPerm_coord]
    simpa only [Equiv.apply_symm_apply] using
      (Equiv.prod_comp σ.symm (fun j => s2_segrePowerCoord d n a j (b (σ j))))

end HodgeLean.Foundations.Program
