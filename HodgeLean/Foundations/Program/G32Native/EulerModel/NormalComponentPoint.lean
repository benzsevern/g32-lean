import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalCoordinatePoint
import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinateClasses

/-! # The same coordinate point on the specified actual component -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual normal model base transported through the specified component isomorphism. -/
def normalComponentHomeomorph
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    Projectivization ℂ (ℂ × (Fin k → ℂ)) ≃ₜ ComplexPoint Q :=
  (normalProjectiveSchemeHomeomorph k).trans (Point.isoMapHomeomorph eQ.symm)

/-- The same actual coordinate ideal on the chosen component retains the distinguished point support. -/
theorem normalComponentHomeomorph_point_support
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    (normalComponentHomeomorph k eQ p).underlying ∈
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left).support ↔
        p = normalProjectiveBase k := by
  rw [Scheme.IdealSheafData.support_comap]
  change (Point.map eQ.hom (normalComponentHomeomorph k eQ p)).underlying ∈
    (s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).support ↔ _
  have he : Point.map eQ.hom (normalComponentHomeomorph k eQ p) =
      normalProjectiveSchemeHomeomorph k p := by
    exact (Point.isoMapHomeomorph eQ.symm).symm_apply_apply _
  rw [he]
  exact normal_coordinate_point_support k p

#print axioms normalComponentHomeomorph
#print axioms normalComponentHomeomorph_point_support
/-- The actual component cycle of the coordinate point has precisely the model's distinguished point as support. -/
theorem normalComponentHomeomorph_cycle_support
    {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    normalComponentHomeomorph k eQ p ∈
      HodgeLean.Adapters.a3b4_cycleSupport Q.hom
        (s2e_componentCycle (s2c_subschemeι Q
          ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) ↔
        p = normalProjectiveBase k := by
  let I := (s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left
  letI : IsClosedImmersion (s2c_subschemeι Q I).left :=
    inferInstanceAs (IsClosedImmersion I.subschemeι)
  rw [s2e_componentCycle_analytic_support]
  change (normalComponentHomeomorph k eQ p).underlying ∈ Set.range I.subschemeι ↔ _
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact normalComponentHomeomorph_point_support k eQ p

#print axioms normalComponentHomeomorph_cycle_support
end HodgeLean.Foundations.Program.G32Native.EulerModel
