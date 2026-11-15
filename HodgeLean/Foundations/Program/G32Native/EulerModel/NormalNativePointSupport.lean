import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalNativeHolomorphicChart
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalComponentPointClass

/-! # Native holomorphic flattening of the literal coordinate-point cycle -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual native point chart flattens the literal coordinate-point component-cycle support. -/
theorem normalSchemePointChart_support (k : ℕ)
    [IsIntegral (s2c_subscheme
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      (s2e_s2b_intersectionIdeal k (Finset.univ.erase 0))).left]
    (q : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
    (hq : q ∈ (normalSchemePointChart k).source) :
    q ∈ a3b4_cycleSupport (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
      (s2e_componentCycle (s2c_subschemeι
        (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
        (s2e_s2b_intersectionIdeal k (Finset.univ.erase 0))) ℚ) ↔
      (normalSchemePointChart k q).2 = 0 := by
  let P := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let I := s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)
  letI : IsClosedImmersion (s2c_subschemeι P I).left :=
    inferInstanceAs (IsClosedImmersion I.subschemeι)
  rw [normalSchemePointChart_source, normalSchemeAffineChart_source] at hq
  obtain ⟨z, rfl⟩ := hq
  rw [normalSchemePointChart_param]
  change normalSchemeAffineParam k z ∈
    a3b4_cycleSupport P.hom (s2e_componentCycle (s2c_subschemeι P I) ℚ) ↔ z = 0
  rw [s2e_componentCycle_analytic_support (s2c_subschemeι P I)]
  change (normalSchemeAffineParam k z).underlying ∈ Set.range I.subschemeι ↔ z = 0
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact (normal_coordinate_point_support k (normalProjectiveChart k z)).trans
    (normalProjectiveChart_eq_base_iff k z)

#print axioms normalSchemePointChart_support
end HodgeLean.Foundations.Program.G32Native.EulerModel
