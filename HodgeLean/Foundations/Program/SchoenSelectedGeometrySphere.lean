import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveCoordinates
import HodgeLean.Foundations.Program.HurwitzPrymCovSphere

noncomputable section
set_option maxHeartbeats 400000
open Filter Set Topology CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program

theorem s0_sphere_projectivization_continuous :
    Continuous (OnePoint.equivProjectivization ℂ) := by
  classical
  let v0 : ℂ → {v : CoordinateSpace 1 // v ≠ 0} := fun z ↦ ⟨![z, 1], by simp⟩
  let vInf : ℂ → {v : CoordinateSpace 1 // v ≠ 0} := fun z ↦ ⟨![1, z], by simp⟩
  have hv0 : Continuous v0 := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hvInf : Continuous vInf := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hc0 : Continuous (fun z : ℂ ↦ OnePoint.equivProjectivization ℂ (z : OnePoint ℂ)) :=
    continuous_quot_mk.comp hv0
  have hcInf : Continuous (fun z : ℂ ↦ Projectivization.mk ℂ (![1, z] : CoordinateSpace 1)
      (by simp)) := continuous_quot_mk.comp hvInf
  rw [OnePoint.continuous_iff]
  refine ⟨?_, hc0⟩
  have ht : Tendsto (fun z : ℂ ↦ z⁻¹) (coclosedCompact ℂ) (𝓝 0) := by
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  have hh := hcInf.continuousAt.tendsto.comp ht
  apply hh.congr'
  have hn : {z : ℂ | z ≠ 0} ∈ coclosedCompact ℂ := by
    rw [coclosedCompact_eq_cocompact]
    exact isCompact_singleton.compl_mem_cocompact
  filter_upwards [hn] with z hz
  change Projectivization.mk ℂ (![1, z⁻¹] : CoordinateSpace 1) _ =
    Projectivization.mk ℂ (![z, 1] : CoordinateSpace 1) _
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨z⁻¹, ?_⟩
  funext i
  fin_cases i <;> simp [hz]

#print axioms s0_sphere_projectivization_continuous

/-- The sphere identified with the complex points of the scheme-theoretic projective line.
Source: Hartshorne, Algebraic Geometry, II.2.5, the two standard projective-line charts. -/
def s0_sphere_projective_homeomorph :
    OnePoint ℂ ≃ₜ AlgebraicGeometry.ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))) :=
  let e := (OnePoint.equivProjectivization ℂ).trans
    (s0_projective_coordinate_homeomorph 1).toEquiv
  (show Continuous e from (s0_projective_coordinate_homeomorph 1).continuous.comp
    s0_sphere_projectivization_continuous).homeoOfEquivCompactToT2

example (z : ℂ) : s0_sphere_projective_homeomorph (z : OnePoint ℂ) =
    vectorToComplexPoint (![z, 1] : CoordinateSpace 1) (by simp) := rfl

example : s0_sphere_projective_homeomorph OnePoint.infty =
    vectorToComplexPoint (![1, 0] : CoordinateSpace 1) (by simp) := rfl

#print axioms s0_sphere_projective_homeomorph

end HodgeLean.Foundations.Program
