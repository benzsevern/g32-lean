import HodgeLean.Foundations.Program.SchoenSelectedGeometryLineCharts

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_sphere_finite_chart_holomorphic :
    letI : SmoothOfRelativeDimension 1
        (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
      s0_complex_projective_relative_dimension 1
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω
      (fun z : ℂ ↦ s0_sphere_projective_homeomorph (z : OnePoint ℂ)) := by
  letI : SmoothOfRelativeDimension 1
      (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension 1
  have hc : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω (fun z : ℂ ↦ fun _ : Fin 1 ↦ z) := by
    exact contMDiff_iff_contDiff.mpr (contDiff_pi.mpr (fun _ ↦ contDiff_id))
  have h := (s0_projective_line_affine_chart_holomorphic (1 : Fin 2)).comp hc
  convert h using 1
  funext z
  dsimp only [Function.comp_apply]
  rw [s0_projective_line_affine_chart_value]
  change vectorToComplexPoint (![z, 1] : CoordinateSpace 1) _ =
    vectorToComplexPoint (fun j : Fin 2 ↦ if j = 1 then 1 else z) _
  congr 1
  funext j
  fin_cases j <;> rfl

#print axioms s0_sphere_finite_chart_holomorphic

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_sphere_infinite_chart_holomorphic :
    letI : SmoothOfRelativeDimension 1
        (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
      s0_complex_projective_relative_dimension 1
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω
      (fun z : ℂ ↦ s0_sphere_projective_homeomorph (b4cov_sphInv (z : OnePoint ℂ))) := by
  letI : SmoothOfRelativeDimension 1
      (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension 1
  have hc : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω (fun z : ℂ ↦ fun _ : Fin 1 ↦ z) := by
    exact contMDiff_iff_contDiff.mpr (contDiff_pi.mpr (fun _ ↦ contDiff_id))
  have h := (s0_projective_line_affine_chart_holomorphic (0 : Fin 2)).comp hc
  convert h using 1
  funext z
  dsimp only [Function.comp_apply]
  rw [s0_projective_line_affine_chart_value]
  have he : (fun j : Fin 2 ↦ if j = 0 then 1 else z) = (![1, z] : CoordinateSpace 1) := by
    funext j
    fin_cases j <;> rfl
  simp only [he]
  by_cases hz : z = 0
  · subst z
    rw [b4cov_sphInv_zero]
    rfl
  · rw [b4cov_sphInv_coe hz]
    change vectorToComplexPoint (![z⁻¹, 1] : CoordinateSpace 1) _ =
      vectorToComplexPoint (![1, z] : CoordinateSpace 1) _
    have hs : z⁻¹ • (![1, z] : CoordinateSpace 1) = ![z⁻¹, 1] := by
      funext j
      fin_cases j <;> simp [hz]
    simpa only [hs] using vectorToComplexPoint_smul
      (![1, z] : CoordinateSpace 1) (by simp) z⁻¹ (inv_ne_zero hz)

#print axioms s0_sphere_infinite_chart_holomorphic

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_sphere_projective_holomorphic :
    letI : SmoothOfRelativeDimension 1
        (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
      s0_complex_projective_relative_dimension 1
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω s0_sphere_projective_homeomorph := by
  letI : SmoothOfRelativeDimension 1
      (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension 1
  intro p
  rw [contMDiffAt_iff]
  refine ⟨s0_sphere_projective_homeomorph.continuous.continuousAt, ?_⟩
  induction p using OnePoint.rec with
  | coe z =>
      have h := s0_sphere_finite_chart_holomorphic z
      rw [contMDiffAt_iff] at h
      simpa [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
        b4cov_chartAt_coe, b4cov_chart0_coe, b4cov_chart0_symm] using h.2
  | infty =>
      have h := s0_sphere_infinite_chart_holomorphic 0
      rw [contMDiffAt_iff] at h
      simpa [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
        b4cov_chartAt_infty, b4cov_chartInf_apply, b4cov_sphInv_infty,
        b4cov_chart0_coe, b4cov_chartInf_symm, b4cov_sphInv_zero] using h.2

#print axioms s0_sphere_projective_holomorphic

end HodgeLean.Foundations.Program
