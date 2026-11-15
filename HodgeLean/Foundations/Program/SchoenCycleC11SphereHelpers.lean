import HodgeLean.Foundations.Program.SchoenCycleC11ChartHelpers
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Metric Topology
namespace HodgeLean.Foundations.Program

/-- Unit-sphere vectors are nonzero.
Source: Mathlib, Metric.mem_sphere and norm_zero. -/
theorem s2e_c11_unitSphere_ne_zero
    {E : Type*} [NormedAddCommGroup E] (v : sphere (0 : E) 1) : (v : E) ≠ 0 := by
  intro h
  have hn := v.property
  rw [mem_sphere, dist_zero_right, h, norm_zero] at hn
  exact zero_ne_one hn

/-- Radial normalization converts a nonzero vector into a unit vector.
Source: Mathlib, norm_smul; Hatcher, Algebraic Topology, radial retraction. -/
def s2e_c11_radialNormalize
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) (hv : v ≠ 0) :
    sphere (0 : E) 1 :=
  ⟨‖v‖⁻¹ • v, by
    rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

/-- A real continuous linear equivalence induces a radial homeomorphism of unit spheres.
Source: Hatcher, Algebraic Topology, radial normalization between equivalent norms. -/
def s2e_c11_radialSphereHomeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 where
  toFun v := s2e_c11_radialNormalize (e v)
    (e.injective.ne (s2e_c11_unitSphere_ne_zero v) |>.trans_eq (map_zero e))
  invFun w := s2e_c11_radialNormalize (e.symm w)
    (e.symm.injective.ne (s2e_c11_unitSphere_ne_zero w) |>.trans_eq (map_zero e.symm))
  left_inv v := by
    apply Subtype.ext
    have hv : ‖(v : E)‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using v.property
    have he : e (v : E) ≠ 0 := by
      intro h
      exact s2e_c11_unitSphere_ne_zero v (e.injective (h.trans (map_zero e).symm))
    change ‖e.symm (‖e (v : E)‖⁻¹ • e (v : E))‖⁻¹ •
      e.symm (‖e (v : E)‖⁻¹ • e (v : E)) = v
    rw [map_smul, e.symm_apply_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hv, mul_one,
      inv_inv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr he), one_smul]
  right_inv w := by
    apply Subtype.ext
    have hw : ‖(w : F)‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using w.property
    have he : e.symm (w : F) ≠ 0 := by
      intro h
      exact s2e_c11_unitSphere_ne_zero w (e.symm.injective (h.trans (map_zero e.symm).symm))
    change ‖e (‖e.symm (w : F)‖⁻¹ • e.symm (w : F))‖⁻¹ •
      e (‖e.symm (w : F)‖⁻¹ • e.symm (w : F)) = w
    rw [map_smul, e.apply_symm_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hw, mul_one,
      inv_inv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr he), one_smul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc := e.continuous.comp (continuous_subtype_val : Continuous
      (Subtype.val : sphere (0 : E) 1 → E))
    apply (hc.norm.inv₀ ?_).smul hc
    intro v
    apply norm_ne_zero_iff.mpr
    intro h
    exact s2e_c11_unitSphere_ne_zero v (e.injective (h.trans (map_zero e).symm))
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hc := e.symm.continuous.comp (continuous_subtype_val : Continuous
      (Subtype.val : sphere (0 : F) 1 → F))
    apply (hc.norm.inv₀ ?_).smul hc
    intro w
    apply norm_ne_zero_iff.mpr
    intro h
    exact s2e_c11_unitSphere_ne_zero w (e.symm.injective (h.trans (map_zero e.symm).symm))

/-- The actual coordinate norm sphere is radially homeomorphic to the complex Euclidean sphere.
Source: Mathlib, EuclideanSpace.equiv and radial normalization between equivalent norms. -/
def s2e_c11_coordinateSphereEuclideanHomeomorph (k : ℕ) :
    sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1 :=
  s2e_c11_radialSphereHomeomorph
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (k + 1) => ℂ)).symm

/-- Simply connected spaces transmit simple connectivity along surjections with based loop lifts.
Source: Mathlib, simply_connected_iff_loops_nullhomotopic and homotopy of mapped paths. -/
theorem s2e_c11_simplyConnected_of_basedLoop_lifts
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SimplyConnectedSpace X]
    (f : C(X, Y)) (hs : Function.Surjective f)
    (hlift : ∀ x (γ : Path (f x) (f x)), ∃ δ : Path x x, (δ.map f.continuous).Homotopic γ) :
    SimplyConnectedSpace Y := by
  letI : PathConnectedSpace Y := hs.pathConnectedSpace f.continuous
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro y γ
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨δ, hδ⟩ := hlift x γ
  have h := (SimplyConnectedSpace.paths_homotopic δ (Path.refl x)).map f
  exact hδ.symm.trans h

/-- The actual coordinate space has the expected real dimension.
Source: Mathlib, Module.finrank_pi_fintype and Complex.finrank_real_complex. -/
theorem s2e_c11_coordinateSpace_real_finrank (k : ℕ) :
    Module.finrank ℝ (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) =
      (k + 1) * 2 := by
  simp only [AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace,
    Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Every actual coordinate unit sphere is path connected, including the circle case.
Source: Mathlib, isPathConnected_sphere for real dimension greater than one. -/
theorem s2e_c11_coordinateSphere_pathConnected (k : ℕ) :
    PathConnectedSpace
      (sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1) := by
  have hd : 1 < Module.finrank ℝ (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) := by
    rw [s2e_c11_coordinateSpace_real_finrank]
    omega
  have hr : 1 < Module.rank ℝ (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hd
  exact isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hr _ zero_le_one)

/-- A normalized projective chart has an explicit unit-sphere representative section.
Source: Hartshorne, Algebraic Geometry, I.2, normalized coordinates; Hatcher, Hopf bundle. -/
def s2e_c11_projectiveChartSphereSection (k : ℕ) (i : Fin (k + 1)) :
    {p : Projectivization ℂ (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) //
      s2e_c11_normalizedCoordinates i p i ≠ 0} →
        sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1 :=
  fun p => s2e_c11_radialNormalize
    (s2e_c11_chartVector i (s2e_c11_normalizedChartHomeomorph i p))
    (s2e_c11_chartVector_ne_zero i _)

/-- The unit-sphere representative section is continuous in each actual projective chart.
Source: Mathlib, continuity of radial normalization away from zero. -/
theorem s2e_c11_projectiveChartSphereSection_continuous (k : ℕ) (i : Fin (k + 1)) :
    Continuous (s2e_c11_projectiveChartSphereSection k i) := by
  have hc := (s2e_c11_chartVector_continuous i).comp
    (s2e_c11_normalizedChartHomeomorph i).continuous
  apply Continuous.subtype_mk
  exact (hc.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (s2e_c11_chartVector_ne_zero i _))).smul hc

/-- Projecting the unit-sphere section recovers the specified projective point.
Source: Mathlib, Projectivization.mk_eq_mk_iff' and normalized chart inverse identities. -/
theorem s2e_c11_projectiveChartSphereSection_projection (k : ℕ) (i : Fin (k + 1))
    (p : {p : Projectivization ℂ (AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) //
      s2e_c11_normalizedCoordinates i p i ≠ 0}) :
    AlgebraicGeometry.ComplexProjectiveSpace.sphereToProjectivization
      (s2e_c11_projectiveChartSphereSection k i p) = p.1 := by
  let v := s2e_c11_chartVector i (s2e_c11_normalizedChartHomeomorph i p)
  have hv : v ≠ 0 := s2e_c11_chartVector_ne_zero i _
  have hraw : Projectivization.mk ℂ v hv = p.1 :=
    congrArg Subtype.val ((s2e_c11_normalizedChartHomeomorph i).symm_apply_apply p)
  change Projectivization.mk ℂ (‖v‖⁻¹ • v) _ = p.1
  trans Projectivization.mk ℂ v hv
  · apply (Projectivization.mk_eq_mk_iff' ℂ _ v _ hv).mpr
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ), ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  · exact hraw

/-- The actual coordinate sphere identifies with the real Euclidean sphere of the correct ambient dimension.
Source: Mathlib, LinearEquiv.ofFinrankEq and radial transport between equivalent norms. -/
def s2e_c11_coordinateSphereRealEuclideanHomeomorph (k : ℕ) :
    sphere (0 : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin ((k + 1) * 2))) 1 := by
  let e : AlgebraicGeometry.ComplexProjectiveSpace.CoordinateSpace k ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin ((k + 1) * 2)) :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [s2e_c11_coordinateSpace_real_finrank]
      simp only [finrank_euclideanSpace, Fintype.card_fin])
  exact s2e_c11_radialSphereHomeomorph e.toContinuousLinearEquiv

end HodgeLean.Foundations.Program
