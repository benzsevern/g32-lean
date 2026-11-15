import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRealSurface

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold
open scoped Manifold ContDiff

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_sphere_regular_open_dense (b : Fin 10 → ℂ) :
    IsOpen {x : OnePoint ℂ | ∃ z : ℂ, (z : OnePoint ℂ) = x ∧
      ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b} ∧
    Dense {x : OnePoint ℂ | ∃ z : ℂ, (z : OnePoint ℂ) = x ∧
      ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b} := by
  have he : {x : OnePoint ℂ | ∃ z : ℂ, (z : OnePoint ℂ) = x ∧
      ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b} =
      ((↑) : ℂ → OnePoint ℂ) ''
        {z : ℂ | ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    exact exists_congr fun z ↦ and_comm
  rw [he]
  exact ⟨OnePoint.isOpenMap_coe _ (b6m_plane_regular_open_dense b).1,
    OnePoint.denseRange_coe.dense_image OnePoint.continuous_coe
      (b6m_plane_regular_open_dense b).2⟩

theorem b6m_sphere_mfderiv_plane (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (ht : t ∈ b6t_polydisc b) (z : ℂ) (hd : DifferentiableAt ℝ (b6t_plane b t) z) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b6t_sphere b t) (z : OnePoint ℂ) ∧
      ∀ v : ℂ, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b6t_sphere b t) (z : OnePoint ℂ) v =
        fderiv ℝ (b6t_plane b t) z v := by
  obtain ⟨e, he⟩ := b6t_homeomorph b hb t ht
  have hc : Continuous (b6t_sphere b t) := e.continuous.congr he
  have hw : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (z : OnePoint ℂ)
      (b6t_sphere b t) = b6t_plane b t := by
    funext w
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe,
      extChartAt_coe_symm, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      b6t_sphere, OnePoint.map_some, b4cov_chartAt_coe, b4cov_chart0_symm,
      b4cov_chart0_coe, id_eq]
  have hD : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b6t_sphere b t) (z : OnePoint ℂ) := by
    rw [mdifferentiableAt_iff]
    refine ⟨hc.continuousAt, ?_⟩
    rw [hw]
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ, Function.comp_apply, b4cov_chartAt_coe,
      b4cov_chart0_coe, id_eq] using hd
  refine ⟨hD, fun v ↦ ?_⟩
  rw [hD.mfderiv, hw]
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ,
    Function.comp_apply, b4cov_chartAt_coe, b4cov_chart0_coe, id_eq]
  rfl

theorem b6m_sphere_regular_orientation (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (ht : t ∈ b6t_polydisc b) (z : ℂ)
    (hz : ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b6t_sphere b t) (z : OnePoint ℂ) ∧
      ∀ v w : ℂ, SignType.sign (b3_orient ℂ
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b6t_sphere b t) (z : OnePoint ℂ) v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b6t_sphere b t) (z : OnePoint ℂ) w)) =
        SignType.sign (b3_orient ℂ v w) := by
  obtain ⟨hd, ho⟩ := b6m_plane_regular_orientation b t hb ht z hz
  obtain ⟨hs, hder⟩ := b6m_sphere_mfderiv_plane b t hb ht z hd
  refine ⟨hs, fun v w ↦ ?_⟩
  rw [hder v, hder w]
  exact ho v w

set_option backward.isDefEq.respectTransparency false in
theorem b6m_filling_comparison_regular {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart) (ht : t ∈ b6t_polydisc b)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (e : C ≃ₜ D) (he : ∀ y, k (e y) = b6t_sphere b t (f y))
    (x : C) (z : ℂ) (hx : f x = (z : OnePoint ℂ))
    (hz : ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b)
    (hfd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ≠ 0)
    (hkd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e x) ≠ 0) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x ∧ ∀ v w : ℂ,
      SignType.sign (b3_orient ℂ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x w)) = SignType.sign (b3_orient ℂ v w) := by
  obtain ⟨hd, ho⟩ := b6m_sphere_regular_orientation b t hb ht z hz
  apply b6m_surface_comparison_orientation e e.continuous f k (b6t_sphere b t)
    hf hk he x hfd hkd
  · simpa only [hx] using hd
  · exact hx.symm ▸ ho

end HodgeLean.Foundations.Program
