import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cOrientation
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section

namespace HodgeLean.Foundations.Program

open scoped Topology

theorem b6m_plane_regular_open_dense (b : Fin 10 → ℂ) :
    IsOpen {z : ℂ | ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b} ∧
      Dense {z : ℂ | ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b} := by
  let U : Fin 10 → Set ℂ := fun i ↦ {b i}ᶜ ∩ (Metric.sphere (b i) (b6t_radius b))ᶜ
  have ho : ∀ i, IsOpen (U i) := fun i ↦
    isOpen_compl_singleton.inter Metric.isClosed_sphere.isOpen_compl
  have hd : ∀ i, Dense (U i) := fun i ↦
    (dense_compl_singleton (b i)).inter_of_isOpen_left
      (interior_eq_empty_iff_dense_compl.mp (interior_sphere' _ _))
      isOpen_compl_singleton
  have he : {z : ℂ | ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b} = ⋂ i, U i := by
    ext z
    simp [U, dist_eq_norm]
  rw [he]
  exact ⟨isOpen_iInter_of_finite ho, dense_iInter_of_isOpen ho hd⟩

theorem b6m_plane_eq_single (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (i : Fin 10) (z : ℂ) (hz : z ∈ Metric.closedBall (b i) (b6t_radius b)) :
    b6t_plane b t z = z + (max 0 (1 - dist z (b i) / b6t_radius b)) • (t i - b i) := by
  have hr := (b6t_discs b hb).1
  unfold b6t_plane
  congr 1
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hj : b6t_radius b < dist z (b j) := by
      apply lt_of_not_ge
      intro hj
      exact Set.disjoint_left.mp ((b6t_discs b hb).2.2 hji) hj hz
    rw [max_eq_left (sub_nonpos.mpr ((one_le_div hr).mpr hj.le)), zero_smul]
  · simp

theorem b6m_plane_eventually_id (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (z : ℂ) (hz : ∀ i, b6t_radius b < dist z (b i)) :
    b6t_plane b t =ᶠ[𝓝 z] id := by
  have hr := (b6t_discs b hb).1
  have he : ∀ᶠ x in 𝓝 z, ∀ i, b6t_radius b < dist x (b i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds (hz i)
  filter_upwards [he] with x hx
  change x + ∑ i : Fin 10, (max 0 (1 - dist x (b i) / b6t_radius b)) • (t i - b i) = x
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro i _
  rw [max_eq_left (sub_nonpos.mpr ((one_le_div hr).mpr (hx i).le)), zero_smul]

theorem b6m_plane_regular_orientation (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (ht : t ∈ b6t_polydisc b) (z : ℂ)
    (hz : ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b) :
    DifferentiableAt ℝ (b6t_plane b t) z ∧ ∀ v w : ℂ,
      SignType.sign (b3_orient ℂ (fderiv ℝ (b6t_plane b t) z v)
        (fderiv ℝ (b6t_plane b t) z w)) = SignType.sign (b3_orient ℂ v w) := by
  have hr := (b6t_discs b hb).1
  by_cases hi : ∃ i, dist z (b i) < b6t_radius b
  · obtain ⟨i, hi⟩ := hi
    have he : b6t_plane b t =ᶠ[𝓝 z]
        (fun x : ℂ ↦ x + (max 0 (1 - dist x (b i) / b6t_radius b)) • (t i - b i)) := by
      have hn : Metric.ball (b i) (b6t_radius b) ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hi
      filter_upwards [hn] with x hx
      exact b6m_plane_eq_single b t hb i x (Metric.ball_subset_closedBall hx)
    have hd := b6m_radial_tent_differentiable (b i) z (b6t_radius b) hr (hz i).1 (hz i).2
    refine ⟨(differentiableAt_id.add (hd.smul_const (t i - b i))).congr_of_eventuallyEq he, ?_⟩
    intro v w
    rw [he.fderiv_eq]
    exact b6m_radial_shift_orientation (b i) z (t i - b i) (b6t_radius b) hr
      (hz i).1 (hz i).2 (by simpa only [Metric.mem_ball, dist_eq_norm] using ht i) v w
  · have hout : ∀ i, b6t_radius b < dist z (b i) := by
      intro i
      exact (lt_or_gt_of_ne (hz i).2).resolve_left (fun h ↦ hi ⟨i, h⟩)
    have he := b6m_plane_eventually_id b t hb z hout
    refine ⟨differentiableAt_id.congr_of_eventuallyEq he, fun v w ↦ ?_⟩
    rw [he.fderiv_eq, fderiv_id]
    rfl

theorem b6m_plane_regular_derivative_injective (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (ht : t ∈ b6t_polydisc b) (z : ℂ)
    (hz : ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b) :
    Function.Injective (fderiv ℝ (b6t_plane b t) z) := by
  change Function.Injective (fderiv ℝ (b6t_plane b t) z).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  change v = 0
  by_contra hv0
  have hs := (b6m_plane_regular_orientation b t hb ht z hz).2 v (Complex.I • v)
  have hv' : fderiv ℝ (b6t_plane b t) z v = 0 := hv
  rw [hv'] at hs
  have hzero : b3_orient ℂ 0 (fderiv ℝ (b6t_plane b t) z (Complex.I • v)) = 0 := by
    simp [b3_orient]
  rw [hzero, sign_zero, sign_pos (b3A_orient_I v hv0)] at hs
  exact zero_ne_one hs

end HodgeLean.Foundations.Program
