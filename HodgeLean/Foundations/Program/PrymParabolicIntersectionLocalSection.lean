import HodgeLean.Foundations.Program.PrymParabolicIntersectionApprox
import HodgeLean.Foundations.Program.PrymParabolicIntersectionLocalLift

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter Manifold Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Points at height at least `1/2` avoid the branch discs, so the radial push fixes them. -/
theorem hga_offAxis_fixed (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (z : ℂ)
    (hz : 1 / 2 ≤ |z.im|) : b6t_sphere mr_base t (z : OnePoint ℂ) = (z : OnePoint ℂ) := by
  apply (b6t_fixed mr_base mr_base_mem_chart t ht).2.2.2
  simp only [Set.mem_iUnion, not_exists]
  intro k
  rintro ⟨w, hw, he⟩
  have he' : w = z := OnePoint.coe_injective he
  subst w
  have hn : ‖z - mr_base k‖ < 1 / 8 :=
    lt_of_le_of_lt (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw) mr_radius_lt8
  have hi : |(z - mr_base k).im| ≤ ‖z - mr_base k‖ := Complex.abs_im_le_norm _
  have h0 : (mr_base k).im = 0 := by simp [mr_base]
  rw [Complex.sub_im, h0, sub_zero] at hi
  linarith

/-- Points off the real axis are not branch points. -/
theorem hga_offAxis_not_branch (z : ℂ) (hz : z.im ≠ 0) :
    (z : OnePoint ℂ) ∉ Set.range (b6_branch mr_base) := by
  rw [hg5_coe_mark_iff]
  exact fun h ↦ hz h.1

/-- The radial retraction of `ℂ` onto the closed disc of radius `r` about `P`.
Source: elementary plane geometry. -/
def hga_discRetract (P : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  P + ((r / max r ‖z - P‖ : ℝ) : ℂ) * (z - P)

theorem hga_discRetract_continuous (P : ℂ) {r : ℝ} (hr : 0 < r) :
    Continuous (hga_discRetract P r) := by
  unfold hga_discRetract
  have hm : ∀ z : ℂ, max r ‖z - P‖ ≠ 0 := fun z ↦ (lt_max_of_lt_left hr).ne'
  have : Continuous (fun z : ℂ ↦ r / max r ‖z - P‖) :=
    continuous_const.div (continuous_const.max (continuous_norm.comp
      (continuous_id.sub continuous_const))) hm
  fun_prop

theorem hga_discRetract_of_mem (P : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z - P‖ ≤ r) :
    hga_discRetract P r z = z := by
  unfold hga_discRetract
  rw [max_eq_left hz, div_self hr.ne']
  push_cast
  ring

theorem hga_discRetract_mem (P : ℂ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    hga_discRetract P r z ∈ closedBall P r := by
  rw [mem_closedBall, dist_eq_norm]
  unfold hga_discRetract
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr.le (le_max_of_le_left hr.le))]
  have hm : 0 < max r ‖z - P‖ := lt_max_of_lt_left hr
  rw [div_mul_eq_mul_div, div_le_iff₀ hm]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hr.le

/-- **A local section of the projection.** Over a disc about a point `P` at height at least
`1/2`, the covering gives a continuous section of the projection of a parameter fibre through any
point over `P`; its image of a smaller disc is open. -/
theorem hga_exists_local_section {G : Type} [Group G] (U : Type) [TopologicalSpace U]
    [MulAction G U] (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
    (C : Type) [TopologicalSpace C] (f : C → OnePoint ℂ)
    (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
    (hfι : ∀ u, f (ι u) = π u)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    (x : b63l_parameterFibre mr_base C V hV t) (P : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ x) = (P : OnePoint ℂ))
    (hfar : ∀ z ∈ closedBall P ρ, 1 / 2 ≤ |z.im|) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∃ e : C(ℂ, b63l_parameterFibre mr_base C V hV t), e P = x ∧
      (∀ z ∈ ball P r, b63d_projection mr_base C f V hV t (e z) = (z : OnePoint ℂ)) ∧
      IsOpen (e '' ball P r) := by
  classical
  let H := b6m_coordinate mr_base C ⟨t.val, hV t.property⟩
  have hnb : ∀ z ∈ closedBall P ρ, (z : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    intro z hz
    apply hga_offAxis_not_branch
    intro h0
    have := hfar z hz
    rw [h0, abs_zero] at this
    norm_num at this
  have hxr : H x ∈ Set.range ι := by
    rw [hιr]
    show f (H x) ∈ (Set.range (b6_branch mr_base))ᶜ
    rw [hx]
    exact hnb P (mem_closedBall_self hρ.le)
  obtain ⟨u, hu⟩ := hxr
  obtain ⟨φ, huφ, hφ⟩ := hπ.isCoveringMap.isLocalHomeomorph u
  have hπu : ((π u : OnePoint ℂ)) = (P : OnePoint ℂ) := by rw [← hfι, hu, hx]
  have hpo : IsOpen (b6t_punctured mr_base) :=
    (Set.finite_range (b6_branch mr_base)).isClosed.isOpen_compl
  have hO : IsOpen ((↑) ⁻¹' (Subtype.val '' φ.target) : Set ℂ) :=
    (hpo.isOpenMap_subtype_val _ φ.open_target).preimage OnePoint.continuous_coe
  have hPO : P ∈ ((↑) ⁻¹' (Subtype.val '' φ.target) : Set ℂ) := by
    refine ⟨φ u, φ.map_source huφ, ?_⟩
    rw [← hφ]
    exact hπu
  obtain ⟨r'', hr'', hball⟩ := Metric.isOpen_iff.mp hO P hPO
  set r : ℝ := min (r'' / 2) (ρ / 2) with hr_def
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrρ : r ≤ ρ := (min_le_right _ _).trans (by linarith)
  have hrr : r < r'' := (min_le_left _ _).trans_lt (by linarith)
  let ret := hga_discRetract P r
  have hret_mem : ∀ z, ret z ∈ closedBall P ρ := fun z ↦
    closedBall_subset_closedBall hrρ (hga_discRetract_mem P hr z)
  let w : ℂ → b6t_punctured mr_base := fun z ↦ ⟨(ret z : OnePoint ℂ), hnb _ (hret_mem z)⟩
  have hw : Continuous w :=
    (OnePoint.continuous_coe.comp (hga_discRetract_continuous P hr)).subtype_mk _
  have hwt : ∀ z, w z ∈ φ.target := by
    intro z
    have h1 : ret z ∈ ball P r'' :=
      mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp (hga_discRetract_mem P hr z)) hrr)
    obtain ⟨y, hy, hyv⟩ := hball h1
    have : y = w z := Subtype.ext hyv
    rw [← this]
    exact hy
  let e : C(ℂ, b63l_parameterFibre mr_base C V hV t) :=
    ⟨fun z ↦ H.symm (ι (φ.symm (w z))), H.symm.continuous.comp (hι.continuous.comp
      (φ.continuousOn_symm.comp_continuous hw hwt))⟩
  have hwP : w P = π u := Subtype.ext (by
    change ((hga_discRetract P r P : ℂ) : OnePoint ℂ) = _
    rw [hπu, hga_discRetract_of_mem P hr (by simp [hr.le])])
  have hwz : ∀ z ∈ ball P r, ((w z : b6t_punctured mr_base) : OnePoint ℂ) = (z : OnePoint ℂ) := by
    intro z hz
    change ((hga_discRetract P r z : ℂ) : OnePoint ℂ) = _
    rw [hga_discRetract_of_mem P hr (by rw [← dist_eq_norm]; exact (mem_ball.mp hz).le)]
  refine ⟨r, hr, hrρ, e, ?_, ?_, ?_⟩
  · change H.symm (ι (φ.symm (w P))) = x
    rw [hwP, hφ, φ.left_inv huφ, hu]
    exact H.symm_apply_apply x
  · intro z hz
    change b6t_sphere mr_base t.val (f (ι (φ.symm (w z)))) = _
    rw [hfι, hφ, φ.right_inv (hwt z), hwz z hz]
    exact hga_offAxis_fixed _ (hV t.property) z
      (hfar z (closedBall_subset_closedBall hrρ (ball_subset_closedBall hz)))
  · have hset : e '' ball P r = H.symm '' (ι '' (φ.symm '' (w '' ball P r))) := by
      rw [Set.image_image, Set.image_image, Set.image_image]
      rfl
    have hwo : IsOpen (w '' ball P r) := by
      have : w '' ball P r = Subtype.val ⁻¹' (((↑) : ℂ → OnePoint ℂ) '' ball P r) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z, hz, (hwz z hz).symm⟩
        · rintro ⟨z, hz, hzy⟩
          exact ⟨z, hz, Subtype.ext ((hwz z hz).trans hzy)⟩
      rw [this]
      exact (OnePoint.isOpenMap_coe _ isOpen_ball).preimage continuous_subtype_val
    rw [hset]
    apply H.symm.isOpenMap
    apply hι.isOpenMap
    exact φ.isOpen_image_symm_of_subset_target hwo (by rintro _ ⟨z, -, rfl⟩; exact hwt z)

/-- A continuous section of a holomorphic map over a disc is holomorphic on the disc. -/
theorem hga_section_contMDiffAt {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ, ℂ) ω T] [CompactSpace T] [ConnectedSpace T]
    (k : T → OnePoint ℂ) (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (e : C(ℂ, T)) (P : ℂ) (r : ℝ)
    (hr : 0 < r) (he : ∀ z ∈ ball P r, k (e z) = (z : OnePoint ℂ)) :
    ∀ z ∈ ball P r, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e z := by
  intro z hz
  let U : TopologicalSpace.Opens ℂ := ⟨ball P r, isOpen_ball⟩
  let eU : C(U, T) := e.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hP : P ∈ U := mem_ball_self hr
  have hQ : P + (r / 2 : ℝ) ∈ U := by
    change P + ((r / 2 : ℝ) : ℂ) ∈ ball P r
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have hne : (⟨P, hP⟩ : U) ≠ ⟨P + (r / 2 : ℝ), hQ⟩ := by
    intro h
    have h' := congrArg Subtype.val h
    simp only at h'
    have : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination -h'
    have : r / 2 = 0 := by exact_mod_cast this
    linarith
  have hh : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω eU :=
    hga_holomorphic_plane_lift U eU k hk 0 (fun z ↦ by
      rw [add_zero]; exact he z.1 z.2) _ _ hne
  exact contMDiffAt_subtype_iff.mp (hh ⟨z, hz⟩)

/-- **Agreement with a section.** A path over the disc that meets the section once lies on the
section. -/
theorem hga_section_agree {T X : Type} [TopologicalSpace T] [T2Space T] [TopologicalSpace X]
    [PreconnectedSpace X] (k : T → OnePoint ℂ) (e : C(ℂ, T)) (P : ℂ) (r : ℝ)
    (he : ∀ z ∈ ball P r, k (e z) = (z : OnePoint ℂ)) (ho : IsOpen (e '' ball P r))
    (γ : C(X, T)) (c : X → ℂ) (hc : Continuous c) (hcb : ∀ a, c a ∈ ball P r)
    (hkc : ∀ a, k (γ a) = (c a : OnePoint ℂ)) (a₀ : X) (h₀ : γ a₀ = e (c a₀)) :
    ∀ a, γ a = e (c a) := by
  let S : Set X := {a | γ a = e (c a)}
  have hcl : IsClosed S := isClosed_eq γ.continuous (e.continuous.comp hc)
  have hop : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro a ha
    have hmem : γ a ∈ e '' ball P r := ⟨c a, hcb a, ha.symm⟩
    filter_upwards [γ.continuous.continuousAt.preimage_mem_nhds (ho.mem_nhds hmem)] with a' ha'
    obtain ⟨z', hz', hze⟩ := ha'
    have hk' := hkc a'
    rw [← hze, he z' hz'] at hk'
    have : z' = c a' := OnePoint.coe_injective hk'
    change γ a' = e (c a')
    rw [← this, hze]
  have hS : S = univ := (IsClopen.eq_univ ⟨hcl, hop⟩ ⟨a₀, h₀⟩)
  intro a
  have : a ∈ S := hS ▸ mem_univ a
  exact this

#print axioms hga_section_agree
#print axioms hga_section_contMDiffAt
#print axioms hga_exists_local_section
#print axioms hga_discRetract_mem
#print axioms hga_discRetract_of_mem
#print axioms hga_discRetract_continuous
#print axioms hga_discRetract
#print axioms hga_offAxis_not_branch
#print axioms hga_offAxis_fixed
end HodgeLean.Foundations.Program
