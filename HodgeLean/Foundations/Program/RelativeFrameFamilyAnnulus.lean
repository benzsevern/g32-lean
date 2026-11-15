import HodgeLean.Foundations.Program.RelativeFrameFamilyAnnulusBounds
import HodgeLean.Foundations.Program.RelativeFrameFamilyNonzeroRoot

noncomputable section
open Set Metric Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Restricting a base root to the stationary region retains the prescribed annulus.
Source: `rf7_offset_avoids`, `rf7_stationary_power_analytic`. -/
theorem rf7_annulus_chart {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C)
    (u : OpenPartialHomeomorph C ℂ)
    (hus : u.source = rf7_component P.f (b i) (3 * b6t_radius b) x)
    (hut : u.target = {w : ℂ | ‖w ^ P.n x‖ < 3 * b6t_radius b})
    (hu : u ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C)
    (hpow : ∀ y ∈ u.source, P.f y = ((b i + u y ^ P.n x : ℂ) : OnePoint ℂ)) :
    ∃ a : OpenPartialHomeomorph C ℂ,
      a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C ∧
      a.source ⊆ rf7_component P.f (b i) (3 * b6t_radius b) x ∧
      (∀ y ∈ a.source, P.f y = ((b i + a y ^ P.n x : ℂ) : OnePoint ℂ)) ∧
      a.source ⊆ P.f ⁻¹' b6a_stationaryOpen b ∧
      closure (b63r_annulus (P.n x) (rf7_radius b)) ⊆ a.target ∧
      a.symm '' b63r_annulus (P.n x) (rf7_radius b) ⊆ rf7_outer b P.f ∧
      ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × C ↦ a q.2) (univ ×ˢ a.source) := by
  let S := P.f ⁻¹' b6a_stationaryOpen b
  have hS : IsOpen S := (b6a_stationaryOpen_isOpen b).preimage P.hf.continuous
  let a := u.restr S
  have has : a.source = u.source ∩ S := by simp [a, hS.interior_eq]
  have ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C :=
    restr_mem_maximalAtlas _ hu hS
  have hstat : a.source ⊆ S := by rw [has]; exact inter_subset_right
  have hpow' : ∀ y ∈ a.source, P.f y = ((b i + a y ^ P.n x : ℂ) : OnePoint ℂ) :=
    fun y hy ↦ hpow y ((has ▸ hy).1)
  have hr := (b6t_discs b P.hb).1
  have hρ : b6t_radius b < rf7_radius b := by unfold rf7_radius; linarith
  have hρhi : 2 * rf7_radius b < 3 * b6t_radius b := by unfold rf7_radius; linarith
  have hcl : closure (b63r_annulus (P.n x) (rf7_radius b)) ⊆
      rf4_closedAnnulus (P.n x) (rf7_radius b) :=
    closure_minimal (rf4_annulus_subset_closed _ _) (rf4_closedAnnulus_isCompact (P.hn x) _).isClosed
  have ht : closure (b63r_annulus (P.n x) (rf7_radius b)) ⊆ a.target := by
    intro z hz
    have hz' : rf7_radius b ≤ ‖z ^ P.n x‖ ∧ ‖z ^ P.n x‖ ≤ 2 * rf7_radius b := by
      simpa only [norm_pow] using (show rf7_radius b ≤ ‖z‖ ^ P.n x ∧ ‖z‖ ^ P.n x ≤ 2 * rf7_radius b from hcl hz)
    have hzu : z ∈ u.target := by rw [hut]; exact lt_of_le_of_lt hz'.2 hρhi
    have huS : u.symm z ∈ S := by
      change P.f (u.symm z) ∈ b6a_stationaryOpen b
      rw [hpow _ (u.map_target hzu), u.right_inv hzu]
      intro hh
      obtain ⟨j, w, hw, he⟩ := mem_iUnion.mp hh
      have hw' : w = b i + z ^ P.n x := OnePoint.coe_injective he
      subst w
      have hh := rf7_offset_avoids P.hb i (z ^ P.n x) (b6t_radius b)
        (by linarith) (lt_of_lt_of_le hρ hz'.1) (by linarith [hz'.2]) j
      exact (not_le_of_gt hh) hw
    have hsa : u.symm z ∈ a.source := by rw [has]; exact ⟨u.map_target hzu, huS⟩
    have h := a.map_source hsa
    simpa [a, u.right_inv hzu] using h
  have houter : a.symm '' b63r_annulus (P.n x) (rf7_radius b) ⊆ rf7_outer b P.f := by
    rintro y ⟨z, hz, rfl⟩ j ⟨w, hw, he⟩
    have hzT := ht (subset_closure hz)
    rw [hpow' _ (a.map_target hzT), a.right_inv hzT] at he
    have hw' : w = b i + z ^ P.n x := OnePoint.coe_injective he
    subst w
    have hzlo : rf7_radius b < ‖z ^ P.n x‖ := by simpa only [norm_pow] using hz.1
    have hzhi : ‖z ^ P.n x‖ < 2 * rf7_radius b := by simpa only [norm_pow] using hz.2
    have hh := rf7_offset_avoids P.hb i (z ^ P.n x) (rf7_radius b)
      (by linarith) hzlo (by linarith) j
    exact (not_le_of_gt hh) hw
  have hne : ∀ y ∈ a.source, a y ≠ 0 := by
    intro y hy hzero
    have hp := hpow' y hy
    rw [hzero, zero_pow (P.hn x).ne', add_zero] at hp
    apply hstat hy
    apply mem_iUnion.mpr
    exact ⟨i, b i, Metric.mem_closedBall_self hr.le, hp.symm⟩
  refine ⟨a, ha, ?_, hpow', hstat, ht, houter, ?_⟩
  · rw [has, ← hus]
    exact inter_subset_left
  · exact rf7_stationary_power_analytic P a.source a.open_source a a.continuousOn
      (P.n x) (P.hn x) (b i) hne hstat hpow'

end HodgeLean.Foundations.Program
