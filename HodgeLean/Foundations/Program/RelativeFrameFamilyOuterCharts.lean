import HodgeLean.Foundations.Program.RelativeFrameFamilyOuterStationary
import HodgeLean.Foundations.Program.RelativeFrameFamilyPowerChart
import HodgeLean.Foundations.Program.RelativeFrameFamilyNonzeroRoot

noncomputable section
open Set Metric Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold


/-- Stationary power charts cover the outer boundary and are analytic on the total family.
Source: `b6a_sliceChart`, `rf7_power_chart_analytic`, `rf7_total_root_analytic`. -/
theorem rf7_outer_chart_at {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (p : closure (rf7_outer b P.f)) :
    ∃ u : OpenPartialHomeomorph C ℂ,
      p.val ∈ u.source ∧ u ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C ∧
      u.source ⊆ P.f ⁻¹' b6a_stationaryOpen b ∧
      ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × C ↦ u q.2) (univ ×ˢ u.source) := by
  classical
  let t : b6t_polydisc b := ⟨b, (b6t_polydisc_neighbourhood b P.hb).1⟩
  let s := b6a_sliceChart b C P.A P.hparam t p.val
  have hps : p.val ∈ s.source := (P.hA (t, p.val)).1
  have hpstat := rf7_outer_closure_stationary P.hb P.f P.hf.continuous p.property
  obtain ⟨j, n, hn, hj, hpower⟩ : ∃ (j : Fin 13) (n : ℕ), 0 < n ∧ ¬j.val < 10 ∧
      ∀ y ∈ s.source, P.f y = b6a_value b j (s y ^ n) := by
    by_cases hm : P.f p.val ∈ range (b6_branch b)
    · obtain ⟨j, hj⟩ := hm
      have hjfix : ¬ j.val < 10 := by
        intro hlt
        let i : Fin 10 := ⟨j.val, hlt⟩
        have hjval : b6_branch b j = ((b i : ℂ) : OnePoint ℂ) := by
          rw [← b6a_value_zero]
          simp [b6a_value, hlt, i]
        apply hpstat
        apply mem_iUnion.mpr
        refine ⟨i, b i, Metric.mem_closedBall_self (b6t_discs b P.hb).1.le, ?_⟩
        exact hjval.symm.trans hj
      refine ⟨j, P.n p.val, P.hn p.val, hjfix, fun y hy ↦ ?_⟩
      have h := (P.hmark (t, p.val) j hj.symm).2 (t, y) hy
      change b6t_sphere b b (P.f y) = b6a_value b j (s y ^ P.n p.val) at h
      rwa [b6t_identity] at h
    · refine ⟨10, 1, by decide, by decide, fun y hy ↦ ?_⟩
      have h := (P.hfree (t, p.val) hm).2 (t, y) hy
      change b6t_sphere b b (P.f y) = ((s y : ℂ) : OnePoint ℂ) at h
      rw [b6t_identity] at h
      simpa [b6a_value] using h
  have hnc : ∃ x y, P.f x ≠ P.f y := by
    obtain ⟨x, hx⟩ := P.hsurj ((0 : ℂ) : OnePoint ℂ)
    obtain ⟨y, hy⟩ := P.hsurj OnePoint.infty
    exact ⟨x, y, by rw [hx, hy]; exact OnePoint.coe_ne_infty 0⟩
  have hs := rf7_power_chart_analytic P.f P.hf hnc b j n hn s hpower
  let S := P.f ⁻¹' b6a_stationaryOpen b
  have hS : IsOpen S := (b6a_stationaryOpen_isOpen b).preimage P.hf.continuous
  let u := s.restr S
  have hus : u.source = s.source ∩ S := by simp [u, hS.interior_eq]
  have hu : u ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C :=
    restr_mem_maximalAtlas _ hs hS
  have hstat : u.source ⊆ S := by rw [hus]; exact inter_subset_right
  refine ⟨u, by rw [hus]; exact ⟨hps, hpstat⟩, hu, hstat, ?_⟩
  have hw : ContinuousOn (fun q : b6t_polydisc b × C ↦ u q.2) (univ ×ˢ u.source) :=
    u.continuousOn.comp continuous_snd.continuousOn (fun _ h ↦ h.2)
  exact rf7_total_root_analytic P u.source u.open_source _ hw j n hn (fun q hq ↦ by
    change b6t_sphere b q.1.val (P.f q.2) = _
    rw [(b6t_fixed b P.hb q.1.val q.1.property).2.2.2 _ (hstat hq.2)]
    rw [hpower q.2 ((hus ▸ hq.2).1)]
    simp [u, b6a_value, hj])

end HodgeLean.Foundations.Program
