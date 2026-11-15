import HodgeLean.Foundations.Program.RelativeFrameFamilyBase

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem rf7_total_root_analytic {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (S : Set C) (hS : IsOpen S)
    (w : b6t_polydisc b × C → ℂ)
    (hw : ContinuousOn w (univ ×ˢ S)) (j : Fin 13) (e : ℕ) (he : 0 < e)
    (hroot : ∀ q ∈ univ ×ˢ S, b6a_map b P.f q = b6a_value q.1.val j (w q ^ e)) :
    ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω w (univ ×ˢ S) := by
  letI := P.total_isManifold
  have hD : IsOpen (univ ×ˢ S : Set (b6t_polydisc b × C)) := isOpen_univ.prod hS
  intro q hq
  let A := P.A q
  have hqA : q ∈ A.source := (P.hA q).1
  have hA : A ∈ IsManifold.maximalAtlas 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C) :=
    StructureGroupoid.subset_maximalAtlas _ (P.hA q).2
  let R : ((Fin 10 → ℂ) × ℂ) → ℂ := fun z ↦ w (A.symm z)
  let Ω := A.target ∩ A.symm ⁻¹' (univ ×ˢ S)
  have hΩ : IsOpen Ω := A.symm.isOpen_inter_preimage hD
  have hqΩ : A q ∈ Ω := ⟨A.map_source hqA, by rw [Set.mem_preimage, A.left_inv hqA]; exact hq⟩
  have hr : ∀ᶠ z in 𝓝 (A q), ContinuousAt R z := by
    filter_upwards [hΩ.mem_nhds hqΩ] with z hz
    exact (hw.continuousAt (hD.mem_nhds hz.2)).comp (A.symm.continuousAt hz.1)
  obtain ⟨l, m, hm, hmodel⟩ : ∃ (l : Fin 13) (m : ℕ), 0 < m ∧
      ∀ y ∈ A.source, b6a_map b P.f y = b6a_value y.1.val l ((A y).2 ^ m) := by
    by_cases hmark : P.f q.2 ∈ Set.range (b6_branch b)
    · obtain ⟨l, hl⟩ := hmark
      exact ⟨l, P.n q.2, P.hn q.2, (P.hmark q l hl.symm).2⟩
    · refine ⟨10, 1, by decide, ?_⟩
      intro y hy
      simpa [b6a_value] using (P.hfree q hmark).2 y hy
  have ht : (A q).1 ∈ b6_chart := by
    rw [P.hparam q q hqA]
    exact (b6t_polydisc_neighbourhood b P.hb).2.2.2 q.1.property
  have hv : ∀ᶠ z in 𝓝 (A q), b6a_value z.1 l (z.2 ^ m) = b6a_value z.1 j (R z ^ e) := by
    filter_upwards [hΩ.mem_nhds hqΩ] with z hz
    have hy := A.map_target hz.1
    have hp := P.hparam q (A.symm z) hy
    rw [A.right_inv hz.1] at hp
    have h₁ := hmodel (A.symm z) hy
    have h₂ := hroot (A.symm z) hz.2
    rw [A.right_inv hz.1, ← hp] at h₁
    rw [← hp] at h₂
    exact h₁.symm.trans h₂
  have hR : ContDiffAt ℂ ω R (A q) :=
    b6a_contDiffAt_value_root R (A q) ht l j m e hm he hr hv
  have hAh := (contMDiffOn_of_mem_maximalAtlas hA).contMDiffAt (A.open_source.mem_nhds hqA)
  have hh := hR.contMDiffAt.comp q hAh
  apply ContMDiffAt.contMDiffWithinAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [A.open_source.mem_nhds hqA] with y hy
  exact congrArg w (A.left_inv hy).symm

end HodgeLean.Foundations.Program
