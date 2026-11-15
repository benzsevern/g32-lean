import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bAtlasFormulas
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bTransitions

noncomputable section

open Filter
open scoped Topology ContDiff Manifold
open Manifold

namespace HodgeLean.Foundations.Program

variable (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] [MulAction G C] [ChartedSpace ℂ C]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (n : C → ℕ)
    (hn : ∀ x, 0 < n x)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)

local notation "B" => b6a_isolatedFamilyChart b hb G U C π hπ f ι hι hrange n hn hlocal

theorem b6a_isolatedFamilyChart_transition_eq (hf : Continuous f)
    (q q' : b6t_polydisc b × C) (hqq' : q.2 = q'.2)
    (z : (Fin 10 → ℂ) × ℂ) (hz : z ∈ ((B hf q).symm.trans (B hf q')).source) :
    ((B hf q).symm.trans (B hf q')) z = z := by
  let y := (B hf q).symm z
  have hy : y ∈ (B hf q).source := (B hf q).map_target hz.1
  have hy' : y ∈ (B hf q').source := hz.2
  have h := b6a_familyChart_eq_of_snd_eq b hb G U C π hπ f ι hι hrange n hn hlocal q q' y hqq'
    (b6a_isolatedFamilyChart_source_subset b hb G U C π hπ f ι hι hrange n hn hlocal hf q hy)
    (b6a_isolatedFamilyChart_source_subset b hb G U C π hπ f ι hι hrange n hn hlocal hf q' hy')
  have heq : B hf q y = B hf q' y := by
    simpa only [b6a_isolatedFamilyChart_apply] using h
  exact heq.symm.trans ((B hf q).right_inv hz.1)

theorem b6a_isolatedFamilyChart_transition (hf : Continuous f) (hproj : ∀ u, f (ι u) = π u)
    (q q' : b6t_polydisc b × C) :
    ContDiffOn ℂ ω ((B hf q).symm.trans (B hf q')) ((B hf q).symm.trans (B hf q')).source := by
  obtain ⟨hp, hfree, hmark⟩ :=
    b6a_isolatedFamilyChart_formulas b hb G U C π hπ f ι hι hrange n hn hlocal hf hproj
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases hq' : b6a_IsMarked b f q'.2
  · by_cases hzero : (((B hf q).symm.trans (B hf q')) z).2 = 0
    · let y := (B hf q).symm z
      have hy' : y.2 = q'.2 :=
        b6a_isolatedFamilyChart_zero_fibre_eq b hb G U C π hπ f ι hι hrange n hn hlocal
          hf q' y hq' hz.2 hzero
      have hym : b6a_IsMarked b f y.2 := by simpa only [hy'] using hq'
      have hy : y.2 = q.2 := b6a_isolatedFamilyChart_marked_point b hb G U C π hπ f ι hι
        hrange n hn hlocal hf q y ((B hf q).map_target hz.1) hym
      have hqq' : q.2 = q'.2 := hy.symm.trans hy'
      apply contDiffAt_id.congr_of_eventuallyEq
      filter_upwards [((B hf q).symm.trans (B hf q')).open_source.mem_nhds hz] with w hw
      exact b6a_isolatedFamilyChart_transition_eq b hb G U C π hπ f ι hι hrange n hn hlocal
        hf q q' hqq' w hw
    · obtain ⟨j, hj⟩ := hq'
      exact b6a_transition_contDiffAt_of_mark_ne_zero b C f n hn (B hf) hp hfree
        (fun q j hj ↦ (hmark q j hj).2) q q' j hj z hz hzero
  · have hfree' : f q'.2 ∉ Set.range (b6_branch b) := by
      rintro ⟨j, hj⟩
      exact hq' ⟨j, hj.symm⟩
    exact b6a_transition_contDiffAt_of_free b C f n (B hf) hp hfree
      (fun q j hj ↦ (hmark q j hj).2) q q' hfree' z hz

theorem b6a_isolatedFamilyChart_isManifold (hf : Continuous f) (hproj : ∀ u, f (ι u) = π u) :
    letI : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C) :=
      b6a_familyChartedSpace b C (B hf)
        (b6a_mem_isolatedFamilyChart_source b hb G U C π hπ f ι hι hrange n hn hlocal hf)
    IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C) := by
  letI := b6a_familyChartedSpace b C (B hf)
    (b6a_mem_isolatedFamilyChart_source b hb G U C π hπ f ι hι hrange n hn hlocal hf)
  apply isManifold_of_contDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)
  rintro e e' ⟨q, rfl⟩ ⟨q', rfl⟩
  simpa using b6a_isolatedFamilyChart_transition b hb G U C π hπ f ι hι hrange n hn hlocal
    hf hproj q q'

end HodgeLean.Foundations.Program
