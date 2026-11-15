import HodgeLean.Foundations.Program.RelativeFrameFamilyMovingAnalytic

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- A continuous nonzero root of an analytic function is analytic in manifold coordinates.
Source: `b6a_contDiffAt_of_pow`. -/
theorem rf7_contMDiffOn_nonzero_root {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    (S : Set M) (hS : IsOpen S) (w : M → ℂ) (hw : ContinuousOn w S)
    (n : ℕ) (hn : 0 < n) (hne : ∀ q ∈ S, w q ≠ 0)
    (hh : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun q ↦ w q ^ n) S) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω w S := by
  intro q hq
  let A := extChartAt 𝓘(ℂ, E) q
  have hqA : q ∈ A.source := mem_extChartAt_source q
  have hAt : A q ∈ A.target := A.map_source hqA
  have hinv : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω A.symm (A q) := (contMDiffOn_extChartAt_symm q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hAt)
  have he : A.symm (A q) = q := A.left_inv hqA
  have hr : ContinuousAt (fun z ↦ w (A.symm z)) (A q) := by
    have hc : ContinuousAt w (A.symm (A q)) := by
      rw [he]
      exact hw.continuousAt (hS.mem_nhds hq)
    exact hc.comp hinv.continuousAt
  have hp : ContDiffAt ℂ ω (fun z ↦ w (A.symm z) ^ n) (A q) := by
    have hc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun y ↦ w y ^ n) (A.symm (A q)) := by
      rw [he]
      exact hh.contMDiffAt (hS.mem_nhds hq)
    exact (hc.comp (A q) hinv).contDiffAt
  have hne' : w (A.symm (A q)) ≠ 0 := by rw [he]; exact hne q hq
  have hR := b6a_contDiffAt_of_pow (fun z ↦ w (A.symm z)) (A q) n hn hr hne' hp
  have hchart : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω A q := contMDiffAt_extChartAt
  apply ContMDiffAt.contMDiffWithinAt
  apply (hR.contMDiffAt.comp q hchart).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source q).mem_nhds hqA] with y hy
  exact congrArg w (A.left_inv hy).symm

/-- A nonzero power coordinate outside the tent supports is analytic on the total space.
Source: `rf7_total_root_analytic`, `rf7_contMDiffOn_nonzero_root`, `b6t_fixed`. -/
theorem rf7_stationary_power_analytic {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (S : Set C) (hS : IsOpen S) (w : C → ℂ)
    (hw : ContinuousOn w S) (n : ℕ) (hn : 0 < n) (c : ℂ)
    (hne : ∀ y ∈ S, w y ≠ 0)
    (hstat : S ⊆ P.f ⁻¹' b6a_stationaryOpen b)
    (hpow : ∀ y ∈ S, P.f y = ((c + w y ^ n : ℂ) : OnePoint ℂ)) :
    ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
      (fun q : b6t_polydisc b × C ↦ w q.2) (univ ×ˢ S) := by
  letI := P.total_isManifold
  have hcont : ContinuousOn (fun q : b6t_polydisc b × C ↦ w q.2) (univ ×ˢ S) :=
    hw.comp continuous_snd.continuousOn (fun _ h ↦ h.2)
  have hW := rf7_total_root_analytic P S hS
    (fun q ↦ c + w q.2 ^ n) (continuousOn_const.add (hcont.pow n)) 10 1 (by decide)
    (fun q hq ↦ by
      change b6t_sphere b q.1.val (P.f q.2) = _
      rw [(b6t_fixed b P.hb q.1.val q.1.property).2.2.2 _ (hstat hq.2), hpow q.2 hq.2]
      simp [b6a_value])
  have hWpow : ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
      (fun q : b6t_polydisc b × C ↦ w q.2 ^ n) (univ ×ˢ S) := by
    simpa using hW.sub (contMDiffOn_const (c := c))
  exact rf7_contMDiffOn_nonzero_root _ (isOpen_univ.prod hS) _ hcont n hn
    (fun q hq ↦ hne q.2 hq.2) hWpow

end HodgeLean.Foundations.Program
